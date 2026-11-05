"""Durable local state and an at-most-once alert outbox."""
from __future__ import annotations
import fcntl
import hashlib
import json
import os
import tempfile
from contextlib import contextmanager
from datetime import datetime
from pathlib import Path
from typing import Any

class StateError(RuntimeError):
    pass

@contextmanager
def lock(path: Path):
    path.parent.mkdir(parents=True,exist_ok=True)
    with open(str(path)+".lock","a+") as f:
        try: fcntl.flock(f,fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError: raise StateError("Another local scan is running") from None
        try: yield
        finally: fcntl.flock(f,fcntl.LOCK_UN)

def save(path: Path, state: dict):
    path.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(prefix="."+path.name+".",dir=path.parent)
    try:
        with os.fdopen(fd,"w",encoding="utf-8") as f:
            json.dump(state,f,sort_keys=True,separators=(",",":"),allow_nan=False)
            f.flush(); os.fsync(f.fileno())
        os.replace(tmp,path)
        directory=os.open(path.parent,os.O_RDONLY)
        try: os.fsync(directory)
        finally: os.close(directory)
    finally:
        if os.path.exists(tmp): os.unlink(tmp)

def load(path: Path):
    if not path.exists(): raise StateError("STATE_NOT_INITIALIZED: reconcile prior scanner and initialize the new state")
    try:
        with path.open(encoding="utf-8") as f: s=json.load(f)
    except (OSError,json.JSONDecodeError) as e: raise StateError("State is unreadable; reconcile before continuing") from e
    if not isinstance(s,dict) or s.get("schema")!=1 or not isinstance(s.get("outbox"),list) or "position" not in s or not isinstance(s.get("history"),list):
        raise StateError("Unsupported or invalid state; reconcile before continuing")
    return s

def initialize(path: Path, now: datetime):
    if path.exists(): raise StateError("State already exists; refusing to overwrite")
    save(path,{"schema":1,"initialized_at":now.isoformat(),"initialized_flat":True,"session_date":None,"thesis":None,"position":None,"history":[],"outbox":[],"last_exit":None,"oi_snapshot":None})

def queue(state: dict, kind: str, details: dict, when: datetime):
    raw=json.dumps([kind,details],sort_keys=True,separators=(",",":"),allow_nan=False)
    event_id=hashlib.sha256(raw.encode()).hexdigest()[:24]
    if not any(x["id"]==event_id for x in state["outbox"]):
        state["outbox"].append({"id":event_id,"kind":kind,"created_at":when.isoformat(),"details":details,"status":"PENDING","claim":None})
    return event_id

def claim(state: dict, token: str):
    if not token or len(token)>160: raise StateError("Notification claim token required")
    for event in state["outbox"]:
        if event["status"]=="PENDING": event.update(status="CLAIMED",claim=token)

def append_audit(path: Path, event: dict):
    path.parent.mkdir(parents=True,exist_ok=True)
    line=json.dumps(event,sort_keys=True,separators=(",",":"),allow_nan=False)+"\n"
    with path.open("a",encoding="utf-8") as f:
        f.write(line); f.flush(); os.fsync(f.fileno())
