#!/usr/bin/env python3
"""NIFTY signal scanner CLI. Generates alerts; does not submit broker orders."""
from __future__ import annotations
import argparse
import json
import os
import smtplib
import ssl
import sys
from datetime import datetime
from email.message import EmailMessage
from pathlib import Path
from scanner import __version__
from scanner.core import Config,IST
from scanner.provider import Upstox,ProviderError
from scanner.runner import scan
from scanner.state import StateError,lock,load,save,initialize,claim,queue,append_audit


def paths():
    return Path(os.environ.get("STATE_FILE","state/market_state_v113.json")),Path(os.environ.get("AUDIT_DIR","audit"))


def deliver(s: dict, path: Path, token: str):
    sender=os.environ.get("EMAIL_SENDER",""); receiver=os.environ.get("EMAIL_RECEIVER","")
    username=os.environ.get("EMAIL_USERNAME") or sender; password=os.environ.get("EMAIL_PASSWORD","")
    host=os.environ.get("SMTP_HOST","smtp.gmail.com"); port=int(os.environ.get("SMTP_PORT","465"))
    if not all((sender,receiver,username,password,token)): raise StateError("Email credentials or claim token missing")
    uncertain=False
    for event in s["outbox"]:
        if event.get("status")!="CLAIMED" or event.get("claim")!=token: continue
        msg=EmailMessage(); msg["Subject"]="NIFTY scanner: "+("RETRIED " if event.get("manually_requeued_at") else "")+event["kind"]
        msg["From"]=sender; msg["To"]=receiver
        msg["Message-ID"]="<"+event["id"]+"@nifty-scanner.local>"
        msg.set_content("Signal/monitoring alert; this is not a broker order or a confirmed fill.\nOriginal alert created: "+event["created_at"]+"\nA retried alert is historical, not a fresh entry.\n\n"+json.dumps(event["details"],indent=2,sort_keys=True,allow_nan=False))
        try:
            with smtplib.SMTP_SSL(host,port,timeout=20,context=ssl.create_default_context()) as smtp:
                smtp.login(username,password); smtp.send_message(msg)
            event["status"]="SENT"; event["sent_at"]=datetime.now(IST).isoformat()
        except (OSError,smtplib.SMTPException):
            # Once a delivery attempt begins its outcome may be ambiguous; do not resend automatically.
            event["status"]="DELIVERY_UNCERTAIN"; event["attempted_at"]=datetime.now(IST).isoformat(); uncertain=True
        save(path,s)
    return 1 if uncertain else 0


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--version",action="store_true")
    mode.add_argument("--initialize-flat",action="store_true",help="Initialize only after manually reconciling prior scanner and broker positions")
    mode.add_argument("--scan-and-claim",action="store_true")
    mode.add_argument("--deliver-claimed",action="store_true")
    mode.add_argument("--reconcile-flat",metavar="POSITION_ID",help="After manual verification, close the matching alert lock without inventing a fill")
    mode.add_argument("--requeue-alert",metavar="ALERT_ID",help="After verifying non-delivery, explicitly requeue an uncertain alert")
    args=parser.parse_args()
    if args.version:
        print(__version__);return 0
    state_path,audit_dir=paths()
    try:
        with lock(state_path):
            if args.initialize_flat:
                initialize(state_path,datetime.now(IST));print("Initialized flat state after operator reconciliation.");return 0
            state=load(state_path)
            if args.reconcile_flat:
                position=state.get("position")
                if not isinstance(position,dict) or position.get("id")!=args.reconcile_flat:
                    raise StateError("Position ID does not match the current open lock")
                now=datetime.now(IST).isoformat()
                closed=dict(position,status="CLOSED",closed_at=now,exit_reason="MANUAL_RECONCILIATION_NO_FILL")
                state["history"].append(closed);state["position"]=None
                state["last_exit"]={"at":now,"direction":closed.get("direction"),"three":(state.get("thesis") or {}).get("last_3m")}
                save(state_path,state)
                append_audit(audit_dir/("market_scan_v113_"+datetime.now(IST).date().isoformat()+".jsonl"),{"operation":"MANUAL_RECONCILIATION","position_id":args.reconcile_flat,"at":now,"fill":"UNKNOWN"})
                print(json.dumps({"status":"RECONCILED_FLAT","position_id":args.reconcile_flat,"at":now}));return 0
            if args.requeue_alert:
                event=next((x for x in state["outbox"] if x.get("id")==args.requeue_alert),None)
                if not event or event.get("status") not in {"CLAIMED","DELIVERY_UNCERTAIN"}:
                    raise StateError("Alert ID is not an uncertain or previously claimed alert")
                event.update(status="PENDING",claim=None,manually_requeued_at=datetime.now(IST).isoformat())
                save(state_path,state)
                append_audit(audit_dir/("market_scan_v113_"+datetime.now(IST).date().isoformat()+".jsonl"),{"operation":"MANUAL_ALERT_REQUEUE","alert_id":args.requeue_alert,"at":datetime.now(IST).isoformat()})
                print(json.dumps({"status":"REQUEUED","alert_id":args.requeue_alert}));return 0
            token=os.environ.get("NOTIFICATION_CLAIM_TOKEN","")
            if args.deliver_claimed: return deliver(state,state_path,token)
            if not token: raise StateError("NOTIFICATION_CLAIM_TOKEN is required")
            try:
                api=Upstox(os.environ.get("UPSTOX_ANALYTICS_TOKEN",""))
            except ProviderError as exc:
                if state.get("position"):
                    now=datetime.now(IST)
                    queue(state,"MONITORING_UNAVAILABLE",{"position_id":state["position"].get("id"),"session_date":now.date().isoformat(),"cause":"TOKEN_UNAVAILABLE"},now)
                    claim(state,token); save(state_path,state)
                print(json.dumps({"decision":"ERROR","message":str(exc)}),file=sys.stderr);return 1
            result=scan(state,api,Config(),audit_dir)
            claim(state,token);save(state_path,state)
            print(json.dumps(result,sort_keys=True,allow_nan=False))
            return 1 if result["decision"]=="POSITION_MONITORING_UNAVAILABLE" or result["reason"] in {"DATA_OR_INTEGRATION_ERROR","PRIOR_SESSION_POSITION_REQUIRES_RECONCILIATION"} else 0
    except (StateError,OSError,ValueError) as exc:
        print(json.dumps({"decision":"ERROR","message":str(exc)},allow_nan=False),file=sys.stderr);return 1

if __name__=="__main__": sys.exit(main())
