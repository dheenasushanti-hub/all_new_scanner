#!/usr/bin/env python3
"""NIFTY 50 intraday options scanner — V91 persistent structure/OI confluence.

V91 calculates price structure and option-flow independently, persists developing directional
setups across scans, authorizes entries only after strict same-session paired OI confirmation,
selects a liquid ATM/ITM option, and derives index targets from opposing OI/price barriers. It is
signal-only and never places orders. Historical replay is required before performance claims.

Required environment: UPSTOX_ANALYTICS_TOKEN. Configure NIFTY_FUTURES_INSTRUMENT_KEY with the
current NIFTY futures contract to enable futures-volume VWAP.
Optional: NIFTY_INSTRUMENT_KEY, NIFTY_FUTURES_INSTRUMENT_KEY, STATE_FILE, AUDIT_DIR,
SCAN_INTERVAL_SECONDS, REQUEST_TIMEOUT, API_RETRIES, MAX_QUOTE_AGE_SECONDS, MAX_CANDLE_AGE_SECONDS,
MIN_SIGNAL_SCORE, MIN_T1_REWARD_RISK_RATIO, REENTRY_COOLDOWN_MINUTES, MAX_SPREAD_RATIO,
MIN_LOCAL_OI_CHANGE_PCT (minimum enforced at 2.5%), DIVERGENCE_RSI_DELTA, EMAIL_SENDER,
EMAIL_PASSWORD, EMAIL_RECEIVER, SMTP_HOST, SMTP_PORT, LOG_LEVEL.

Dependencies: requests, pandas, numpy.
"""
from __future__ import annotations

import argparse
import json
import logging
import math
import os
import smtplib
import ssl
import sys
import tempfile
import time as time_module
import urllib.parse
from dataclasses import asdict, dataclass, field, replace
from datetime import date, datetime, time, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests

VERSION = "V91-ADAPTIVE-PAIRED-FLOW-EARLY-TRIGGER"
BASE_URL = "https://api.upstox.com"
IST = ZoneInfo("Asia/Kolkata")
NIFTY_KEY_DEFAULT = "NSE_INDEX|Nifty 50"
MARKET_OPEN = time(9, 15)
ENTRY_OPEN = time(9, 16)
ENTRY_CUTOFF = time(15, 15)
MARKET_CLOSE = time(15, 30)
LOG = logging.getLogger("market_scanner_v91")
logging.basicConfig(
    level=os.getenv("LOG_LEVEL", "INFO").upper(),
    format="%(asctime)s | %(levelname)s | %(message)s",
    stream=sys.stderr,
)


class ScannerError(RuntimeError):
    """Expected configuration, API, or market-data failure."""


def env_float(name: str, default: float) -> float:
    try:
        value = float(os.getenv(name, str(default)))
        return value if math.isfinite(value) else default
    except (TypeError, ValueError):
        return default


def env_int(name: str, default: int) -> int:
    try:
        return int(os.getenv(name, str(default)))
    except (TypeError, ValueError):
        return default


def number(value: Any, default: float = float("nan")) -> float:
    try:
        out = float(value)
        return out if math.isfinite(out) else default
    except (TypeError, ValueError, OverflowError):
        return default


def finite(value: Any) -> bool:
    try:
        return math.isfinite(float(value))
    except (TypeError, ValueError, OverflowError):
        return False


def clamp(value: float, low: float, high: float) -> float:
    return max(low, min(high, value)) if finite(value) else low


DIVERGENCE_RSI_DELTA = clamp(env_float("DIVERGENCE_RSI_DELTA", 2.0), 1.0, 10.0)
STRUCTURE_WATCH_TTL_MINUTES = int(clamp(env_int("STRUCTURE_WATCH_TTL_MINUTES", 9), 3, 15))
STRUCTURE_WATCH_MAX_EXTENSION_ATR = clamp(env_float("STRUCTURE_WATCH_MAX_EXTENSION_ATR", 1.25), 0.75, 2.0)


def round_to_grid(value: float, step: float = 50.0) -> float:
    """Round a finite NIFTY level to the observed option strike grid."""
    if not finite(value) or not finite(step) or step <= 0:
        return float("nan")
    return float(math.floor(float(value) / float(step) + 0.5) * float(step))


def parse_date(value: Any) -> Optional[date]:
    if isinstance(value, date) and not isinstance(value, datetime):
        return value
    if not value:
        return None
    try:
        return date.fromisoformat(str(value)[:10])
    except (ValueError, TypeError):
        return None


def parse_dt(value: Any) -> Optional[datetime]:
    if isinstance(value, datetime):
        dt = value
    elif value:
        text = str(value).strip()
        try:
            dt = datetime.fromisoformat(text.replace("Z", "+00:00"))
        except (TypeError, ValueError):
            # Upstox sometimes represents last_trade_time as a Unix timestamp in milliseconds.
            try:
                epoch = float(text)
                if abs(epoch) >= 1_000_000_000_000:
                    dt = datetime.fromtimestamp(epoch / 1000.0, tz=IST)
                elif abs(epoch) >= 1_000_000_000:
                    dt = datetime.fromtimestamp(epoch, tz=IST)
                else:
                    return None
            except (ValueError, OverflowError, OSError):
                return None
    else:
        return None
    if dt.tzinfo is None:
        return dt.replace(tzinfo=IST)
    return dt.astimezone(IST)


def now_ist() -> datetime:
    return datetime.now(IST)


def safe_json(value: Any) -> Any:
    if value is None or isinstance(value, (str, bool, int)):
        return value
    if isinstance(value, float):
        return value if math.isfinite(value) else None
    if isinstance(value, datetime):
        return value.astimezone(IST).isoformat() if value.tzinfo else value.replace(tzinfo=IST).isoformat()
    if isinstance(value, date):
        return value.isoformat()
    if isinstance(value, Mapping):
        return {str(k): safe_json(v) for k, v in value.items()}
    if isinstance(value, (tuple, list, set)):
        return [safe_json(v) for v in value]
    if isinstance(value, np.generic):
        return safe_json(value.item())
    if pd.isna(value) if not isinstance(value, (dict, list, tuple, set)) else False:
        return None
    return str(value)


def _resolve_state_path(raw: str = "") -> Path:
    """Resolve the single canonical state file named ``market_state``.

    This repository's established contract is one unversioned ``market_state`` file beside
    the scanner. Do not probe versioned filenames or silently move state into another path.
    STATE_FILE is the only explicit override; a relative override is resolved from the
    workflow's working directory.
    """
    value = str(raw or "").strip()
    if value:
        path = Path(value).expanduser()
        return path if path.is_absolute() else (Path.cwd() / path).resolve()
    return Path(__file__).resolve().parent / "market_state"


@dataclass(frozen=True)
class Config:
    token: str = field(default_factory=lambda: os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip())
    nifty_key: str = field(default_factory=lambda: os.getenv("NIFTY_INSTRUMENT_KEY", NIFTY_KEY_DEFAULT).strip())
    futures_key: str = field(default_factory=lambda: os.getenv("NIFTY_FUTURES_INSTRUMENT_KEY", "").strip())
    timeout: float = field(default_factory=lambda: clamp(env_float("REQUEST_TIMEOUT", 12.0), 2.0, 30.0))
    retries: int = field(default_factory=lambda: int(clamp(env_int("API_RETRIES", 3), 1, 5)))
    max_quote_age: float = field(default_factory=lambda: clamp(env_float("MAX_QUOTE_AGE_SECONDS", 30.0), 5.0, 90.0))
    max_candle_age: float = field(default_factory=lambda: clamp(env_float("MAX_CANDLE_AGE_SECONDS", 180.0), 60.0, 300.0))
    min_signal_score: float = field(default_factory=lambda: clamp(env_float("MIN_SIGNAL_SCORE", 74.0), 70.0, 88.0))
    min_local_oi_change_pct: float = field(default_factory=lambda: max(2.5, clamp(env_float("MIN_LOCAL_OI_CHANGE_PCT", 2.5), 2.5, 10.0)))
    min_t1_rr: float = field(default_factory=lambda: clamp(env_float("MIN_T1_REWARD_RISK_RATIO", 1.25), 1.15, 3.0))
    reentry_cooldown_minutes: int = field(default_factory=lambda: int(clamp(env_int("REENTRY_COOLDOWN_MINUTES", 12), 8, 30)))
    max_spread: float = field(default_factory=lambda: clamp(env_float("MAX_SPREAD_RATIO", 0.0025), 0.0005, 0.01))
    strike_step: float = 50.0
    state_file: Path = field(default_factory=lambda: _resolve_state_path(os.getenv("STATE_FILE", "")))
    audit_dir: Path = field(default_factory=lambda: Path(os.getenv("AUDIT_DIR", "audit")))
    email_sender: str = field(default_factory=lambda: os.getenv("EMAIL_SENDER", "").strip())
    email_password: str = field(default_factory=lambda: os.getenv("EMAIL_PASSWORD", "").strip())
    email_receiver: str = field(default_factory=lambda: os.getenv("EMAIL_RECEIVER", "").strip())
    smtp_host: str = field(default_factory=lambda: os.getenv("SMTP_HOST", "smtp.gmail.com").strip())
    smtp_port: int = field(default_factory=lambda: int(clamp(env_int("SMTP_PORT", 465), 1, 65535)))
    scan_interval: int = field(default_factory=lambda: int(clamp(env_int("SCAN_INTERVAL_SECONDS", 180), 60, 900)))

    def validate(self, require_token: bool = True) -> None:
        if require_token and not self.token:
            raise ScannerError("UPSTOX_ANALYTICS_TOKEN is missing.")
        if not self.nifty_key:
            raise ScannerError("NIFTY_INSTRUMENT_KEY cannot be empty.")
        if not 70.0 <= self.min_signal_score <= 88.0:
            raise ScannerError("MIN_SIGNAL_SCORE must be between 70 and 88.")
        if not 1.15 <= self.min_t1_rr <= 3.0:
            raise ScannerError("MIN_T1_REWARD_RISK_RATIO must be between 1.15 and 3.")


@dataclass(frozen=True)
class Quote:
    instrument_key: str
    symbol: str
    ltp: float
    bid: float
    ask: float
    volume: float
    oi: float
    prev_oi: float
    timestamp: Optional[str]
    age_seconds: Optional[float]
    freshness: str
    bid_qty: float = 0.0
    ask_qty: float = 0.0

    @property
    def mid(self) -> float:
        return (self.bid + self.ask) / 2.0 if finite(self.bid) and finite(self.ask) and 0 < self.bid <= self.ask else float("nan")

    @property
    def spread_ratio(self) -> float:
        mid = self.mid
        return (self.ask - self.bid) / mid if finite(mid) and mid > 0 else float("inf")

    @property
    def depth_imbalance(self) -> float:
        total = max(0.0, self.bid_qty) + max(0.0, self.ask_qty)
        return (self.bid_qty - self.ask_qty) / total if total > 0 else 0.0


@dataclass(frozen=True)
class Contract:
    instrument_key: str
    symbol: str
    strike: float
    side: str
    expiry: str
    ltp: float
    oi: float
    prev_oi: float
    volume: float
    bid: float
    ask: float
    bid_qty: float
    ask_qty: float
    delta: float
    iv: float
    theta: float
    gamma: float
    vega: float


@dataclass(frozen=True)
class Level:
    price: float
    kind: str                 # SUPPORT or RESISTANCE
    source: str               # PRICE_PIVOT, SESSION_EXTREME, OI_WALL, or composite
    strength: float           # 0..1 structure/OI importance score
    touches: int = 1
    oi_change_pct: Optional[float] = None
    oi_state: str = "UNKNOWN"
    flow_state: str = "UNKNOWN"
    notes: str = ""


@dataclass(frozen=True)
class Signal:
    direction: str
    setup: str
    score: float
    confidence_pct: float
    trigger: str
    level: Optional[float]
    evidence: tuple[str, ...]
    blockers: tuple[str, ...] = ()


@dataclass(frozen=True)
class RiskPlan:
    valid: bool
    t1: Optional[float]
    t2: Optional[float]
    sl: Optional[float]
    stop_source: str
    target_source: str
    reward_points: Optional[float]
    risk_points: Optional[float]
    reward_risk: Optional[float]
    reason: str


@dataclass(frozen=True)
class Indicators:
    spot: float
    vwap: float
    vwap_slope: float
    atr: float
    rsi: float
    adx: float
    plus_di: float
    minus_di: float
    momentum_1m: float
    momentum_3m: float
    last_close: float
    prev_close: float
    session_high: float
    session_low: float
    swing_high: float
    swing_low: float
    candles: int
    volume_source: str


class AtomicState:
    """Atomic state store backed by one canonical, unversioned market_state file."""
    SNAPSHOT_SCHEMAS = {80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91}

    def __init__(self, path: Path):
        self.path = path
        self.data: dict[str, Any] = {}

    @staticmethod
    def _valid_snapshot(snap: Any, today: date, expected_expiry: str = "") -> bool:
        if not isinstance(snap, dict):
            return False
        stamp = parse_dt(snap.get("timestamp"))
        expiry = str(snap.get("expiry", ""))
        rows = snap.get("rows")
        if not stamp or stamp.date() != today or not expiry or (expected_expiry and expiry != expected_expiry):
            return False
        if not isinstance(rows, list) or len(rows) < 20:
            return False
        valid_rows = 0
        seen: set[float] = set()
        for row in rows:
            if not isinstance(row, dict):
                continue
            keys = ("strike", "call_oi", "put_oi", "call_ltp", "put_ltp")
            if not all(key in row and finite(row.get(key)) for key in keys):
                continue
            strike = number(row.get("strike"))
            if strike <= 0 or strike in seen or number(row.get("call_oi")) < 0 or number(row.get("put_oi")) < 0:
                continue
            seen.add(strike)
            valid_rows += 1
        return valid_rows >= 20

    @staticmethod
    def _valid_tracker(value: Any, today: date) -> bool:
        if not isinstance(value, dict):
            return False
        stamp = parse_dt(value.get("signal_timestamp"))
        status = str(value.get("status", "")).upper()
        required = ("direction", "symbol", "strike", "side", "T1", "SL", "event_key")
        return bool(stamp and stamp.date() == today and status in {
            "TRACKING", "T1_REACHED", "T2_REACHED", "STOPPED", "TERMINAL"
        } and all(k in value for k in required) and finite(value.get("strike"))
            and finite(value.get("T1")) and finite(value.get("SL")))

    def load(self, today: date) -> dict[str, Any]:
        loaded: dict[str, Any] = {}
        corrupt = False
        existed = self.path.exists()
        if existed:
            try:
                candidate = json.loads(self.path.read_text(encoding="utf-8"))
                if isinstance(candidate, dict):
                    loaded = candidate
                else:
                    corrupt = True
            except (OSError, json.JSONDecodeError) as exc:
                LOG.error("Canonical state file is unreadable; entries are suppressed for this scan: %s", exc)
                corrupt = True
                # Preserve the damaged file before the first valid atomic rewrite. No other
                # state filename is searched or imported.
                try:
                    backup = self.path.with_name(f"{self.path.name}.corrupt-{datetime.now(IST).strftime('%Y%m%d-%H%M%S')}")
                    if self.path.is_file() and not backup.exists():
                        import shutil
                        shutil.copy2(self.path, backup)
                except OSError as backup_exc:
                    LOG.error("Could not preserve corrupt state file: %s", backup_exc)

        schema = int(number(loaded.get("schema_version"), 0))
        prior_date = parse_date(loaded.get("session_date"))
        same_session = prior_date == today
        current_schema = same_session and schema == 91 and loaded.get("scanner_version") == VERSION
        known_migration = same_session and schema in self.SNAPSHOT_SCHEMAS
        expected_expiry = str(loaded.get("option_expiry", "")) if same_session else ""
        old_snaps = loaded.get("chain_snapshots", []) if isinstance(loaded.get("chain_snapshots"), list) else []
        snapshots: list[dict[str, Any]] = []
        if same_session and (current_schema or known_migration) and not corrupt:
            seen_snapshots: set[tuple[str, str]] = set()
            for snap in old_snaps:
                if not self._valid_snapshot(snap, today, expected_expiry):
                    continue
                stamp = parse_dt(snap.get("timestamp"))
                key = (stamp.isoformat() if stamp else "", str(snap.get("expiry", "")))
                if key not in seen_snapshots:
                    snapshots.append(snap)
                    seen_snapshots.add(key)
            snapshots.sort(key=lambda v: parse_dt(v.get("timestamp")) or datetime.min.replace(tzinfo=IST))

        if not expected_expiry and snapshots:
            expected_expiry = str(snapshots[-1].get("expiry", ""))
        active = loaded.get("active_signal") if same_session and not corrupt else None
        if not self._valid_tracker(active, today):
            active = None
        elif not current_schema:
            active = dict(active)
            active["legacy_tracker"] = True
            active["source_scanner_version"] = str(loaded.get("scanner_version", f"SCHEMA_{schema}"))

        history = loaded.get("signal_history", []) if same_session and isinstance(loaded.get("signal_history", []), list) else []
        sent_keys = loaded.get("emailed_notification_keys", []) if same_session and isinstance(loaded.get("emailed_notification_keys", []), list) else []
        sent_events = loaded.get("emailed_event_keys", []) if same_session and isinstance(loaded.get("emailed_event_keys", []), list) else []
        self.data = {
            "schema_version": 91,
            "scanner_version": VERSION,
            "session_date": today.isoformat(),
            "option_expiry": expected_expiry,
            "chain_snapshots": snapshots[-60:],
            "active_signal": active,
            "signal_history": history[-100:],
            "last_email_key": str(loaded.get("last_email_key", "")) if same_session else "",
            "emailed_event_keys": [str(x) for x in sent_events if isinstance(x, str)][-200:],
            "emailed_notification_keys": [str(x) for x in sent_keys if isinstance(x, str)][-300:],
            # Do not import queued messages from a prior scanner generation: their stale
            # bodies/selection assumptions must not be sent by V91.
            "pending_email_notifications": loaded.get("pending_email_notifications", [])[-50:]
                if current_schema and isinstance(loaded.get("pending_email_notifications", []), list) else [],
            "last_scan_timestamp": loaded.get("last_scan_timestamp") if same_session else None,
            "state_file_path": str(self.path.resolve()),
            "state_load_status": ("CORRUPT_RESET_ENTRIES_SUPPRESSED" if corrupt else
                                  "CURRENT_SCHEMA" if current_schema else
                                  f"SAME_FILE_SNAPSHOT_MIGRATION_SCHEMA_{schema}" if snapshots and known_migration else
                                  "NEW_SESSION_RESET" if prior_date and prior_date != today else
                                  "NEW_EMPTY_STATE" if not existed else "SAME_SESSION_STATE_NO_COMPATIBLE_SNAPSHOTS"),
            "state_integrity_ok": not corrupt,
            "snapshot_migrated_from_schema": schema if snapshots and known_migration and not current_schema else None,
            "pending_structure_setup": (loaded.get("pending_structure_setup")
                                        if same_session and not corrupt and isinstance(loaded.get("pending_structure_setup"), dict)
                                        else None),
            "directional_watch": (loaded.get("directional_watch")
                                  if same_session and not corrupt and isinstance(loaded.get("directional_watch"), dict)
                                  else None),
            "historical_context": (loaded.get("historical_context", [])
                                   if same_session and not corrupt and isinstance(loaded.get("historical_context", []), list)
                                   else []),
            "historical_context_date": (str(loaded.get("historical_context_date", "")) if same_session and not corrupt else ""),
            "historical_context_instrument_key": (str(loaded.get("historical_context_instrument_key", "")) if same_session and not corrupt else ""),
        }
        return self.data

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        fd, temp_path = tempfile.mkstemp(prefix=self.path.name + ".", suffix=".tmp", dir=str(self.path.parent))
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(safe_json(self.data), handle, separators=(",", ":"), ensure_ascii=False, allow_nan=False)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp_path, self.path)
            try:
                dir_fd = os.open(str(self.path.parent), os.O_RDONLY)
                try:
                    os.fsync(dir_fd)
                finally:
                    os.close(dir_fd)
            except OSError:
                # Directory fsync is unavailable on some runners; atomic replace still holds.
                pass
        except Exception:
            try:
                os.unlink(temp_path)
            except OSError:
                pass
            raise


class UpstoxClient:
    def __init__(self, config: Config, session: Optional[requests.Session] = None):
        self.config = config
        self.session = session or requests.Session()
        self.session.headers.update({"Accept": "application/json", "Content-Type": "application/json"})

    def get(self, path: str, params: Optional[dict[str, Any]] = None) -> dict[str, Any]:
        self.config.validate()
        url = path if path.startswith("http") else BASE_URL + path
        last_error = "unknown error"
        for attempt in range(self.config.retries):
            try:
                response = self.session.get(
                    url, params=params,
                    headers={"Authorization": f"Bearer {self.config.token}", "Accept": "application/json"},
                    timeout=(min(5.0, self.config.timeout), self.config.timeout),
                )
            except requests.RequestException as exc:
                last_error = f"network error: {exc}"
                if attempt + 1 < self.config.retries:
                    time_module.sleep(min(0.4 * (2 ** attempt), 2.5))
                    continue
                raise ScannerError(f"Upstox request failed for {url}: {last_error}") from exc
            if response.status_code == 200:
                try:
                    payload = response.json()
                except ValueError as exc:
                    raise ScannerError(f"Upstox returned invalid JSON for {url}") from exc
                if not isinstance(payload, dict) or str(payload.get("status", "success")).lower() == "error":
                    raise ScannerError(f"Unexpected Upstox response from {url}: {str(payload)[:500]}")
                return payload
            last_error = f"HTTP {response.status_code}: {response.text[:500]}"
            if response.status_code in {429, 500, 502, 503, 504} and attempt + 1 < self.config.retries:
                retry_after = number(response.headers.get("Retry-After"), min(0.5 * (2 ** attempt), 3.0))
                time_module.sleep(clamp(retry_after, 0.2, 5.0))
                continue
            raise ScannerError(f"Upstox request failed for {url}: {last_error}")
        raise ScannerError(f"Upstox request failed for {url}: {last_error}")

    def market_status(self) -> str:
        payload = self.get("/v2/market/status/NSE")
        data = payload.get("data") or {}
        status = str(data.get("status", "UNKNOWN")).upper() if isinstance(data, dict) else "UNKNOWN"
        return "OPEN" if status in {"OPEN", "NORMAL_OPEN"} else "CLOSED" if status in {"CLOSED", "NORMAL_CLOSE"} else status

    def expiry(self, state: dict[str, Any], today: date) -> str:
        cached = parse_date(state.get("option_expiry"))
        if cached and cached >= today:
            return cached.isoformat()
        payload = self.get("/v2/option/contract", {"instrument_key": self.config.nifty_key})
        rows = payload.get("data")
        if not isinstance(rows, list):
            raise ScannerError("Option contracts response has no data array.")
        expiries = sorted({d for r in rows if isinstance(r, dict) and (d := parse_date(r.get("expiry"))) and d >= today})
        if not expiries:
            raise ScannerError("No non-expired NIFTY option expiry was returned.")
        state["option_expiry"] = expiries[0].isoformat()
        return expiries[0].isoformat()

    def chain(self, expiry: str) -> list[dict[str, Any]]:
        exp = parse_date(expiry)
        if not exp:
            raise ScannerError(f"Invalid option expiry: {expiry!r}")
        payload = self.get("/v2/option/chain", {"instrument_key": self.config.nifty_key, "expiry_date": exp.isoformat()})
        rows = payload.get("data")
        if not isinstance(rows, list) or not rows:
            raise ScannerError(f"Option chain is empty for expiry {exp.isoformat()}.")
        with_expiry = [r for r in rows if isinstance(r, dict) and r.get("expiry")]
        if with_expiry:
            matched = [r for r in with_expiry if parse_date(r.get("expiry")) == exp]
            if not matched:
                raise ScannerError("Option-chain expiry does not match requested expiry; refusing mixed-expiry rows.")
            return matched
        return [r for r in rows if isinstance(r, dict)]

    def quotes(self, keys: Sequence[str]) -> dict[str, Quote]:
        unique = list(dict.fromkeys(str(k) for k in keys if str(k).strip()))
        result: dict[str, Quote] = {}
        for start in range(0, len(unique), 450):
            group = unique[start:start + 450]
            if not group:
                continue
            payload = self.get("/v3/market-quote/quotes", {"instrument_key": ",".join(group)})
            rows = payload.get("data")
            if not isinstance(rows, dict):
                raise ScannerError("V3 quotes response data is not an object.")
            for key in group:
                raw = rows.get(key) or rows.get(key.replace("|", ":", 1))
                if not isinstance(raw, dict):
                    # Some quote responses key rows by their exchange-formatted token.
                    raw = next((v for v in rows.values() if isinstance(v, dict) and str(v.get("instrument_token", "")).replace(":", "|") == key), None)
                if not isinstance(raw, dict):
                    continue
                result[key] = normalise_quote(key, raw, self.config.max_quote_age)
        return result

    def candles(self, key: str, interval: int = 1) -> pd.DataFrame:
        encoded = urllib.parse.quote(key, safe="")
        payload = self.get(f"/v3/historical-candle/intraday/{encoded}/minutes/{interval}")
        data = payload.get("data") or {}
        rows = data.get("candles", []) if isinstance(data, dict) else []
        frame = parse_candles(rows)
        if frame.empty:
            return frame
        today = now_ist().date()
        dates = frame["timestamp"].dt.tz_convert(IST).dt.date
        return frame.loc[dates == today].reset_index(drop=True)

    def historical_candles(self, key: str, interval: int, to_date: date, from_date: date) -> pd.DataFrame:
        """Fetch prior one-minute context; current-session entries still use current-session bars."""
        if from_date > to_date:
            return pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
        encoded = urllib.parse.quote(key, safe="")
        payload = self.get(f"/v3/historical-candle/{encoded}/minutes/{int(interval)}/{to_date.isoformat()}/{from_date.isoformat()}")
        data = payload.get("data") or {}
        rows = data.get("candles", []) if isinstance(data, dict) else []
        frame = parse_candles(rows)
        if frame.empty:
            return frame
        local_dates = frame["timestamp"].dt.tz_convert(IST).dt.date
        return frame.loc[(local_dates >= from_date) & (local_dates <= to_date)].reset_index(drop=True)


def normalise_quote(key: str, raw: Mapping[str, Any], max_age_seconds: float = 30.0) -> Quote:
    depth = raw.get("depth") if isinstance(raw.get("depth"), dict) else {}
    ohlc = raw.get("ohlc") if isinstance(raw.get("ohlc"), dict) else {}
    buys = depth.get("buy", []) if isinstance(depth.get("buy", []), list) else []
    sells = depth.get("sell", []) if isinstance(depth.get("sell", []), list) else []
    buy_rows = [x for x in buys if isinstance(x, dict)]
    sell_rows = [x for x in sells if isinstance(x, dict)]
    bid = number(buy_rows[0].get("price")) if buy_rows else float("nan")
    ask = number(sell_rows[0].get("price")) if sell_rows else float("nan")
    stamp = parse_dt(raw.get("timestamp")) or parse_dt(raw.get("last_trade_time"))
    age = (now_ist() - stamp).total_seconds() if stamp else None
    freshness = "UNVERIFIED" if age is None else "FRESH" if -5 <= age <= max_age_seconds else "STALE" if age > max_age_seconds else "FUTURE_TIMESTAMP"
    volume = number(raw.get("volume"), number(ohlc.get("volume"), 0.0))
    return Quote(
        instrument_key=key,
        symbol=str(raw.get("symbol", raw.get("trading_symbol", key))),
        ltp=number(raw.get("last_price", raw.get("ltp"))),
        bid=bid, ask=ask, volume=max(0.0, volume),
        oi=max(0.0, number(raw.get("oi"), 0.0)),
        prev_oi=number(raw.get("previous_oi", raw.get("prev_oi"))),
        timestamp=stamp.isoformat() if stamp else None,
        age_seconds=age, freshness=freshness,
        bid_qty=sum(max(0.0, number(x.get("quantity"), 0.0)) for x in buy_rows),
        ask_qty=sum(max(0.0, number(x.get("quantity"), 0.0)) for x in sell_rows),
    )


def parse_candles(rows: Any) -> pd.DataFrame:
    columns = ["timestamp", "open", "high", "low", "close", "volume", "oi"]
    parsed: list[dict[str, Any]] = []
    if not isinstance(rows, list):
        return pd.DataFrame(columns=columns)
    for row in rows:
        if not isinstance(row, (list, tuple)) or len(row) < 6:
            continue
        stamp = pd.to_datetime(row[0], utc=True, errors="coerce")
        values = [number(row[i]) for i in range(1, 6)]
        if pd.isna(stamp) or not all(finite(x) for x in values[:4]):
            continue
        if values[1] < values[2] or values[0] <= 0 or values[3] <= 0:
            continue
        parsed.append({"timestamp": stamp, "open": values[0], "high": values[1], "low": values[2], "close": values[3],
                       "volume": max(0.0, values[4]), "oi": number(row[6]) if len(row) > 6 else float("nan")})
    if not parsed:
        return pd.DataFrame(columns=columns)
    frame = pd.DataFrame(parsed).sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)
    return frame


def parse_contract_side(row: Mapping[str, Any], side: str, strike: float, expiry: str) -> Contract:
    key = "call_options" if side == "CE" else "put_options"
    block = row.get(key) if isinstance(row.get(key), dict) else {}
    market = block.get("market_data") if isinstance(block.get("market_data"), dict) else {}
    greeks = block.get("option_greeks") if isinstance(block.get("option_greeks"), dict) else {}
    return Contract(
        instrument_key=str(block.get("instrument_key", "")),
        symbol=str(block.get("trading_symbol", f"NIFTY {strike:g} {side}")),
        strike=float(strike), side=side, expiry=expiry,
        ltp=number(market.get("ltp")), oi=max(0.0, number(market.get("oi"), 0.0)),
        prev_oi=number(market.get("prev_oi")), volume=max(0.0, number(market.get("volume"), 0.0)),
        bid=number(market.get("bid_price")), ask=number(market.get("ask_price")),
        bid_qty=max(0.0, number(market.get("bid_qty"), 0.0)), ask_qty=max(0.0, number(market.get("ask_qty"), 0.0)),
        delta=number(greeks.get("delta")), iv=number(greeks.get("iv")), theta=number(greeks.get("theta")),
        gamma=number(greeks.get("gamma")), vega=number(greeks.get("vega")),
    )


def chain_to_contracts(chain: Sequence[dict[str, Any]], expiry: str) -> tuple[dict[float, dict[str, Any]], dict[tuple[float, str], Contract]]:
    rows_by_strike: dict[float, dict[str, Any]] = {}
    contracts: dict[tuple[float, str], Contract] = {}
    for row in chain:
        strike = number(row.get("strike_price"))
        if not finite(strike) or strike <= 0:
            continue
        strike = float(strike)
        rows_by_strike[strike] = row
        for side in ("CE", "PE"):
            contract = parse_contract_side(row, side, strike, expiry)
            if contract.instrument_key:
                contracts[(strike, side)] = contract
    if not rows_by_strike:
        raise ScannerError("Option chain contains no valid strike prices.")
    return rows_by_strike, contracts


def frame_to_records(frame: pd.DataFrame, limit: int = 4000) -> list[dict[str, Any]]:
    """Compact, JSON-safe OHLC context for persistent warm-up across workflow invocations."""
    if frame is None or frame.empty:
        return []
    records: list[dict[str, Any]] = []
    for _, row in frame.tail(limit).iterrows():
        ts = row.get("timestamp")
        stamp = ts.to_pydatetime().astimezone(IST).isoformat() if hasattr(ts, "to_pydatetime") else str(ts)
        records.append({"timestamp": stamp, "open": number(row.get("open")), "high": number(row.get("high")),
                        "low": number(row.get("low")), "close": number(row.get("close")),
                        "volume": number(row.get("volume"), 0.0), "oi": number(row.get("oi"))})
    return records


def records_to_frame(records: Any) -> pd.DataFrame:
    columns = ["timestamp", "open", "high", "low", "close", "volume", "oi"]
    if not isinstance(records, list) or not records:
        return pd.DataFrame(columns=columns)
    rows: list[dict[str, Any]] = []
    for row in records:
        if not isinstance(row, Mapping):
            continue
        stamp = parse_dt(row.get("timestamp"))
        values = [number(row.get(k)) for k in ("open", "high", "low", "close")]
        if not stamp or not all(finite(x) for x in values) or values[0] <= 0 or values[1] < values[2]:
            continue
        rows.append({"timestamp": pd.Timestamp(stamp).tz_convert("UTC"), "open": values[0], "high": values[1],
                     "low": values[2], "close": values[3], "volume": max(0.0, number(row.get("volume"), 0.0)),
                     "oi": number(row.get("oi"))})
    if not rows:
        return pd.DataFrame(columns=columns)
    return pd.DataFrame(rows, columns=columns).sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)


def completed_candles(frame: pd.DataFrame, now: datetime) -> pd.DataFrame:
    """Exclude the currently forming minute candle; decisions use closed candles only."""
    if frame is None or frame.empty:
        return pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
    stamps = frame["timestamp"].dt.tz_convert(IST)
    minute_start = now.astimezone(IST).replace(second=0, microsecond=0)
    return frame.loc[stamps < minute_start].copy().reset_index(drop=True)


def _rsi_series(close: pd.Series, period: int = 14, timestamps: Optional[pd.Series] = None) -> pd.Series:
    """Wilder-smoothed RSI; do not treat an overnight session gap as an intraday momentum bar."""
    values = close.astype(float)
    delta = values.diff()
    if timestamps is not None and len(timestamps) == len(values):
        stamp_series = pd.to_datetime(timestamps, utc=True, errors="coerce")
        local_dates = stamp_series.dt.tz_convert(IST).dt.date
        session_change = local_dates.ne(local_dates.shift(1))
        delta = delta.mask(session_change)
    gain = delta.clip(lower=0).ewm(alpha=1 / period, adjust=False, min_periods=period).mean()
    loss = (-delta.clip(upper=0)).ewm(alpha=1 / period, adjust=False, min_periods=period).mean()
    rs = gain / loss.replace(0, np.nan)
    result = 100 - (100 / (1 + rs))
    result = result.where(loss.ne(0), 100.0)
    result = result.where(~(gain.eq(0) & loss.eq(0)), 50.0)
    return result.clip(0, 100)


def _confirmed_pivots(frame: pd.DataFrame, window: int = 2) -> list[dict[str, Any]]:
    """Return closed-bar pivots only; each pivot has right-side confirmation bars."""
    if frame is None or frame.empty or len(frame) < window * 2 + 8:
        return []
    bars = frame.tail(180).reset_index(drop=True).copy()
    rsi = _rsi_series(bars["close"], timestamps=bars["timestamp"])
    high_values = bars["high"].to_numpy(dtype=float)
    low_values = bars["low"].to_numpy(dtype=float)
    raw: list[dict[str, Any]] = []
    for i in range(window, len(bars) - window):
        hi = high_values[i]
        lo = low_values[i]
        hw = high_values[i-window:i+window+1]
        lw = low_values[i-window:i+window+1]
        pivot_high = hi >= float(np.max(hw)) and int(np.sum(hw == hi)) == 1
        pivot_low = lo <= float(np.min(lw)) and int(np.sum(lw == lo)) == 1
        # Wide candles can appear as both high and low pivots. Skipping ambiguous bars
        # is safer than inventing an order for an intrabar swing.
        if pivot_high == pivot_low:
            continue
        ts = bars.loc[i, "timestamp"]
        raw.append({
            "index": int(i), "kind": "HIGH" if pivot_high else "LOW",
            "price": float(hi if pivot_high else lo),
            "rsi": number(rsi.iloc[i]),
            "timestamp": ts.to_pydatetime().astimezone(IST).isoformat() if hasattr(ts, "to_pydatetime") else str(ts),
        })
    # Enforce alternating pivots. If a second same-kind pivot appears before a valid
    # opposite pivot, keep only the more extreme one.
    pivots: list[dict[str, Any]] = []
    for point in raw:
        if not pivots:
            pivots.append(point)
            continue
        prior = pivots[-1]
        if point["kind"] == prior["kind"]:
            more_extreme = (point["price"] > prior["price"]) if point["kind"] == "HIGH" else (point["price"] < prior["price"])
            if more_extreme:
                pivots[-1] = point
        elif point["index"] - prior["index"] >= 3:
            pivots.append(point)
    return pivots


def _leg_payload(start: Mapping[str, Any], end: Mapping[str, Any], direction: str) -> Optional[dict[str, Any]]:
    """Build a swing-leg Fibonacci map from two confirmed opposite pivots."""
    high = number(start["price"] if start.get("kind") == "HIGH" else end["price"] if end.get("kind") == "HIGH" else float("nan"))
    low = number(start["price"] if start.get("kind") == "LOW" else end["price"] if end.get("kind") == "LOW" else float("nan"))
    if not finite(high) or not finite(low) or high <= low:
        return None
    span = high - low
    if direction == "UP":
        # Retracements descend from the completed swing high toward its swing low.
        retracements = {f"{pct:.1f}": round(high - span * pct / 100, 2) for pct in (38.2, 50.0, 61.8, 78.6)}
        extensions = {"127.2": round(low + span * 1.272, 2), "161.8": round(low + span * 1.618, 2)}
    else:
        # During a down leg, resistance retracements rise from swing low toward swing high.
        retracements = {f"{pct:.1f}": round(low + span * pct / 100, 2) for pct in (38.2, 50.0, 61.8, 78.6)}
        extensions = {"127.2": round(high - span * 1.272, 2), "161.8": round(high - span * 1.618, 2)}
    return {
        "direction": direction, "high": round(high, 2), "low": round(low, 2),
        "range_points": round(span, 2), "start_timestamp": start.get("timestamp"),
        "end_timestamp": end.get("timestamp"), "start_index": int(start["index"]),
        "end_index": int(end["index"]), "retracements": retracements,
        "extensions": extensions,
    }


def analyze_fibonacci(frame: pd.DataFrame, atr: float, now: Optional[datetime] = None) -> dict[str, Any]:
    """Derive the latest qualified upward and downward legs and associated Fib levels."""
    bars = completed_candles(frame, (now or now_ist()).astimezone(IST)).tail(180).reset_index(drop=True)
    if len(bars) < 20:
        return {"available": False, "reason": "INSUFFICIENT_CLOSED_BARS", "up_leg": None, "down_leg": None,
                "latest_swing_high": None, "latest_swing_low": None, "pivots": []}
    pivots = _confirmed_pivots(bars)
    min_range = max(0.70 * atr if finite(atr) else 20.0, 20.0)
    up_legs: list[dict[str, Any]] = []
    down_legs: list[dict[str, Any]] = []
    for a, b in zip(pivots, pivots[1:]):
        span = abs(number(b.get("price")) - number(a.get("price")))
        if span < min_range:
            continue
        if a["kind"] == "LOW" and b["kind"] == "HIGH":
            item = _leg_payload(a, b, "UP")
            if item: up_legs.append(item)
        elif a["kind"] == "HIGH" and b["kind"] == "LOW":
            item = _leg_payload(a, b, "DOWN")
            if item: down_legs.append(item)
    latest_high = next((p for p in reversed(pivots) if p["kind"] == "HIGH"), None)
    latest_low = next((p for p in reversed(pivots) if p["kind"] == "LOW"), None)
    result = {
        "available": bool(up_legs or down_legs),
        "reason": "CONFIRMED_SWING_LEGS" if up_legs or down_legs else "NO_QUALIFIED_SWING_LEG",
        "up_leg": up_legs[-1] if up_legs else None,
        "down_leg": down_legs[-1] if down_legs else None,
        "latest_swing_high": {k: latest_high[k] for k in ("price", "timestamp", "index", "rsi")} if latest_high else None,
        "latest_swing_low": {k: latest_low[k] for k in ("price", "timestamp", "index", "rsi")} if latest_low else None,
        "pivots": [{k: p[k] for k in ("kind", "price", "timestamp", "index", "rsi")} for p in pivots[-12:]],
    }
    if result["up_leg"]:
        leg = result["up_leg"]
        result["bullish_support_zone"] = {
            "fib_50": leg["retracements"]["50.0"], "fib_61_8": leg["retracements"]["61.8"],
            "fib_78_6_invalidation_reference": leg["retracements"]["78.6"],
            "zone_low": leg["retracements"]["61.8"], "zone_high": leg["retracements"]["50.0"],
        }
    else:
        result["bullish_support_zone"] = None
    if result["down_leg"]:
        leg = result["down_leg"]
        result["bearish_resistance_levels"] = {
            "fib_61_8": leg["retracements"]["61.8"], "fib_100": leg["high"],
            "fib_50": leg["retracements"]["50.0"],
        }
    else:
        result["bearish_resistance_levels"] = None
    return result


def detect_rsi_divergence(frame: pd.DataFrame, atr: float, now: Optional[datetime] = None) -> dict[str, Any]:
    """Detect fresh regular RSI divergence at confirmed swing pivots, without repainting."""
    bars = completed_candles(frame, (now or now_ist()).astimezone(IST)).tail(180).reset_index(drop=True)
    pivots = _confirmed_pivots(bars)
    lows = [p for p in pivots if p["kind"] == "LOW" and finite(p.get("rsi"))]
    highs = [p for p in pivots if p["kind"] == "HIGH" and finite(p.get("rsi"))]
    bullish = bearish = None
    min_price_diff = max(0.05 * atr if finite(atr) else 2.0, 2.0)
    if len(lows) >= 2:
        a, b = lows[-2], lows[-1]
        gap, age = b["index"] - a["index"], len(bars) - 1 - b["index"]
        if 3 <= gap <= 60 and age <= 25 and b["price"] <= a["price"] - min_price_diff and b["rsi"] >= a["rsi"] + DIVERGENCE_RSI_DELTA:
            bullish = {"type": "BULLISH", "price_low_1": a["price"], "price_low_2": b["price"],
                       "rsi_low_1": round(a["rsi"], 2), "rsi_low_2": round(b["rsi"], 2),
                       "first_pivot_time": a["timestamp"], "second_pivot_time": b["timestamp"],
                       "price_lower_low_points": round(a["price"] - b["price"], 2),
                       "rsi_higher_low_points": round(b["rsi"] - a["rsi"], 2)}
    if len(highs) >= 2:
        a, b = highs[-2], highs[-1]
        gap, age = b["index"] - a["index"], len(bars) - 1 - b["index"]
        if 3 <= gap <= 60 and age <= 25 and b["price"] >= a["price"] + min_price_diff and b["rsi"] <= a["rsi"] - DIVERGENCE_RSI_DELTA:
            bearish = {"type": "BEARISH", "price_high_1": a["price"], "price_high_2": b["price"],
                       "rsi_high_1": round(a["rsi"], 2), "rsi_high_2": round(b["rsi"], 2),
                       "first_pivot_time": a["timestamp"], "second_pivot_time": b["timestamp"],
                       "price_higher_high_points": round(b["price"] - a["price"], 2),
                       "rsi_lower_high_points": round(a["rsi"] - b["rsi"], 2)}
    return {
        "available": len(bars) >= 35 and (len(lows) >= 2 or len(highs) >= 2),
        "bullish_available": len(bars) >= 35 and len(lows) >= 2,
        "bearish_available": len(bars) >= 35 and len(highs) >= 2,
        "bullish": bullish, "bearish": bearish,
        "confirmed_pivot_lows": len(lows), "confirmed_pivot_highs": len(highs),
        "lookback_closed_bars": len(bars),
        "method": "REGULAR_DIVERGENCE_ON_CONFIRMED_2_LEFT_2_RIGHT_PIVOTS",
    }




def true_range(frame: pd.DataFrame) -> pd.Series:
    prev = frame["close"].shift(1)
    tr = pd.concat([frame["high"] - frame["low"], (frame["high"] - prev).abs(), (frame["low"] - prev).abs()], axis=1).max(axis=1)
    if "timestamp" in frame and len(frame):
        sessions = frame["timestamp"].dt.tz_convert(IST).dt.date
        tr = tr.mask(sessions.ne(sessions.shift(1)), frame["high"] - frame["low"])
    return tr


def rsi_value(close: pd.Series, period: int = 14, timestamps: Optional[pd.Series] = None) -> float:
    if len(close) < period + 1:
        return float("nan")
    diff_all = close.astype(float).diff()
    if timestamps is not None and len(timestamps) == len(close):
        stamp_series = pd.to_datetime(timestamps, utc=True, errors="coerce")
        local_dates = stamp_series.dt.tz_convert(IST).dt.date
        diff_all = diff_all.mask(local_dates.ne(local_dates.shift(1)))
    diff = diff_all.dropna()
    gain = diff.clip(lower=0).ewm(alpha=1/period, adjust=False, min_periods=period).mean()
    loss = (-diff.clip(upper=0)).ewm(alpha=1/period, adjust=False, min_periods=period).mean()
    if len(gain) == 0:
        return float("nan")
    g, l = number(gain.iloc[-1]), number(loss.iloc[-1])
    if l == 0 and g == 0: return 50.0
    if l == 0: return 100.0
    return 100 - 100/(1 + g/l)


def indicator_set(frame: pd.DataFrame, live_spot: float, now: Optional[datetime] = None,
                  calculate_rsi: bool = True, vwap_frame: Optional[pd.DataFrame] = None) -> Indicators:
    """Indicators use cached prior-session context; trigger momentum and range remain session-local.

    NIFTY spot has no usable traded volume. VWAP is calculated only from the separately supplied
    NIFTY futures candles; unavailable futures data is reported explicitly and never replaced by
    fabricated index volume.
    """
    effective_now = (now or now_ist()).astimezone(IST)
    bars = completed_candles(frame, effective_now)
    if bars.empty:
        raise ScannerError("No completed one-minute candles are available for indicator warm-up.")
    session_dates = bars["timestamp"].dt.tz_convert(IST).dt.date
    session_bars = bars.loc[session_dates == effective_now.date()].copy().reset_index(drop=True)
    if session_bars.empty:
        raise ScannerError("No completed current-session candles are available for price-trigger evaluation.")

    closes = bars["close"].astype(float)
    trs = true_range(bars)
    atr = number(trs.tail(14).mean(), number((bars["high"] - bars["low"]).tail(14).mean(), 25.0))
    atr = max(8.0, atr) if finite(atr) else 25.0

    # Never calculate current momentum across the overnight close/open gap.
    session_closes = session_bars["close"].astype(float)
    momentum_1m = (float(session_closes.iloc[-1] / session_closes.iloc[-2] - 1.0)
                   if len(session_closes) >= 2 and session_closes.iloc[-2] > 0 else 0.0)
    momentum_3m = (float(session_closes.iloc[-1] / session_closes.iloc[-4] - 1.0)
                   if len(session_closes) >= 4 and session_closes.iloc[-4] > 0 else 0.0)

    vwap = vwap_slope = float("nan")
    volume_source = "UNAVAILABLE_NIFTY_FUTURES_KEY_NOT_CONFIGURED"
    if isinstance(vwap_frame, pd.DataFrame) and not vwap_frame.empty:
        future_bars = completed_candles(vwap_frame, effective_now)
        future_dates = future_bars["timestamp"].dt.tz_convert(IST).dt.date if not future_bars.empty else pd.Series([], dtype=object)
        future_bars = future_bars.loc[future_dates == effective_now.date()].copy() if not future_bars.empty else future_bars
        vol = future_bars["volume"].clip(lower=0) if not future_bars.empty else pd.Series(dtype=float)
        if not future_bars.empty and float(vol.sum()) > 0:
            typical = (future_bars["high"] + future_bars["low"] + future_bars["close"]) / 3.0
            vwap = number(float((typical * vol).sum() / vol.sum()))
            prior_n = max(1, len(future_bars) - min(5, len(future_bars) - 1))
            prior_vol = vol.iloc[:prior_n]
            if float(prior_vol.sum()) > 0:
                vwap_prior = number(float((typical.iloc[:prior_n] * prior_vol).sum() / prior_vol.sum()))
                vwap_slope = vwap - vwap_prior if finite(vwap) and finite(vwap_prior) else float("nan")
            else:
                vwap_slope = float("nan")
            volume_source = "ACTIVE_NIFTY_FUTURES_SESSION_VWAP"
        else:
            volume_source = "UNAVAILABLE_FUTURES_CANDLE_VOLUME_ZERO"

    # Wilder-style directional movement, resetting directional moves across session boundaries.
    if len(bars) >= 15:
        up_move = bars["high"].diff()
        down_move = -bars["low"].diff()
        session_change = bars["timestamp"].dt.tz_convert(IST).dt.date.ne(bars["timestamp"].dt.tz_convert(IST).dt.date.shift(1))
        up_move = up_move.mask(session_change)
        down_move = down_move.mask(session_change)
        plus_dm = pd.Series(np.where((up_move > down_move) & (up_move > 0), up_move, 0.0), index=bars.index).where(up_move.notna())
        minus_dm = pd.Series(np.where((down_move > up_move) & (down_move > 0), down_move, 0.0), index=bars.index).where(down_move.notna())
        tr_mean = trs.ewm(alpha=1/14, adjust=False, min_periods=8).mean().replace(0, np.nan)
        plus_series = 100 * plus_dm.ewm(alpha=1/14, adjust=False, min_periods=8).mean() / tr_mean
        minus_series = 100 * minus_dm.ewm(alpha=1/14, adjust=False, min_periods=8).mean() / tr_mean
        denominator = (plus_series + minus_series).replace(0, np.nan)
        dx_series = (100 * (plus_series - minus_series).abs() / denominator).clip(0, 100)
        adx_series = dx_series.ewm(alpha=1/14, adjust=False, min_periods=8).mean().clip(0, 100)
        plus_di = number(plus_series.iloc[-1])
        minus_di = number(minus_series.iloc[-1])
        adx = number(adx_series.iloc[-1])
    else:
        plus_di = minus_di = adx = float("nan")

    recent = bars.tail(80)
    recent_pivot_highs = _pivot_prices(recent, "high", "high")
    recent_pivot_lows = _pivot_prices(recent, "low", "low")
    return Indicators(
        spot=float(live_spot), vwap=vwap, vwap_slope=vwap_slope, atr=atr,
        rsi=rsi_value(closes, timestamps=bars["timestamp"]) if calculate_rsi else float("nan"), adx=adx, plus_di=plus_di, minus_di=minus_di,
        momentum_1m=momentum_1m, momentum_3m=momentum_3m,
        last_close=float(session_closes.iloc[-1]),
        prev_close=float(session_closes.iloc[-2]) if len(session_closes) >= 2 else float(session_closes.iloc[-1]),
        session_high=float(session_bars["high"].max()), session_low=float(session_bars["low"].min()),
        swing_high=max(recent_pivot_highs) if recent_pivot_highs else float(recent["high"].max()),
        swing_low=min(recent_pivot_lows) if recent_pivot_lows else float(recent["low"].min()),
        candles=len(session_bars), volume_source=volume_source,
    )


def _pivot_prices(frame: pd.DataFrame, column: str, which: str) -> list[float]:
    if frame is None or len(frame) < 5:
        return []
    values = frame[column].to_numpy(dtype=float)
    result: list[float] = []
    for i in range(2, len(values) - 2):
        window = values[i-2:i+3]
        if which == "high" and values[i] >= max(window) and sum(values[i] == x for x in window) == 1:
            result.append(float(values[i]))
        elif which == "low" and values[i] <= min(window) and sum(values[i] == x for x in window) == 1:
            result.append(float(values[i]))
    return result


def _snapshot_rows(snapshot: Mapping[str, Any]) -> dict[float, Mapping[str, Any]]:
    out: dict[float, Mapping[str, Any]] = {}
    for row in snapshot.get("rows", []) if isinstance(snapshot.get("rows", []), list) else []:
        if isinstance(row, dict) and finite(row.get("strike")):
            out[float(row["strike"])] = row
    return out


def _recent_snapshot(snapshots: Sequence[dict[str, Any]], now: datetime, expiry: str,
                     low_minutes: float = 1.5, high_minutes: float = 7.5,
                     target_minutes: float = 3.0) -> tuple[Optional[dict[str, Any]], Optional[float]]:
    """Choose a prior same-session snapshot close to one scheduled scan interval old."""
    current = now.astimezone(IST)
    matches: list[tuple[float, dict[str, Any]]] = []
    for snap in snapshots:
        if not isinstance(snap, dict):
            continue
        stamp = parse_dt(snap.get("timestamp"))
        if not stamp or stamp.date() != current.date() or str(snap.get("expiry", "")) != expiry:
            continue
        age = (current - stamp).total_seconds() / 60.0
        if low_minutes <= age <= high_minutes:
            matches.append((age, snap))
    if not matches:
        return None, None
    age, snap = min(matches, key=lambda item: (abs(item[0] - target_minutes), -item[0]))
    return snap, age


def oi_snapshot(chain: Sequence[dict[str, Any]], expiry: str, now: datetime) -> dict[str, Any]:
    rows = []
    for row in chain:
        strike = number(row.get("strike_price"))
        if not finite(strike):
            continue
        ce = row.get("call_options") if isinstance(row.get("call_options"), dict) else {}
        pe = row.get("put_options") if isinstance(row.get("put_options"), dict) else {}
        ce_md = ce.get("market_data") if isinstance(ce.get("market_data"), dict) else {}
        pe_md = pe.get("market_data") if isinstance(pe.get("market_data"), dict) else {}
        rows.append({
            "strike": float(strike),
            "call_oi": max(0.0, number(ce_md.get("oi"), 0.0)),
            "put_oi": max(0.0, number(pe_md.get("oi"), 0.0)),
            "call_ltp": number(ce_md.get("ltp")),
            "put_ltp": number(pe_md.get("ltp")),
            "call_volume": max(0.0, number(ce_md.get("volume"), 0.0)),
            "put_volume": max(0.0, number(pe_md.get("volume"), 0.0)),
        })
    return {"timestamp": now.isoformat(), "expiry": expiry, "rows": rows}


def classify_oi_flow(oi_change: Optional[float], premium_change: Optional[float]) -> str:
    """Use OI and same-session option premium change together; OI alone is not writing/ buying."""
    if oi_change is None or premium_change is None or not finite(oi_change) or not finite(premium_change):
        return "UNKNOWN"
    oi_up, premium_up = oi_change >= 0.001, premium_change >= 0.002
    oi_down, premium_down = oi_change <= -0.001, premium_change <= -0.002
    if oi_up and premium_down: return "SHORT_BUILDUP_WRITING"
    if oi_up and premium_up: return "LONG_BUILDUP_BUYING"
    if oi_down and premium_up: return "SHORT_COVERING"
    if oi_down and premium_down: return "LONG_UNWINDING"
    return "FLAT_OR_MIXED"


def analyze_oi(chain: Sequence[dict[str, Any]], snapshots: Sequence[dict[str, Any]], spot: float,
               expiry: str, now: datetime, strike_step: float, scan_interval_seconds: int = 180) -> dict[str, Any]:
    current = oi_snapshot(chain, expiry, now)
    interval_minutes = max(1.0, min(15.0, float(scan_interval_seconds) / 60.0))
    prior, age = _recent_snapshot(
        snapshots, now, expiry,
        low_minutes=max(0.5, interval_minutes * 0.5),
        high_minutes=min(20.0, max(interval_minutes * 2.5, interval_minutes + 1.0)),
        target_minutes=interval_minutes,
    )
    prior_rows = _snapshot_rows(prior) if prior else {}
    rows = _snapshot_rows(current)
    all_calls = sum(number(r.get("call_oi"), 0.0) for r in rows.values())
    all_puts = sum(number(r.get("put_oi"), 0.0) for r in rows.values())
    pcr = all_puts / all_calls if all_calls > 0 else float("nan")
    calls_delta = puts_delta = 0.0
    calls_base = puts_base = 0.0
    wall_items: list[dict[str, Any]] = []
    for strike, row in rows.items():
        old = prior_rows.get(strike, {})
        call_oi, put_oi = number(row.get("call_oi"), 0), number(row.get("put_oi"), 0)
        call_old, put_old = number(old.get("call_oi")), number(old.get("put_oi"))
        call_prem, put_prem = number(row.get("call_ltp")), number(row.get("put_ltp"))
        call_prem_old, put_prem_old = number(old.get("call_ltp")), number(old.get("put_ltp"))
        c_change = (call_oi - call_old) / call_old if finite(call_old) and call_old > 0 else None
        p_change = (put_oi - put_old) / put_old if finite(put_old) and put_old > 0 else None
        c_premium = (call_prem - call_prem_old) / call_prem_old if finite(call_prem) and finite(call_prem_old) and call_prem_old > 0 else None
        p_premium = (put_prem - put_prem_old) / put_prem_old if finite(put_prem) and finite(put_prem_old) and put_prem_old > 0 else None
        if c_change is not None and call_old > 0:
            calls_delta += call_oi - call_old; calls_base += call_old
        if p_change is not None and put_old > 0:
            puts_delta += put_oi - put_old; puts_base += put_old
        if abs(strike - spot) <= max(500, 8 * strike_step):
            wall_items.append({
                "strike": strike, "call_oi": call_oi, "put_oi": put_oi,
                "call_prev_oi": call_old if finite(call_old) else None,
                "put_prev_oi": put_old if finite(put_old) else None,
                "call_delta_oi": (call_oi - call_old) if finite(call_old) else None,
                "put_delta_oi": (put_oi - put_old) if finite(put_old) else None,
                "call_ltp": call_prem, "put_ltp": put_prem,
                "call_prev_ltp": call_prem_old if finite(call_prem_old) else None,
                "put_prev_ltp": put_prem_old if finite(put_prem_old) else None,
                "call_change_pct": c_change, "put_change_pct": p_change,
                "call_premium_change_pct": c_premium, "put_premium_change_pct": p_premium,
                "call_flow": classify_oi_flow(c_change, c_premium),
                "put_flow": classify_oi_flow(p_change, p_premium),
                "call_volume": number(row.get("call_volume"), 0), "put_volume": number(row.get("put_volume"), 0),
            })
    tactical_available = calls_base > 0 and puts_base > 0 and age is not None
    call_tactical = calls_delta / calls_base if calls_base > 0 else None
    put_tactical = puts_delta / puts_base if puts_base > 0 else None
    # Static OI concentration and *dynamic* OI flow are different facts. Mark only a
    # small set of nearby concentration peaks as walls; never label a raw OI level
    # "confirmed" merely because its OI is large.
    ordered = sorted(wall_items, key=lambda row: number(row.get("strike"), 0.0))
    for side in ("CALL", "PUT"):
        low_key = "call_oi" if side == "CALL" else "put_oi"
        vals = [number(row.get(low_key), 0.0) for row in ordered if number(row.get(low_key), 0.0) > 0]
        peak = max(vals, default=0.0)
        q75 = float(np.quantile(vals, 0.75)) if vals else float("inf")
        eligible: list[tuple[float, dict[str, Any]]] = []
        for index, row in enumerate(ordered):
            oi_value = number(row.get(low_key), 0.0)
            prev_value = number(ordered[index - 1].get(low_key), 0.0) if index else -1.0
            next_value = number(ordered[index + 1].get(low_key), 0.0) if index + 1 < len(ordered) else -1.0
            local_peak = oi_value >= prev_value and oi_value >= next_value
            if oi_value > 0 and oi_value >= q75 and oi_value >= peak * 0.38 and local_peak:
                eligible.append((oi_value, row))
        chosen = {id(row) for _, row in sorted(eligible, key=lambda item: item[0], reverse=True)[:5]}
        for row in ordered:
            oi_value = number(row.get(low_key), 0.0)
            change = row["call_change_pct"] if side == "CALL" else row["put_change_pct"]
            flow = row["call_flow"] if side == "CALL" else row["put_flow"]
            row[f"{side.lower()}_wall"] = id(row) in chosen
            row[f"{side.lower()}_state"] = (
                "BUILDING" if finite(change) and change >= 0.002 else
                "WEAKENING" if finite(change) and change <= -0.002 else
                "STABLE" if finite(change) else "UNKNOWN"
            )
            row[f"{side.lower()}_flow"] = flow
            row[f"{side.lower()}_wall_type"] = "LOCAL_OI_CONCENTRATION_PEAK" if id(row) in chosen else None
    calls_walls = sorted([w for w in wall_items if w.get("call_wall") and w["strike"] >= spot - 1e-6], key=lambda w: w["strike"])
    puts_walls = sorted([w for w in wall_items if w.get("put_wall") and w["strike"] <= spot + 1e-6], key=lambda w: w["strike"], reverse=True)
    return {
        "snapshot": current, "snapshot_age_minutes": age, "tactical_available": tactical_available,
        "call_tactical_change_pct": call_tactical, "put_tactical_change_pct": put_tactical,
        "call_total_oi": all_calls, "put_total_oi": all_puts, "pcr": pcr,
        "walls": sorted(wall_items, key=lambda w: w["strike"]),
        "call_resistance_walls": calls_walls[:8], "put_support_walls": puts_walls[:8],
        "source": "SAME_SESSION_OI_AND_PREMIUM_SNAPSHOTS" if tactical_available else "OI_CONCENTRATION_WITHOUT_VALID_TACTICAL_BASELINE",
    }


def make_structure_levels(frame: pd.DataFrame, indicators: Indicators, oi: Mapping[str, Any], step: float,
                         now: Optional[datetime] = None, fib: Optional[Mapping[str, Any]] = None) -> list[Level]:
    """Build levels from confirmed price pivots, session extremes, recent Fib and selected OI peaks.

    A static OI concentration is never itself described as live writing/covering confirmation.
    Dynamic flow fields are attached only when a valid same-session OI comparison exists.
    """
    effective_now = (now or now_ist()).astimezone(IST)
    bars = completed_candles(frame, effective_now)
    recent = bars.tail(90)
    tolerance = max(8.0, min(22.0, indicators.atr * 0.22))
    raw: list[tuple[float, str, str, float]] = []
    for val in _pivot_prices(recent, "high", "high"):
        if abs(indicators.spot - val) <= max(350.0, indicators.atr * 12):
            raw.append((val, "RESISTANCE", "PRICE_PIVOT_HIGH", 0.58))
    for val in _pivot_prices(recent, "low", "low"):
        if abs(indicators.spot - val) <= max(350.0, indicators.atr * 12):
            raw.append((val, "SUPPORT", "PRICE_PIVOT_LOW", 0.58))
    raw += [(indicators.session_high, "RESISTANCE", "SESSION_HIGH", 0.66),
            (indicators.session_low, "SUPPORT", "SESSION_LOW", 0.66)]

    # Only attach recent, sufficiently large confirmed Fib legs. Older pivots are not
    # allowed to create irrelevant targets several hundred points from current structure.
    fib = fib or {}
    fib_bars = min(180, len(bars))
    fib_age_limit = min(45, max(20, int(fib_bars * 0.35)))
    fib_range_floor = max(1.0 * indicators.atr, 30.0)
    if fib.get("available"):
        up_leg = fib.get("up_leg") if isinstance(fib.get("up_leg"), Mapping) else None
        down_leg = fib.get("down_leg") if isinstance(fib.get("down_leg"), Mapping) else None
        if up_leg and number(up_leg.get("range_points"), 0.0) >= fib_range_floor:
            age = max(0, fib_bars - 1 - int(number(up_leg.get("end_index"), fib_bars - 1)))
            if age <= fib_age_limit:
                retr = up_leg.get("retracements", {}) if isinstance(up_leg.get("retracements"), Mapping) else {}
                ext = up_leg.get("extensions", {}) if isinstance(up_leg.get("extensions"), Mapping) else {}
                for key, name, strength in (("50.0", "FIB_UP_RETRACEMENT_50", 0.64),
                                            ("61.8", "FIB_UP_RETRACEMENT_61_8", 0.68),
                                            ("78.6", "FIB_UP_RETRACEMENT_78_6", 0.60)):
                    val = number(retr.get(key))
                    if finite(val) and abs(val - indicators.spot) <= max(250.0, indicators.atr * 10):
                        raw.append((val, "SUPPORT", name, strength))
                for key, name in (("127.2", "FIB_UP_EXTENSION_127_2"), ("161.8", "FIB_UP_EXTENSION_161_8")):
                    val = number(ext.get(key))
                    if finite(val) and val > indicators.spot + max(0.8 * indicators.atr, 15):
                        raw.append((val, "RESISTANCE", name, 0.64 if key == "127.2" else 0.60))
        if down_leg and number(down_leg.get("range_points"), 0.0) >= fib_range_floor:
            age = max(0, fib_bars - 1 - int(number(down_leg.get("end_index"), fib_bars - 1)))
            if age <= fib_age_limit:
                retr = down_leg.get("retracements", {}) if isinstance(down_leg.get("retracements"), Mapping) else {}
                ext = down_leg.get("extensions", {}) if isinstance(down_leg.get("extensions"), Mapping) else {}
                for key, name, strength in (("50.0", "FIB_DOWN_RETRACEMENT_50", 0.62),
                                            ("61.8", "FIB_DOWN_RETRACEMENT_61_8", 0.68),
                                            ("78.6", "FIB_DOWN_RETRACEMENT_78_6", 0.60)):
                    val = number(retr.get(key))
                    if finite(val) and val > indicators.spot and abs(val - indicators.spot) <= max(250.0, indicators.atr * 10):
                        raw.append((val, "RESISTANCE", name, strength))
                high_val = number(down_leg.get("high"))
                if finite(high_val) and high_val > indicators.spot + 0.5 * indicators.atr:
                    raw.append((high_val, "RESISTANCE", "FIB_DOWN_RETRACEMENT_100", 0.62))
                for key, name in (("127.2", "FIB_DOWN_EXTENSION_127_2"), ("161.8", "FIB_DOWN_EXTENSION_161_8")):
                    val = number(ext.get(key))
                    if finite(val) and val < indicators.spot - max(0.8 * indicators.atr, 15):
                        raw.append((val, "SUPPORT", name, 0.64 if key == "127.2" else 0.60))

    walls = [w for w in oi.get("walls", []) if isinstance(w, Mapping) and finite(w.get("strike"))]
    call_peak = max((number(w.get("call_oi"), 0.0) for w in walls), default=1.0)
    put_peak = max((number(w.get("put_oi"), 0.0) for w in walls), default=1.0)
    for wall in walls:
        strike = number(wall.get("strike"))
        if abs(strike - indicators.spot) > max(350.0, indicators.atr * 12):
            continue
        call_oi = number(wall.get("call_oi"), 0.0)
        put_oi = number(wall.get("put_oi"), 0.0)
        if wall.get("call_wall") and strike >= indicators.spot:
            strength = 0.58 + 0.28 * clamp(call_oi / max(1.0, call_peak), 0.0, 1.0)
            raw.append((strike, "RESISTANCE", "CALL_OI_CONCENTRATION", strength))
        if wall.get("put_wall") and strike <= indicators.spot:
            strength = 0.58 + 0.28 * clamp(put_oi / max(1.0, put_peak), 0.0, 1.0)
            raw.append((strike, "SUPPORT", "PUT_OI_CONCENTRATION", strength))

    levels: list[Level] = []
    used: set[int] = set()
    for i, (price, kind, source, strength) in enumerate(raw):
        if i in used or not finite(price):
            continue
        cluster = [(j, item) for j, item in enumerate(raw)
                   if j not in used and item[1] == kind and abs(item[0] - price) <= tolerance]
        for j, _ in cluster:
            used.add(j)
        weights = [max(0.05, item[3]) for _, item in cluster]
        level_price = sum(item[0] * weight for (_, item), weight in zip(cluster, weights)) / sum(weights)
        sources = sorted({item[2] for _, item in cluster})
        matching_walls = [w for w in walls if abs(number(w.get("strike"), -999999) - level_price) <= max(tolerance, step * 0.15)]
        wall = max(matching_walls, key=lambda x: number(x.get("call_oi" if kind == "RESISTANCE" else "put_oi"), 0.0), default={})
        side_key = "call" if kind == "RESISTANCE" else "put"
        change = number(wall.get(f"{side_key}_change_pct"))
        state_name = str(wall.get(f"{side_key}_state", "UNKNOWN"))
        flow_name = str(wall.get(f"{side_key}_flow", "UNKNOWN"))
        is_dynamic = bool(oi.get("tactical_available")) and finite(change) and flow_name not in {"", "UNKNOWN"}
        touches = sum(1 for _, x in cluster if "PIVOT" in x[2])
        cluster_strength = clamp(max(weights) + min(0.16, max(0, len(cluster)-1)*0.035), 0.0, 0.97)
        if is_dynamic:
            notes = "LOCAL_OI_FLOW_AVAILABLE;FLOW_DIRECTION_MUST_MATCH_SETUP"
        elif any("OI_CONCENTRATION" in src for src in sources):
            notes = "STATIC_OI_CONCENTRATION_ONLY;NOT_FLOW_CONFIRMED"
        else:
            notes = "PRICE_STRUCTURE"
        levels.append(Level(float(level_price), kind, "+".join(sources), cluster_strength, max(1, touches),
                            change if finite(change) else None, state_name if is_dynamic else "UNKNOWN",
                            flow_name if is_dynamic else "UNKNOWN", notes))
    return sorted(levels, key=lambda x: x.price)


def nearest_level(levels: Sequence[Level], spot: float, kind: str) -> Optional[Level]:
    candidates = [l for l in levels if l.kind == kind and ((l.price > spot + 0.5) if kind == "RESISTANCE" else (l.price < spot - 0.5))]
    if not candidates: return None
    return min(candidates, key=lambda l: abs(l.price - spot))


def _touch_evidence(frame: pd.DataFrame, level: float, side: str, atr: float, now: Optional[datetime] = None) -> tuple[int, bool, float]:
    """Count distinct recent tests and return away-close evidence, latest extremum, using completed candles."""
    bars = completed_candles(frame, (now or now_ist()).astimezone(IST)).tail(18)
    if len(bars) < 4:
        return 0, False, float("nan")
    tolerance = max(6.0, min(18.0, atr * 0.30))
    col = "low" if side == "SUPPORT" else "high"
    touches = 0
    armed = True
    for _, row in bars.iterrows():
        extremum = number(row[col])
        close_i = number(row["close"])
        bar_high = number(row["high"])
        touched = (extremum <= level + tolerance and bar_high >= level - tolerance)
        # A new test is counted only after price moved away from the level and retested it.
        if touched and armed:
            touches += 1
            armed = False
        if not touched and side == "SUPPORT" and close_i > level + tolerance * 1.2:
            armed = True
        elif not touched and side == "RESISTANCE" and close_i < level - tolerance * 1.2:
            armed = True
    close = number(bars.iloc[-1]["close"])
    away = close > level + tolerance * .25 if side == "SUPPORT" else close < level - tolerance * .25
    return touches, away, number(bars.iloc[-1][col])


def _oi_local_evidence(oi: Mapping[str, Any], direction: str, spot: float, step: float) -> tuple[float, list[str]]:
    """Score both sides of the option chain; OI is interpreted with premium change, not alone."""
    walls = [w for w in oi.get("walls", []) if isinstance(w, dict) and finite(w.get("strike"))]
    evidence: list[str] = []
    score = 0.0

    if direction == "BULLISH":
        # Put writing is support; falling OI with falling premium can be put-long liquidation.
        put_rows = [w for w in walls if number(w.get("strike"), 1e9) <= spot + step * 0.30]
        put_rows.sort(key=lambda w: abs(spot - number(w.get("strike"), spot)))
        if not put_rows:
            evidence.append("LOCAL_PUT_FLOW_UNAVAILABLE")
        else:
            row = put_rows[0]; flow = str(row.get("put_flow", "UNKNOWN")); state = str(row.get("put_state", "UNKNOWN"))
            if flow == "SHORT_BUILDUP_WRITING": score += 24; evidence.append(f"PUT_WRITING_SUPPORT_{number(row.get('strike')):.0f}")
            elif flow == "LONG_UNWINDING": score += 10; evidence.append(f"PUT_LONG_UNWINDING_{number(row.get('strike')):.0f}")
            elif flow == "LONG_BUILDUP_BUYING": score -= 12; evidence.append(f"PUT_BUYING_COUNTERFLOW_{number(row.get('strike')):.0f}")
            elif flow == "SHORT_COVERING": score -= 8; evidence.append(f"PUT_SHORT_COVERING_COUNTERFLOW_{number(row.get('strike')):.0f}")
            elif state == "BUILDING": score += 8; evidence.append(f"PUT_OI_BUILDING_{number(row.get('strike')):.0f}_FLOW_UNCLASSIFIED")
            elif state == "WEAKENING": score -= 8; evidence.append(f"PUT_SUPPORT_WEAKENING_{number(row.get('strike')):.0f}")
        call_rows = [w for w in walls if number(w.get("strike"), -1e9) > spot]
        call_rows.sort(key=lambda w: number(w.get("strike"), 1e9))
        if call_rows:
            row = call_rows[0]; flow = str(row.get("call_flow", "UNKNOWN")); state = str(row.get("call_state", "UNKNOWN"))
            if flow == "SHORT_COVERING" or state == "WEAKENING": score += 10; evidence.append(f"CALL_RESISTANCE_EASING_{number(row.get('strike')):.0f}")
            elif flow == "LONG_BUILDUP_BUYING": score += 7; evidence.append(f"CALL_BUYING_MOMENTUM_{number(row.get('strike')):.0f}")
            elif flow == "SHORT_BUILDUP_WRITING": score -= 7; evidence.append(f"CALL_WRITING_OVERHEAD_{number(row.get('strike')):.0f}")
    else:
        # Call writing/long liquidation is bearish; put buying can confirm a rejection before support breaks.
        call_rows = [w for w in walls if number(w.get("strike"), -1e9) >= spot - step * 0.30]
        call_rows.sort(key=lambda w: abs(spot - number(w.get("strike"), spot)))
        if not call_rows:
            evidence.append("LOCAL_CALL_FLOW_UNAVAILABLE")
        else:
            row = call_rows[0]; flow = str(row.get("call_flow", "UNKNOWN")); state = str(row.get("call_state", "UNKNOWN"))
            if flow == "SHORT_BUILDUP_WRITING": score += 24; evidence.append(f"CALL_WRITING_RESISTANCE_{number(row.get('strike')):.0f}")
            elif flow == "LONG_UNWINDING": score += 10; evidence.append(f"CALL_LONG_UNWINDING_{number(row.get('strike')):.0f}")
            elif flow == "LONG_BUILDUP_BUYING": score -= 12; evidence.append(f"CALL_BUYING_COUNTERFLOW_{number(row.get('strike')):.0f}")
            elif flow == "SHORT_COVERING": score -= 8; evidence.append(f"CALL_SHORT_COVERING_COUNTERFLOW_{number(row.get('strike')):.0f}")
            elif state == "BUILDING": score += 7; evidence.append(f"CALL_OI_BUILDING_{number(row.get('strike')):.0f}_FLOW_UNCLASSIFIED")
            elif state == "WEAKENING": score -= 7; evidence.append(f"CALL_RESISTANCE_WEAKENING_{number(row.get('strike')):.0f}")
        put_rows = [w for w in walls if number(w.get("strike"), 1e9) < spot]
        put_rows.sort(key=lambda w: abs(spot - number(w.get("strike"), spot)))
        if put_rows:
            row = put_rows[0]; flow = str(row.get("put_flow", "UNKNOWN")); state = str(row.get("put_state", "UNKNOWN"))
            if flow == "LONG_BUILDUP_BUYING": score += 16; evidence.append(f"PUT_BUYING_BEARISH_CONFIRMATION_{number(row.get('strike')):.0f}")
            elif flow == "SHORT_COVERING": score += 8; evidence.append(f"PUT_SHORT_COVERING_{number(row.get('strike')):.0f}")
            elif flow == "SHORT_BUILDUP_WRITING": score -= 10; evidence.append(f"PUT_WRITING_SUPPORT_COUNTERFLOW_{number(row.get('strike')):.0f}")
            elif flow == "LONG_UNWINDING": score -= 6; evidence.append(f"PUT_LONG_UNWINDING_COUNTERFLOW_{number(row.get('strike')):.0f}")
            elif state == "WEAKENING": score += 5; evidence.append(f"PUT_SUPPORT_WEAKENING_{number(row.get('strike')):.0f}")

    # Include any locally material OI change in diagnostics without treating OI growth alone as writing.
    relevant = []
    for row in walls:
        if abs(number(row.get("strike"), spot) - spot) <= step * 1.5:
            key = "put_change_pct" if direction == "BULLISH" else "call_change_pct"
            value = number(row.get(key))
            if finite(value): relevant.append((abs(number(row.get("strike"), spot)-spot), value, number(row.get("strike"), spot)))
    if relevant:
        _, change, strike = min(relevant, key=lambda item: item[0])
        if abs(change) >= 0.005:
            evidence.append(f"LOCAL_OI_CHANGE_{strike:.0f}_{change*100:+.2f}%")
    return clamp(score, -18, 34), evidence


def _level_touch_stats(frame: pd.DataFrame, level: float, kind: str, atr: float,
                          now: datetime, lookback: int = 36) -> dict[str, Any]:
    """Count separate visits to a level, not adjacent candles within one visit."""
    bars = completed_candles(frame, now.astimezone(IST)).tail(max(8, int(lookback))).reset_index(drop=True)
    if bars.empty or not finite(level):
        return {"touches": 0, "recent_touch": False, "last_touch_age_bars": None,
                "reclaimed": False, "rejected": False, "last_extreme": None}
    tolerance = max(5.0, min(16.0, 0.24 * atr if finite(atr) else 5.0))
    col = "low" if kind == "SUPPORT" else "high"
    visits: list[int] = []
    in_visit = False
    for i, row in bars.iterrows():
        hi, lo, close = number(row.get("high")), number(row.get("low")), number(row.get("close"))
        # A touch must occur at the actual side-specific extremum. Merely travelling through
        # a higher level while rebounding from a lower one does not count as support there.
        if kind == "SUPPORT":
            touched = finite(lo) and level - 2.0 * tolerance <= lo <= level + tolerance
        else:
            touched = finite(hi) and level - tolerance <= hi <= level + 2.0 * tolerance
        if touched and not in_visit:
            visits.append(int(i))
            in_visit = True
        elif not touched and finite(close) and abs(close - level) > 1.35 * tolerance:
            # Re-arm after price departs the level in either direction. Repeated approaches
            # following a break/retest must not be collapsed into one indefinitely long visit.
            in_visit = False
    last_close = number(bars.iloc[-1]["close"])
    previous_close = number(bars.iloc[-2]["close"]) if len(bars) > 1 else last_close
    buffer = max(1.5, min(5.0, 0.06 * atr if finite(atr) else 1.5))
    reclaimed = kind == "SUPPORT" and finite(last_close) and last_close > level + buffer
    rejected = kind == "RESISTANCE" and finite(last_close) and last_close < level - buffer
    age = len(bars) - 1 - visits[-1] if visits else None
    return {"touches": len(visits), "touch_indices": visits[-8:],
            "recent_touch": bool(age is not None and age <= 7),
            "last_touch_age_bars": age, "reclaimed": bool(reclaimed),
            "rejected": bool(rejected), "last_extreme": number(bars.iloc[-1][col]),
            "tolerance": round(tolerance, 2), "last_close": last_close,
            "previous_close": previous_close}


def _local_pair_strength(oi: Mapping[str, Any], direction: str, level: float,
                             step: float) -> dict[str, Any]:
    """Price-action scoring aid; final eligibility is still decided by qualify_local_oi."""
    rows = [r for r in oi.get("walls", []) if isinstance(r, Mapping) and finite(r.get("strike"))
            and abs(number(r.get("strike")) - level) <= max(2.0 * step, 75.0)]
    threshold = 0.025  # Strict writing threshold is greater than 2.5%.
    prem_floor = 0.002  # Aligned with the OI-flow classifier's minimum directional premium movement.
    if direction == "BULLISH":
        writing_key, covering_key = "put", "call"
    else:
        writing_key, covering_key = "call", "put"

    def writing_ok(row: Mapping[str, Any]) -> bool:
        oi_change = number(row.get(f"{writing_key}_change_pct"))
        prem_change = number(row.get(f"{writing_key}_premium_change_pct"))
        strike = number(row.get("strike"))
        location_ok = strike <= level + step + 0.01 if direction == "BULLISH" else strike >= level - step - 0.01
        return bool(location_ok and oi_change > threshold and prem_change <= -prem_floor
                    and str(row.get(f"{writing_key}_flow", "")) == "SHORT_BUILDUP_WRITING")

    def covering_ok(row: Mapping[str, Any]) -> bool:
        oi_change = number(row.get(f"{covering_key}_change_pct"))
        prem_change = number(row.get(f"{covering_key}_premium_change_pct"))
        return bool(oi_change < -0.005 and prem_change >= prem_floor
                    and str(row.get(f"{covering_key}_flow", "")) == "SHORT_COVERING")

    writers = [r for r in rows if writing_ok(r)]
    covers = [r for r in rows if covering_ok(r)]
    writers.sort(key=lambda r: (abs(number(r.get("strike")) - level), -number(r.get(f"{writing_key}_change_pct"), 0)))
    covers.sort(key=lambda r: (abs(number(r.get("strike")) - level), number(r.get(f"{covering_key}_change_pct"), 0)))
    pair = bool(writers and covers)
    nearest_side = "put" if direction == "BULLISH" else "call"
    contra_flow = False
    for row in rows:
        strike = number(row.get("strike"))
        if abs(strike - level) > step + 0.01:
            continue
        flow = str(row.get(f"{nearest_side}_flow", ""))
        if direction == "BULLISH" and flow == "LONG_BUILDUP_BUYING":
            contra_flow = True
        elif direction == "BEARISH" and flow == "LONG_BUILDUP_BUYING":
            contra_flow = True
    return {"pair_confirmed": pair,
            "writing_leg": ({"strike": number(writers[0].get("strike")),
                             "oi_change_pct": round(100 * number(writers[0].get(f"{writing_key}_change_pct")), 3),
                             "premium_change_pct": round(100 * number(writers[0].get(f"{writing_key}_premium_change_pct")), 3)} if writers else None),
            "covering_leg": ({"strike": number(covers[0].get("strike")),
                              "oi_change_pct": round(100 * number(covers[0].get(f"{covering_key}_change_pct")), 3),
                              "premium_change_pct": round(100 * number(covers[0].get(f"{covering_key}_premium_change_pct")), 3)} if covers else None),
            "score": (20.0 if pair else 10.0 if writers else 0.0) - (8.0 if contra_flow else 0.0),
            "contra_flow": contra_flow}


def resolve_pending_structure_watch(state: dict[str, Any], fresh: Signal, indicators: Indicators,
                                   now: datetime) -> tuple[Signal, dict[str, Any]]:
    """Carry a recent level-reaction hypothesis across scans while price remains valid."""
    watch = state.get("pending_structure_setup")
    if not isinstance(watch, Mapping):
        return fresh, {"status": "NONE"}
    created = parse_dt(watch.get("first_seen"))
    level = number(watch.get("level"))
    direction = str(watch.get("direction", "")).upper()
    setup = str(watch.get("setup", "")).upper()
    if not created or not finite(level) or direction not in {"BULLISH", "BEARISH"}:
        state.pop("pending_structure_setup", None)
        return fresh, {"status": "DISCARDED", "reason": "INVALID_WATCH_SCHEMA"}
    age_minutes = (now.astimezone(IST) - created.astimezone(IST)).total_seconds() / 60.0
    distance = abs(indicators.spot - level)
    max_extension = max(STRUCTURE_WATCH_MAX_EXTENSION_ATR * indicators.atr, 45.0)
    buffer = max(0.25 * indicators.atr, 10.0)
    invalidated = (indicators.spot < level - buffer if direction == "BULLISH" else indicators.spot > level + buffer)
    expired = age_minutes > STRUCTURE_WATCH_TTL_MINUTES
    extended = distance > max_extension
    opposite_fresh = fresh.direction in {"BULLISH", "BEARISH"} and fresh.direction != direction
    same_fresh = fresh.direction == direction and finite(fresh.level) and abs(number(fresh.level) - level) <= max(0.8 * indicators.atr, 30.0)
    if expired or extended or invalidated or opposite_fresh:
        state.pop("pending_structure_setup", None)
        reasons = []
        if expired: reasons.append("TTL_EXPIRED")
        if extended: reasons.append("PRICE_EXTENDED_FROM_WATCH_LEVEL")
        if invalidated: reasons.append("WATCH_LEVEL_INVALIDATED")
        if opposite_fresh: reasons.append("OPPOSITE_STRUCTURAL_SETUP_DETECTED")
        return fresh, {"status": "DISCARDED", "reason": ";".join(reasons), "age_minutes": round(age_minutes, 2),
                       "distance_from_level": round(distance, 2)}
    if fresh.direction == direction and same_fresh:
        return fresh, {"status": "CURRENT_SETUP_CONFIRMS_WATCH", "age_minutes": round(age_minutes, 2),
                       "distance_from_level": round(distance, 2), "level": level}
    if fresh.direction == "NEUTRAL":
        evidence = list(watch.get("evidence", [])) if isinstance(watch.get("evidence"), list) else []
        evidence += ["PERSISTED_STRUCTURE_WATCH_REVALIDATED", f"WATCH_AGE_MINUTES_{age_minutes:.1f}"]
        restored = Signal(direction, setup, round(number(watch.get("score"), 68.0), 1),
                          round(clamp(number(watch.get("score"), 68.0), 0.0, 92.0), 1),
                          "Persisted level-reaction hypothesis; current OI and risk gates must requalify.",
                          level, tuple(dict.fromkeys(evidence)), ())
        return restored, {"status": "REACTIVATED", "age_minutes": round(age_minutes, 2),
                          "distance_from_level": round(distance, 2), "level": level}
    return fresh, {"status": "WATCH_RETAINED_BUT_FRESH_SIGNAL_USED", "age_minutes": round(age_minutes, 2)}


def persist_structure_watch(state: dict[str, Any], signal: Signal, now: datetime,
                            local_oi: Mapping[str, Any]) -> dict[str, Any]:
    """Persist only a price-action setup, never an authorization or pseudo-selection."""
    watchable = {"SUPPORT_CLUSTER_RECLAIM", "RESISTANCE_CLUSTER_REJECTION",
                 "SUPPORT_BOUNCE", "RESISTANCE_REJECTION"}
    if signal.direction not in {"BULLISH", "BEARISH"} or signal.setup not in watchable or not finite(signal.level):
        return {"status": "NOT_WATCHABLE"}
    prior = state.get("pending_structure_setup")
    prior_created = parse_dt(prior.get("first_seen")) if isinstance(prior, Mapping) else None
    similar = bool(isinstance(prior, Mapping) and str(prior.get("direction")) == signal.direction
                   and abs(number(prior.get("level"), -1e9) - signal.level) <= 30.0
                   and prior_created and (now.astimezone(IST) - prior_created.astimezone(IST)).total_seconds() / 60.0 <= STRUCTURE_WATCH_TTL_MINUTES)
    first_seen = prior.get("first_seen") if similar else now.isoformat()
    watch = {"status": "WAITING_FOR_LOCAL_OI_OR_FINAL_GATES",
             "direction": signal.direction, "setup": signal.setup, "level": round(float(signal.level), 2),
             "first_seen": first_seen, "last_seen": now.isoformat(),
             "score": round(float(signal.score), 1), "evidence": list(signal.evidence)[:12],
             "local_oi_qualified_at_last_scan": bool(local_oi.get("qualified")),
             "local_oi_reason_at_last_scan": str(local_oi.get("reason", "")),
             "expires_after_minutes": STRUCTURE_WATCH_TTL_MINUTES,
             "source_version": VERSION}
    state["pending_structure_setup"] = watch
    return {"status": "UPDATED" if similar else "CREATED", "direction": watch["direction"],
            "setup": watch["setup"], "level": watch["level"], "first_seen": first_seen,
            "oi_qualified": watch["local_oi_qualified_at_last_scan"]}


def update_directional_watch(state: dict[str, Any], frame: pd.DataFrame, indicators: Indicators,
                              regime: Mapping[str, Any], oi_first: Mapping[str, Any], now: datetime) -> dict[str, Any]:
    """Maintain a price-only hypothesis across scans; this state never authorizes an entry by itself."""
    bars = completed_candles(frame, now.astimezone(IST))
    current = now.astimezone(IST)
    existing = state.get("directional_watch") if isinstance(state.get("directional_watch"), Mapping) else {}
    direction = "NEUTRAL"
    regime_name = str(regime.get("regime", "TRANSITION")).upper()
    if regime_name == "TREND_BULLISH":
        direction = "BULLISH"
    elif regime_name == "TREND_BEARISH":
        direction = "BEARISH"
    elif indicators.momentum_3m > 0.00025 and indicators.momentum_1m >= -0.00015:
        direction = "BULLISH"
    elif indicators.momentum_3m < -0.00025 and indicators.momentum_1m <= 0.00015:
        direction = "BEARISH"

    if len(bars) < 3 or direction == "NEUTRAL":
        if existing:
            first = parse_dt(existing.get("first_seen"))
            age = (current - first.astimezone(IST)).total_seconds() / 60.0 if first else 999.0
            if age > 15.0:
                state.pop("directional_watch", None)
                return {"status": "EXPIRED", "reason": "NO_DIRECTIONAL_CONFIRMATION_WITHIN_15_MINUTES"}
            return {"status": "RETAINED", "direction": existing.get("direction"), "reason": "CURRENT_SCAN_HAS_NO_NEW_DIRECTIONAL_CONFIRMATION"}
        return {"status": "NONE", "reason": "INSUFFICIENT_DIRECTIONAL_EVIDENCE"}

    closes = bars["close"].astype(float).to_numpy()
    recent_move = float(closes[-1] - closes[-4]) if len(closes) >= 4 else float(closes[-1] - closes[0])
    aligned = (indicators.momentum_3m > 0 and indicators.momentum_1m >= -0.00015
               if direction == "BULLISH" else
               indicators.momentum_3m < 0 and indicators.momentum_1m <= 0.00015)
    recent_price_confirmation = (recent_move >= max(0.15 * indicators.atr, 3.0) if direction == "BULLISH"
                                 else recent_move <= -max(0.15 * indicators.atr, 3.0))
    if not aligned or not recent_price_confirmation:
        return {"status": "RETAINED" if existing else "NO_TRIGGER", "direction": existing.get("direction"),
                "reason": "MOMENTUM_OR_RECENT_PRICE_MOVE_NOT_CONFIRMED", "current_regime": regime_name}

    first_seen = parse_dt(existing.get("first_seen")) if existing else None
    same = bool(existing and str(existing.get("direction", "")).upper() == direction and first_seen
                and (current - first_seen.astimezone(IST)).total_seconds() <= 15 * 60)
    if existing and not same and str(existing.get("direction", "")).upper() != direction:
        old_opposite_count = int(number(existing.get("opposite_direction_observations"), 0)) + 1
        # Avoid flipping the persisted directional hypothesis on a single three-minute counter-move.
        if old_opposite_count < 2:
            retained = dict(existing)
            retained.update({"opposite_direction_observations": old_opposite_count,
                             "last_opposite_observation": current.isoformat()})
            state["directional_watch"] = retained
            return {"status": "OPPOSITE_DIRECTION_PENDING_CONFIRMATION", "direction": retained.get("direction"),
                    "candidate_direction": direction, "observations": old_opposite_count}
        first_seen = None
    if not same:
        first_seen = current
    watch = {"status": "PRICE_SETUP_DEVELOPING", "direction": direction,
             "first_seen": first_seen.isoformat() if first_seen else current.isoformat(),
             "last_seen": current.isoformat(), "last_spot": round(indicators.spot, 2),
             "regime": regime_name, "regime_reason": regime.get("reason"),
             "momentum_1m": indicators.momentum_1m, "momentum_3m": indicators.momentum_3m,
             "recent_move_points": round(recent_move, 2), "oi_confirmed_this_scan": bool(oi_first.get("qualified")),
             "oi_reason": oi_first.get("reason"), "source": "PRICE_CONTEXT_ONLY_NOT_ENTRY_AUTHORIZATION",
             "opposite_direction_observations": 0}
    state["directional_watch"] = watch
    return {"status": "UPDATED" if same else "CREATED", **watch}


def _fib_price_levels(fib: Optional[Mapping[str, Any]]) -> list[float]:
    """Return only actual Fib price values from the current confirmed legs/zones."""
    if not isinstance(fib, Mapping) or not fib.get("available"):
        return []
    values: list[float] = []
    def add(value: Any) -> None:
        x = number(value)
        if finite(x) and x > 0 and not any(abs(x - old) < 0.5 for old in values):
            values.append(float(x))
    for zone_key in ("bullish_support_zone", "bearish_resistance_levels"):
        zone = fib.get(zone_key)
        if isinstance(zone, Mapping):
            for key, val in zone.items():
                if key not in {"zone_low", "zone_high", "fib_78_6_invalidation_reference"} and not isinstance(val, Mapping):
                    add(val)
            add(zone.get("zone_low")); add(zone.get("zone_high"))
    for leg_key in ("up_leg", "down_leg"):
        leg = fib.get(leg_key)
        if not isinstance(leg, Mapping):
            continue
        add(leg.get("high")); add(leg.get("low"))
        for subkey in ("retracements", "extensions"):
            child = leg.get(subkey)
            if isinstance(child, Mapping):
                for value in child.values():
                    add(value)
    return values


def _material_fib_price_levels(fib: Optional[Mapping[str, Any]], atr: float) -> list[float]:
    """Return Fib levels from material swing legs only, avoiding dense levels from noise legs.

    A leg must span at least max(1.25 ATR, 35 NIFTY points). This filter is used for
    continuation distance checks only; reversal and breakout confluence retain their specific
    prescribed Fib levels.
    """
    if not isinstance(fib, Mapping):
        return []
    minimum_range = max(1.25 * number(atr, 0.0), 35.0)
    values: list[float] = []
    def add(value: Any) -> None:
        price = number(value)
        if finite(price) and price > 0 and not any(abs(price - old) < 0.5 for old in values):
            values.append(float(price))
    for key in ("up_leg", "down_leg"):
        leg = fib.get(key)
        if not isinstance(leg, Mapping) or number(leg.get("range_points"), 0.0) < minimum_range:
            continue
        add(leg.get("high")); add(leg.get("low"))
        for subkey in ("retracements", "extensions"):
            levels = leg.get(subkey)
            if isinstance(levels, Mapping):
                for price in levels.values():
                    add(price)
    return values


def continuation_price_extension_guard(frame: pd.DataFrame, indicators: Indicators, spot: float,
                                       now: datetime, direction: str) -> dict[str, Any]:
    """Reject continuous-trend entries after a runaway move, using completed bars only."""
    bars = completed_candles(frame, now.astimezone(IST)).tail(48)
    side = str(direction).upper()
    unavailable = {"qualified": False, "reason": "CONTINUATION_EXTENSION_CHECK_UNAVAILABLE", "bars": len(bars)}
    if side not in {"BULLISH", "BEARISH"} or len(bars) < 20 or not finite(spot) or not finite(indicators.atr) or indicators.atr <= 0:
        return unavailable
    close = bars["close"].astype(float)
    fast = float(close.ewm(span=5, adjust=False).mean().iloc[-1])
    slow = float(close.ewm(span=13, adjust=False).mean().iloc[-1])
    sign = 1.0 if side == "BULLISH" else -1.0
    fast_extension = max(0.0, sign * (float(spot) - fast))
    slow_extension = max(0.0, sign * (float(spot) - slow))
    three_bar_move = sign * float(close.iloc[-1] - close.iloc[-4]) if len(close) >= 4 else float("inf")
    atr = float(indicators.atr)
    fast_limit = max(1.25 * atr, 20.0)
    slow_limit = max(1.80 * atr, 35.0)
    impulse_limit = max(1.75 * atr, 35.0)
    checks = {"not_stretched_from_ema5": fast_extension <= fast_limit,
              "not_stretched_from_ema13": slow_extension <= slow_limit,
              "not_chasing_oversized_three_bar_move": three_bar_move <= impulse_limit}
    failed = [key for key, passed in checks.items() if not passed]
    return {"qualified": not failed,
            "reason": "CONTINUATION_PRICE_EXTENSION_ACCEPTABLE" if not failed else "CONTINUATION_BLOCKED_AS_PRICE_OVEREXTENDED",
            "checks": checks, "failed_checks": failed, "ema5": round(fast, 2), "ema13": round(slow, 2),
            "spot": round(float(spot), 2), "atr": round(atr, 2),
            "directional_extension_from_ema5_points": round(fast_extension, 2),
            "directional_extension_from_ema13_points": round(slow_extension, 2),
            "directional_three_bar_move_points": round(three_bar_move, 2),
            "ema5_extension_limit_points": round(fast_limit, 2),
            "ema13_extension_limit_points": round(slow_limit, 2),
            "three_bar_impulse_limit_points": round(impulse_limit, 2)}


def _fib_touch_tolerance(spot: float) -> float:
    """Use a practical 12–15 point Fib touch zone, capped by the requested 0.15% rule."""
    return max(12.0, min(15.0, 0.0015 * max(0.0, number(spot, 0.0))))


def qualify_oi_first(oi: Mapping[str, Any], spot: float, step: float,
                     min_change_pct: float = 2.5,
                     indicators: Optional[Indicators] = None,
                     regime: Optional[Mapping[str, Any]] = None) -> dict[str, Any]:
    """Qualify same-session local OI flow before allowing a price trigger to authorize entry.

    Two distinct paired-flow signatures are supported:
      * WRITER_COVERING: directional option writing (>2.5% OI growth, premium down) paired
        with opposite-side short covering (OI down, premium up).
      * BUYER_LED_MOMENTUM: directionally dominant option buying (>2.5% OI growth, premium up)
        paired with opposite-side long unwinding (OI down, premium down). This second mode is
        considered only when available price momentum/RSI context confirms the same direction.

    A buyer-led pair is not a blanket replacement for writing confirmation on reversals: it is
    intended for momentum breakouts and continuous-trend entries, where flow and price agree.
    """
    threshold_pct = max(2.5, min(10.0, number(min_change_pct, 2.5)))
    threshold = threshold_pct / 100.0
    empty = {"qualified": False, "reason": "NO_ACTIONABLE_LOCAL_OI_PAIR",
             "threshold_pct_exclusive": threshold_pct, "qualified_directions": [],
             "direction_candidates": {}, "pin_oi_candidate": False, "rows_considered": 0,
             "tactical_available": bool(oi.get("tactical_available")),
             "flow_modes_considered": ["WRITER_COVERING", "BUYER_LED_MOMENTUM"]}
    rows = [r for r in oi.get("walls", []) if isinstance(r, Mapping) and finite(r.get("strike"))
            and abs(number(r.get("strike")) - spot) <= max(4.0 * step, 200.0)]
    empty["rows_considered"] = len(rows)
    atm = round_to_grid(spot, step)
    if not oi.get("tactical_available"):
        return {**empty, "reason": "SAME_SESSION_LOCAL_OI_BASELINE_UNAVAILABLE_OR_STALE"}

    def item(row: Mapping[str, Any], side: str, mode: str, role: str) -> Optional[dict[str, Any]]:
        change = number(row.get(f"{side}_change_pct"))
        prem_change = number(row.get(f"{side}_premium_change_pct"))
        base = number(row.get(f"{side}_prev_oi"))
        old_prem = number(row.get(f"{side}_prev_ltp"))
        new_prem = number(row.get(f"{side}_ltp"))
        delta = number(row.get(f"{side}_delta_oi"))
        current_oi = number(row.get(f"{side}_oi"))
        if not all(finite(x) for x in (change, prem_change, base, old_prem, new_prem, delta, current_oi)):
            return None
        if base < 10000 or current_oi < 0 or min(old_prem, new_prem) < 5:
            return None
        flow = classify_oi_flow(change, prem_change)
        if mode == "WRITER_COVERING":
            if role == "PRIMARY":
                passed = change > threshold and prem_change <= -0.002 and flow == "SHORT_BUILDUP_WRITING"
            else:
                passed = change < -0.005 and prem_change >= 0.002 and flow == "SHORT_COVERING"
        else:
            if role == "PRIMARY":
                passed = change > threshold and prem_change >= 0.002 and flow == "LONG_BUILDUP_BUYING"
            else:
                passed = change < -0.005 and prem_change <= -0.002 and flow == "LONG_UNWINDING"
        if not passed:
            return None
        return {"strike": number(row.get("strike")), "option_side": side.upper(),
                "oi_change_pct": round(change * 100.0, 3), "premium_change_pct": round(prem_change * 100.0, 3),
                "delta_oi": round(delta, 1), "baseline_oi": round(base, 1),
                "current_oi": round(current_oi, 1), "flow": flow}

    def buyer_price_context(direction: str) -> tuple[bool, dict[str, Any]]:
        reg = regime if isinstance(regime, Mapping) else {}
        regime_name = str(reg.get("regime", "TRANSITION")).upper()
        if indicators is None:
            return False, {"reason": "PRICE_CONTEXT_NOT_SUPPLIED_TO_BUYER_LED_GATE", "regime": regime_name}
        m1 = number(getattr(indicators, "momentum_1m", float("nan")))
        m3 = number(getattr(indicators, "momentum_3m", float("nan")))
        rsi = number(getattr(indicators, "rsi", float("nan")))
        last_close = number(getattr(indicators, "last_close", float("nan")))
        prev_close = number(getattr(indicators, "prev_close", float("nan")))
        if direction == "BULLISH":
            aligned = finite(m1) and finite(m3) and m1 > 0 and m3 >= 0.00065
            rsi_aligned = finite(rsi) and rsi >= 55.0
            close_aligned = not (finite(last_close) and finite(prev_close)) or last_close >= prev_close
            regime_aligned = regime_name in {"TREND_BULLISH", "TRANSITION", "WARMUP"} or (
                regime_name == "WHIPSAW" and finite(m1) and finite(m3) and m1 >= 0.00025
                and m3 >= 0.0010 and finite(rsi) and rsi >= 60.0)
        else:
            aligned = finite(m1) and finite(m3) and m1 < 0 and m3 <= -0.00065
            rsi_aligned = finite(rsi) and rsi <= 45.0
            close_aligned = not (finite(last_close) and finite(prev_close)) or last_close <= prev_close
            regime_aligned = regime_name in {"TREND_BEARISH", "TRANSITION", "WARMUP"} or (
                regime_name == "WHIPSAW" and finite(m1) and finite(m3) and m1 <= -0.00025
                and m3 <= -0.0010 and finite(rsi) and rsi <= 40.0)
        ok = bool(aligned and rsi_aligned and close_aligned and regime_aligned)
        return ok, {"direction": direction, "regime": regime_name, "momentum_1m": m1,
                    "momentum_3m": m3, "rsi": rsi, "last_close": last_close,
                    "previous_close": prev_close, "momentum_aligned": bool(aligned),
                    "rsi_aligned": bool(rsi_aligned), "close_aligned": bool(close_aligned),
                    "regime_compatible": bool(regime_aligned), "qualified": ok}

    writer_candidates: dict[str, dict[str, Any]] = {}
    buyer_candidates: dict[str, dict[str, Any]] = {}
    buyer_context: dict[str, Any] = {}
    # Strong writer-led pairs retain priority within each direction. Buyer-led flow is a
    # separate momentum path and is not allowed to masquerade as writing/covering.
    for direction, write_side, cover_side in (("BULLISH", "put", "call"), ("BEARISH", "call", "put")):
        pairs: list[dict[str, Any]] = []
        for wrow in rows:
            primary = item(wrow, write_side, "WRITER_COVERING", "PRIMARY")
            if not primary:
                continue
            wstrike = number(primary.get("strike"))
            if direction == "BULLISH" and wstrike > atm + step + 0.01:
                continue
            if direction == "BEARISH" and wstrike < atm - step - 0.01:
                continue
            for crow in rows:
                secondary = item(crow, cover_side, "WRITER_COVERING", "SECONDARY")
                if not secondary:
                    continue
                cstrike = number(secondary.get("strike"))
                distance = abs(cstrike - wstrike)
                if distance > 2.0 * step + 0.01:
                    continue
                proximity = max(0.0, 1.0 - distance / max(1.0, 2.0 * step))
                score = (number(primary.get("oi_change_pct"), 0.0)
                         + 0.45 * abs(number(secondary.get("oi_change_pct"), 0.0))
                         + 0.15 * abs(number(primary.get("premium_change_pct"), 0.0))
                         + 0.10 * abs(number(secondary.get("premium_change_pct"), 0.0)) + proximity)
                pairs.append({"direction": direction, "flow_mode": "WRITER_COVERING",
                              "primary_flow": primary, "secondary_flow": secondary,
                              "score": round(score, 3), "reference_strikes": sorted({wstrike, cstrike}),
                              "writing_threshold_pct_exclusive": threshold_pct,
                              "pair_distance_points": round(distance, 2)})
        if pairs:
            writer_candidates[direction] = max(pairs, key=lambda x: (number(x.get("score"), 0.0),
                                                                       number(x.get("primary_flow", {}).get("oi_change_pct"), 0.0)))

    # Buyer-led pairs: bullish = call long buildup + put long unwinding; bearish = put long
    # buildup + call long unwinding. Require directional price context before they can authorize.
    for direction, buy_side, unwind_side in (("BULLISH", "call", "put"), ("BEARISH", "put", "call")):
        ctx_ok, ctx = buyer_price_context(direction)
        buyer_context[direction] = ctx
        if not ctx_ok:
            continue
        pairs = []
        for brow in rows:
            primary = item(brow, buy_side, "BUYER_LED_MOMENTUM", "PRIMARY")
            if not primary:
                continue
            bstrike = number(primary.get("strike"))
            # Limit dominant buyer flow to the ATM/near-ATM structure being considered.
            if abs(bstrike - atm) > 2.0 * step + 0.01:
                continue
            for urow in rows:
                secondary = item(urow, unwind_side, "BUYER_LED_MOMENTUM", "SECONDARY")
                if not secondary:
                    continue
                ustrike = number(secondary.get("strike"))
                distance = abs(ustrike - bstrike)
                if distance > 2.0 * step + 0.01:
                    continue
                proximity = max(0.0, 1.0 - distance / max(1.0, 2.0 * step))
                score = (number(primary.get("oi_change_pct"), 0.0)
                         + 0.45 * abs(number(secondary.get("oi_change_pct"), 0.0))
                         + 0.15 * abs(number(primary.get("premium_change_pct"), 0.0))
                         + 0.10 * abs(number(secondary.get("premium_change_pct"), 0.0)) + proximity)
                pairs.append({"direction": direction, "flow_mode": "BUYER_LED_MOMENTUM",
                              "primary_flow": primary, "secondary_flow": secondary,
                              "score": round(score, 3), "reference_strikes": sorted({bstrike, ustrike}),
                              "writing_threshold_pct_exclusive": threshold_pct,
                              "pair_distance_points": round(distance, 2), "price_context": ctx})
        if pairs:
            buyer_candidates[direction] = max(pairs, key=lambda x: (number(x.get("score"), 0.0),
                                                                      number(x.get("primary_flow", {}).get("oi_change_pct"), 0.0)))

    direction_candidates: dict[str, dict[str, Any]] = {}
    for direction in ("BULLISH", "BEARISH"):
        candidate = writer_candidates.get(direction) or buyer_candidates.get(direction)
        if candidate:
            direction_candidates[direction] = candidate

    # Same-strike ATM call+put writing remains a separate non-directional pin candidate.
    pin_row = next((r for r in rows if finite(r.get("strike")) and finite(atm)
                    and abs(number(r.get("strike")) - atm) < 0.5
                    and item(r, "call", "WRITER_COVERING", "PRIMARY")
                    and item(r, "put", "WRITER_COVERING", "PRIMARY")), None)
    pin_oi_candidate = pin_row is not None
    if len(direction_candidates) == 2:
        bull_score = number(direction_candidates["BULLISH"].get("score"), 0.0)
        bear_score = number(direction_candidates["BEARISH"].get("score"), 0.0)
        gap = abs(bull_score - bear_score)
        if gap < max(0.5, 0.12 * max(bull_score, bear_score)):
            return {**empty, "reason": "CONFLICTING_BULLISH_AND_BEARISH_LOCAL_OI_PAIRS",
                    "direction_candidates": direction_candidates, "pin_oi_candidate": pin_oi_candidate,
                    "buyer_price_context": buyer_context}
        dominant = "BULLISH" if bull_score > bear_score else "BEARISH"
        direction_candidates = {dominant: direction_candidates[dominant]}
    if not direction_candidates:
        reason = ("NO_LOCAL_PAIR_WITH_STRICTLY_MORE_THAN_2_5_PERCENT_WRITING_OI"
                  if writer_candidates or not any(ctx.get("qualified") for ctx in buyer_context.values())
                  else "NO_QUALIFYING_DIRECTIONAL_BUYER_LED_PAIR")
        return {**empty, "reason": reason, "pin_oi_candidate": pin_oi_candidate,
                "buyer_price_context": buyer_context,
                "writer_pair_directions": list(writer_candidates), "buyer_pair_directions": list(buyer_candidates)}
    return {**empty, "qualified": True, "reason": "DIRECTIONAL_LOCAL_OI_PAIR_CONFIRMED",
            "qualified_directions": list(direction_candidates.keys()), "direction_candidates": direction_candidates,
            "pin_oi_candidate": pin_oi_candidate, "buyer_price_context": buyer_context,
            "flow_mode": next(iter(direction_candidates.values())).get("flow_mode")}

def score_market_signal(frame: pd.DataFrame, indicators: Indicators, oi: Mapping[str, Any], levels: Sequence[Level],
                        now: datetime, min_score: float, step: float,
                        fib: Optional[Mapping[str, Any]] = None,
                        divergence: Optional[Mapping[str, Any]] = None,
                        regime: Optional[Mapping[str, Any]] = None,
                        oi_first: Optional[Mapping[str, Any]] = None,
                        min_rr: float = 1.25) -> tuple[Signal, dict[str, Any]]:
    """Combine independently computed price structure and paired OI, then rank fully qualified entries."""
    spot, atr = indicators.spot, indicators.atr
    bars = completed_candles(frame, now.astimezone(IST)).tail(180).reset_index(drop=True)
    prefilter = dict(oi_first) if isinstance(oi_first, Mapping) else qualify_oi_first(oi, spot, step, 2.5)
    oi_directions = {str(x).upper() for x in prefilter.get("qualified_directions", [])}
    base_diag = {"threshold": min_score, "decision_model": "INDEPENDENT_PRICE_ANALYSIS_PLUS_WRITER_OR_BUYER_LED_PAIRED_FLOW_THEN_SCENARIO_GATES",
                 "oi_first": safe_json(prefilter), "bullish_candidates": [], "bearish_candidates": []}
    if not prefilter.get("qualified") or not oi_directions:
        reg = regime if isinstance(regime, Mapping) else {}
        watch_direction = str(reg.get("regime", "")).upper()
        if watch_direction not in {"TREND_BULLISH", "TREND_BEARISH"}:
            watch_direction = ("TREND_BULLISH" if indicators.momentum_3m > 0.00025 and indicators.momentum_1m >= -0.00015
                               else "TREND_BEARISH" if indicators.momentum_3m < -0.00025 and indicators.momentum_1m <= 0.00015
                               else "NEUTRAL")
        recent_move = float(bars.iloc[-1]["close"] - bars.iloc[-4]["close"]) if len(bars) >= 4 else 0.0
        base_diag["developing_price_setup"] = {"direction": watch_direction,
            "regime": reg.get("regime"), "momentum_1m": indicators.momentum_1m,
            "momentum_3m": indicators.momentum_3m, "recent_3m_move_points": round(recent_move, 2),
            "price_analysis_performed": True,
            "entry_authorization": "BLOCKED_UNTIL_REQUIRED_LOCAL_OI_PAIR_CONFIRMS"}
        signal = Signal("NEUTRAL", "PRICE_SETUP_TRACKED_AWAITING_OI", 0.0, 0.0,
                        str(prefilter.get("reason", "NO_ACTIONABLE_LOCAL_OI_PAIR")), None,
                        ("PRICE_STRUCTURE_ANALYSED_INDEPENDENTLY", "LOCAL_OI_ENTRY_GATE_NOT_PASSED",
                         str(prefilter.get("reason", "NO_ACTIONABLE_LOCAL_OI_PAIR"))),
                        ("ENTRY_NOT_AUTHORIZED_WITHOUT_REQUIRED_LOCAL_OI_PAIR",))
        return signal, base_diag
    if bars.empty or not finite(spot) or not finite(atr) or atr <= 0:
        signal = Signal("NEUTRAL", "NO_USABLE_PRICE_STRUCTURE", 0.0, 0.0,
                        "No usable completed-candle structure.", None,
                        ("NO_USABLE_PRICE_STRUCTURE",), ("PRICE_DATA_UNAVAILABLE",))
        return signal, base_diag

    last_close = number(bars.iloc[-1]["close"])
    previous_close = number(bars.iloc[-2]["close"]) if len(bars) > 1 else last_close
    closes = bars["close"].astype(float).to_numpy(dtype=float)
    touch_tolerance = _fib_touch_tolerance(spot)
    level_near = max(1.8 * atr, 65.0)
    entry_near = max(1.25 * atr, 45.0)
    break_buffer = max(2.0, 0.08 * atr)
    fib_map = fib if isinstance(fib, Mapping) else {}
    div = divergence if isinstance(divergence, Mapping) else {}
    bull_div = div.get("bullish") if isinstance(div.get("bullish"), Mapping) else None
    bear_div = div.get("bearish") if isinstance(div.get("bearish"), Mapping) else None
    reg = regime if isinstance(regime, Mapping) else {}
    regime_name = str(reg.get("regime", "TRANSITION")).upper()
    session_bias = str(reg.get("session_bias", "UNKNOWN")).upper()
    all_fib = _fib_price_levels(fib_map)
    bull_fib = fib_map.get("bullish_support_zone") if isinstance(fib_map.get("bullish_support_zone"), Mapping) else {}
    bear_fib = fib_map.get("bearish_resistance_levels") if isinstance(fib_map.get("bearish_resistance_levels"), Mapping) else {}
    bull_reversal_fibs = [number(bull_fib.get(k)) for k in ("fib_50", "fib_61_8")]
    bull_reversal_fibs = [x for x in bull_reversal_fibs if finite(x)]
    bear_reversal_fibs = [number(bear_fib.get(k)) for k in ("fib_61_8", "fib_100")]
    bear_reversal_fibs = [x for x in bear_reversal_fibs if finite(x)]
    bull_break_fibs = [number(bear_fib.get(k)) for k in ("fib_50", "fib_61_8", "fib_100")]
    bull_break_fibs = [x for x in bull_break_fibs if finite(x)]
    bear_break_fibs = [number(bull_fib.get(k)) for k in ("fib_50", "fib_61_8", "fib_78_6_invalidation_reference")]
    bear_break_fibs = [x for x in bear_break_fibs if finite(x)]
    # Add recently crossed Fib boundaries even if the level builder omits a Fib now far behind spot.
    scan_levels = list(levels)
    for val in bull_break_fibs:
        if val < spot - 0.5 and spot - val <= max(3.0 * atr, 150.0) and not any(abs(l.price-val) <= touch_tolerance for l in scan_levels):
            scan_levels.append(Level(float(val), "RESISTANCE", "FIB_BREAKOUT_BOUNDARY", 0.70, 1))
    for val in bear_break_fibs:
        if val > spot + 0.5 and val - spot <= max(3.0 * atr, 150.0) and not any(abs(l.price-val) <= touch_tolerance for l in scan_levels):
            scan_levels.append(Level(float(val), "SUPPORT", "FIB_BREAKDOWN_BOUNDARY", 0.70, 1))

    def flow_mode_for(direction: str) -> str:
        pairs = prefilter.get("direction_candidates", {}) if isinstance(prefilter.get("direction_candidates"), Mapping) else {}
        pair = pairs.get(direction, {}) if isinstance(pairs, Mapping) else {}
        return str(pair.get("flow_mode", "WRITER_COVERING")).upper() if isinstance(pair, Mapping) else "WRITER_COVERING"

    def evidence_for(direction: str) -> list[str]:
        pair = prefilter.get("direction_candidates", {}).get(direction, {}) if isinstance(prefilter.get("direction_candidates"), Mapping) else {}
        primary = pair.get("primary_flow", {}) if isinstance(pair, Mapping) else {}
        secondary = pair.get("secondary_flow", {}) if isinstance(pair, Mapping) else {}
        mode = flow_mode_for(direction)
        if mode == "BUYER_LED_MOMENTUM":
            return ["OI_FLOW_MODE_BUYER_LED", "BUYER_LED_DIRECTIONAL_OI_PAIR_CONFIRMED",
                    f"BUYING_LEG_{primary.get('option_side','UNKNOWN')}_OI_CHANGE_{primary.get('oi_change_pct','NA')}PCT",
                    f"UNWINDING_LEG_{secondary.get('option_side','UNKNOWN')}_OI_CHANGE_{secondary.get('oi_change_pct','NA')}PCT"]
        return ["OI_FLOW_MODE_WRITER_COVERING", "OI_FIRST_DIRECTIONAL_PAIR_CONFIRMED",
                f"WRITING_LEG_{primary.get('option_side','UNKNOWN')}_OI_CHANGE_{primary.get('oi_change_pct','NA')}PCT",
                f"COVERING_LEG_{secondary.get('option_side','UNKNOWN')}_OI_CHANGE_{secondary.get('oi_change_pct','NA')}PCT"]

    candidates: list[dict[str, Any]] = []
    diagnostic_candidates: dict[str, list[dict[str, Any]]] = {"BULLISH": [], "BEARISH": []}
    candidate_oi_checks: dict[str, dict[str, Any]] = {}
    candidate_oi_failures: list[dict[str, Any]] = []

    def local_candidate_gate(direction: str, setup: str, level_value: float) -> bool:
        key = f"{direction}|{setup}|{round(number(level_value), 2):.2f}"
        if key not in candidate_oi_checks:
            mode_evidence = ("OI_FLOW_MODE_BUYER_LED",) if flow_mode_for(direction) == "BUYER_LED_MOMENTUM" else ("OI_FLOW_MODE_WRITER_COVERING",)
            proposed = Signal(direction, setup, 0.0, 0.0, "CANDIDATE_OI_PREFILTER", float(level_value), mode_evidence)
            gate = qualify_local_oi(oi, proposed, spot, step, 2.5)
            candidate_oi_checks[key] = {"qualified": bool(gate.get("qualified")), "reason": gate.get("reason"),
                                        "flow_mode": gate.get("flow_mode"),
                                        "pair_distance_points": gate.get("pair_distance_points"),
                                        "reference_strikes": gate.get("reference_strikes"),
                                        "primary_flow": ({k: gate["primary_flow"].get(k) for k in ("strike", "option_side", "oi_change_pct", "premium_change_pct", "flow")}
                                                         if isinstance(gate.get("primary_flow"), Mapping) else None),
                                        "secondary_flow": ({k: gate["secondary_flow"].get(k) for k in ("strike", "option_side", "oi_change_pct", "premium_change_pct", "flow")}
                                                           if isinstance(gate.get("secondary_flow"), Mapping) else None),
                                        "primary_oi_change_pct": number((gate.get("primary_flow") or {}).get("oi_change_pct"), None),
                                        "secondary_oi_change_pct": number((gate.get("secondary_flow") or {}).get("oi_change_pct"), None)}
            if not gate.get("qualified") and len(candidate_oi_failures) < 25:
                candidate_oi_failures.append({"candidate": key, "reason": gate.get("reason")})
        return bool(candidate_oi_checks[key].get("qualified"))

    for level in scan_levels:
        if not finite(level.price):
            continue
        dist = abs(spot - level.price)
        stat = _level_touch_stats(frame, level.price, level.kind, atr, now) if level.kind in {"SUPPORT", "RESISTANCE"} else {}
        touches = min(8, max(int(stat.get("touches", 0)), int(level.touches) if finite(level.touches) else 1))
        recent_touch = bool(stat.get("recent_touch"))
        # OI gates for all relevant setup families are resolved before trigger-specific price tests.
        bull_support_oi = local_candidate_gate("BULLISH", "SUPPORT_BOUNCE", level.price) if level.kind == "SUPPORT" and "BULLISH" in oi_directions else False
        bull_break_oi = local_candidate_gate("BULLISH", "CONFIRMED_BREAKOUT", level.price) if level.kind == "RESISTANCE" and "BULLISH" in oi_directions else False
        bear_resistance_oi = local_candidate_gate("BEARISH", "RESISTANCE_REJECTION", level.price) if level.kind == "RESISTANCE" and "BEARISH" in oi_directions else False
        bear_break_oi = local_candidate_gate("BEARISH", "CONFIRMED_BREAKDOWN", level.price) if level.kind == "SUPPORT" and "BEARISH" in oi_directions else False
        if "BULLISH" in oi_directions:
            # Scenario 1: bullish reversal requires a Fib 50/61.8 touch and confirmed bullish RSI divergence.
            if level.kind == "SUPPORT" and bull_support_oi and dist <= level_near and bull_div and bull_reversal_fibs:
                fib_distance = min(min(abs(x-level.price), abs(x-spot)) for x in bull_reversal_fibs)
                touch_near = recent_touch or (touches >= 3 and dist <= max(0.8*atr, 35.0))
                reclaimed = (last_close > level.price + max(1.5, 0.05*atr)
                             and spot >= level.price - max(0.25*atr, 10.0)
                             and (indicators.momentum_1m > -0.00015 or last_close >= previous_close))
                if fib_distance <= touch_tolerance and touches >= 2 and touch_near and reclaimed and dist <= entry_near:
                    raw = 69.5 + min(touches, 5)*1.6 + (3.0 if recent_touch else 0.0)
                    raw += min(6.0, max(0.0, indicators.momentum_1m*1000.0))
                    ev = evidence_for("BULLISH") + [f"FIB_SUPPORT_TOUCH_WITHIN_{touch_tolerance:.1f}_POINTS",
                            "CONFIRMED_BULLISH_RSI_DIVERGENCE", f"PERSISTENT_SUPPORT_TESTS_{touches}",
                            f"SUPPORT_RECLAIMED_{level.price:.2f}"]
                    cand = {"direction":"BULLISH","setup":"SUPPORT_BOUNCE","level":level.price,"score":raw,
                            "evidence":ev,"distance":dist,"touches":touches}
                    candidates.append(cand); diagnostic_candidates["BULLISH"].append(cand)

            # Scenario 3: confirmed breakout. Writer-led flow keeps the two-close rule.
            # A buyer-led pair may use one completed close only with a stronger momentum burst,
            # elevated RSI and spot still near the boundary; this is an explicit early-trigger path.
            if level.kind == "RESISTANCE" and bull_break_oi and level.price < spot and dist <= max(3*atr,150.0):
                fib_boundary = any(abs(level.price-x) <= touch_tolerance for x in bull_break_fibs)
                two_closes = len(closes) >= 2 and closes[-1] > level.price + break_buffer and closes[-2] > level.price + break_buffer
                buyer_mode = flow_mode_for("BULLISH") == "BUYER_LED_MOMENTUM"
                prior_close = float(closes[-2]) if len(closes) >= 2 else float("nan")
                early_buyer_close = bool(buyer_mode and len(closes) >= 2
                    and closes[-1] > level.price + break_buffer
                    and prior_close <= level.price + break_buffer
                    and spot >= level.price - max(0.15 * atr, 3.0)
                    and indicators.momentum_1m > 0.00015 and indicators.momentum_3m >= 0.00065
                    and finite(indicators.rsi) and indicators.rsi >= 60.0)
                close_confirmed = two_closes or early_buyer_close
                expanding = (indicators.momentum_1m > 0 and indicators.momentum_3m > 0
                             and (len(closes) < 7 or (closes[-1]/closes[-4]-1.0) > (closes[-4]/closes[-7]-1.0)))
                follow_through = last_close > previous_close and indicators.momentum_1m > 0 and indicators.momentum_3m > 0
                opposing = div.get("bearish") if isinstance(div.get("bearish"), Mapping) else None
                opp_price = number((opposing or {}).get("price_high_2"))
                opp_near = bool(opposing and finite(opp_price) and abs(opp_price-level.price) <= max(atr,45.0))
                spot_boundary_ok = spot > level.price + break_buffer or (early_buyer_close and spot >= level.price - max(0.15*atr,3.0))
                if (fib_boundary and close_confirmed and spot_boundary_ok and finite(indicators.rsi)
                        and indicators.rsi >= 55.0 and (expanding or follow_through)):
                    if not opp_near:
                        raw = (76.0 if early_buyer_close and not two_closes else 74.0)
                        raw += (3.0 if expanding else 0.0) + min(6.0, max(0.0,(indicators.rsi-55.0)*0.25))
                        trigger_evidence = ([f"TWO_COMPLETED_CLOSES_ABOVE_FIB_RESISTANCE_{level.price:.2f}"] if two_closes
                                            else [f"BUYER_LED_EARLY_SINGLE_CLOSE_BREAKOUT_{level.price:.2f}",
                                                  "EARLY_TRIGGER_REQUIRES_MOMENTUM_1M_3M_AND_RSI_60"])
                        ev = evidence_for("BULLISH") + trigger_evidence + [
                            "RSI_AT_LEAST_55", "1M_3M_MOMENTUM_ALIGNED", "NO_CONFIRMED_OPPOSING_DIVERGENCE_NEAR_TRIGGER"]
                        cand = {"direction":"BULLISH","setup":"CONFIRMED_BREAKOUT","level":level.price,"score":raw,
                                "evidence":ev,"distance":dist,"touches":touches,
                                "early_buyer_led_trigger":bool(early_buyer_close and not two_closes)}
                        candidates.append(cand); diagnostic_candidates["BULLISH"].append(cand)

        if "BEARISH" in oi_directions:
            # Scenario 2: bearish reversal requires Fib 61.8/100 touch and confirmed bearish RSI divergence.
            if level.kind == "RESISTANCE" and bear_resistance_oi and dist <= level_near and bear_div and bear_reversal_fibs:
                fib_distance = min(min(abs(x-level.price), abs(x-spot)) for x in bear_reversal_fibs)
                touch_near = recent_touch or (touches >= 3 and dist <= max(0.8*atr,35.0))
                rejected = (last_close < level.price - max(1.5,0.05*atr)
                            and spot <= level.price + max(0.25*atr,10.0)
                            and (indicators.momentum_1m < 0.00015 or last_close <= previous_close))
                if fib_distance <= touch_tolerance and touches >= 2 and touch_near and rejected and dist <= entry_near:
                    raw = 69.5 + min(touches,5)*1.6 + (3.0 if recent_touch else 0.0)
                    raw += min(6.0, max(0.0,-indicators.momentum_1m*1000.0))
                    ev = evidence_for("BEARISH") + [f"FIB_RESISTANCE_TOUCH_WITHIN_{touch_tolerance:.1f}_POINTS",
                        "CONFIRMED_BEARISH_RSI_DIVERGENCE", f"PERSISTENT_RESISTANCE_TESTS_{touches}",
                        f"RESISTANCE_REJECTED_{level.price:.2f}"]
                    cand={"direction":"BEARISH","setup":"RESISTANCE_REJECTION","level":level.price,"score":raw,
                          "evidence":ev,"distance":dist,"touches":touches}
                    candidates.append(cand); diagnostic_candidates["BEARISH"].append(cand)

            # Scenario 4: confirmed breakdown. Buyer-led put accumulation can use a single
            # decisive close only when bearish momentum and RSI are notably strong.
            if level.kind == "SUPPORT" and bear_break_oi and level.price > spot and dist <= max(3*atr,150.0):
                fib_boundary = any(abs(level.price-x) <= touch_tolerance for x in bear_break_fibs)
                two_closes = len(closes) >= 2 and closes[-1] < level.price - break_buffer and closes[-2] < level.price - break_buffer
                buyer_mode = flow_mode_for("BEARISH") == "BUYER_LED_MOMENTUM"
                prior_close = float(closes[-2]) if len(closes) >= 2 else float("nan")
                early_buyer_close = bool(buyer_mode and len(closes) >= 2
                    and closes[-1] < level.price - break_buffer
                    and prior_close >= level.price - break_buffer
                    and spot <= level.price + max(0.15 * atr, 3.0)
                    and indicators.momentum_1m < -0.00015 and indicators.momentum_3m <= -0.00065
                    and finite(indicators.rsi) and indicators.rsi <= 40.0)
                close_confirmed = two_closes or early_buyer_close
                expanding = (indicators.momentum_1m < 0 and indicators.momentum_3m < 0
                             and (len(closes) < 7 or (closes[-1]/closes[-4]-1.0) < (closes[-4]/closes[-7]-1.0)))
                follow_through = last_close < previous_close and indicators.momentum_1m < 0 and indicators.momentum_3m < 0
                opposing = div.get("bullish") if isinstance(div.get("bullish"), Mapping) else None
                opp_price = number((opposing or {}).get("price_low_2"))
                opp_near = bool(opposing and finite(opp_price) and abs(opp_price-level.price) <= max(atr,45.0))
                spot_boundary_ok = spot < level.price - break_buffer or (early_buyer_close and spot <= level.price + max(0.15*atr,3.0))
                ok_break = (fib_boundary and close_confirmed and spot_boundary_ok and finite(indicators.rsi)
                            and indicators.rsi <= 45.0 and (expanding or follow_through))
                if ok_break and not opp_near:
                    raw = (76.0 if early_buyer_close and not two_closes else 74.0)
                    raw += (3.0 if expanding else 0.0) + min(6.0, max(0.0,(45.0-indicators.rsi)*0.25))
                    trigger_evidence = ([f"TWO_COMPLETED_CLOSES_BELOW_FIB_SUPPORT_{level.price:.2f}"] if two_closes
                                        else [f"BUYER_LED_EARLY_SINGLE_CLOSE_BREAKDOWN_{level.price:.2f}",
                                              "EARLY_TRIGGER_REQUIRES_MOMENTUM_1M_3M_AND_RSI_40"])
                    ev=evidence_for("BEARISH")+trigger_evidence+[
                        "RSI_AT_MOST_45","1M_3M_MOMENTUM_ALIGNED","NO_CONFIRMED_OPPOSING_DIVERGENCE_NEAR_TRIGGER"]
                    cand={"direction":"BEARISH","setup":"CONFIRMED_BREAKDOWN","level":level.price,"score":raw,
                          "evidence":ev,"distance":dist,"touches":touches,
                          "early_buyer_led_trigger":bool(early_buyer_close and not two_closes)}
                    candidates.append(cand); diagnostic_candidates["BEARISH"].append(cand)

    # Continuous trend continuation: a strong, fresh OI pair can authorize a trend entry even
    # when price has moved away from a Fib boundary. Extension is recorded as a timing warning;
    # it is not a blanket veto when price structure, momentum and OI are aligned.
    material_fib = _material_fib_price_levels(fib_map, atr)
    nearest_material_fib_dist = min((abs(spot - x) for x in material_fib), default=float("inf"))
    continuation_guard_diagnostics: list[dict[str, Any]] = []
    for direction in oi_directions:
        cont_setup = "CONTINUOUS_BULLISH_TREND" if direction == "BULLISH" else "CONTINUOUS_BEARISH_TREND"
        cont_oi_ok = local_candidate_gate(direction, cont_setup, spot)
        extension_guard = continuation_price_extension_guard(frame, indicators, spot, now, direction)
        continuation_guard_diagnostics.append({"direction": direction, **extension_guard})
        expected_regime = "TREND_BULLISH" if direction == "BULLISH" else "TREND_BEARISH"
        watch = reg.get("directional_watch") if isinstance(reg.get("directional_watch"), Mapping) else {}
        watch_direction = str(watch.get("direction", "")).upper()
        watch_time = parse_dt(watch.get("first_seen"))
        watch_age_seconds = (now.astimezone(IST) - watch_time.astimezone(IST)).total_seconds() if watch_time else float("inf")
        watch_fresh = bool(0.0 <= watch_age_seconds <= 15 * 60)
        persistent_watch_aligned = watch_direction == direction and watch_fresh
        regime_aligned = regime_name == expected_regime or (regime_name in {"TRANSITION", "WARMUP"} and persistent_watch_aligned)
        momentum_aligned = ((direction == "BULLISH" and indicators.momentum_3m > 0.00015 and indicators.momentum_1m >= -0.00015)
                            or (direction == "BEARISH" and indicators.momentum_3m < -0.00015 and indicators.momentum_1m <= 0.00015))
        if len(closes) >= 4:
            recent_move = float(closes[-1] - closes[-4])
            last_close_active = (closes[-1] >= closes[-2] if direction == "BULLISH" else closes[-1] <= closes[-2])
            directional_bars = np.diff(closes[-4:])
            directional_count = int(np.sum(directional_bars > 0)) if direction == "BULLISH" else int(np.sum(directional_bars < 0))
            recent_trigger = ((recent_move >= max(0.15 * atr, 3.0) and (last_close_active or directional_count >= 2))
                              if direction == "BULLISH" else
                              (recent_move <= -max(0.15 * atr, 3.0) and (last_close_active or directional_count >= 2)))
        else:
            recent_move = 0.0
            recent_trigger = False
        opposing_div = (div.get("bearish") if direction == "BULLISH" else div.get("bullish"))
        opp_price = number((opposing_div or {}).get("price_high_2" if direction == "BULLISH" else "price_low_2")) if isinstance(opposing_div, Mapping) else float("nan")
        opposing_near = bool(isinstance(opposing_div, Mapping) and finite(opp_price) and abs(opp_price - spot) <= max(atr, 45.0))
        pair = prefilter.get("direction_candidates", {}).get(direction, {}) if isinstance(prefilter.get("direction_candidates"), Mapping) else {}
        primary = pair.get("primary_flow", {}) if isinstance(pair, Mapping) else {}
        writer_pct = number(primary.get("oi_change_pct"), 0.0) if isinstance(primary, Mapping) else 0.0
        # Exceptional local writing permits entry through a moderate overextension warning; extreme
        # extension with only marginally qualifying flow still waits for a retest.
        fast_ext = number(extension_guard.get("directional_extension_from_ema5_points"), 0.0)
        slow_ext = number(extension_guard.get("directional_extension_from_ema13_points"), 0.0)
        impulse_ext = number(extension_guard.get("directional_three_bar_move_points"), 0.0)
        extreme_extension = (fast_ext > max(2.75 * atr, 75.0) and slow_ext > max(3.5 * atr, 90.0)
                             and impulse_ext > max(3.25 * atr, 85.0))
        extension_ok = not extreme_extension or writer_pct >= 8.0
        opposing_div_ok = not opposing_near or (writer_pct >= 8.0 and momentum_aligned)
        if cont_oi_ok and regime_aligned and momentum_aligned and recent_trigger and extension_ok and opposing_div_ok:
            score = 76.0 + min(10.0, max(0.0, (writer_pct - 2.5) * 0.35))
            if not extension_guard.get("qualified"):
                score -= 2.5
            if opposing_near:
                score -= 2.0
            evidence = evidence_for(direction) + ["PERSISTENT_TREND_CONTINUATION_TRIGGER",
                "DIRECTIONAL_1M_3M_MOMENTUM_CONFIRMED", "LOCAL_OI_PAIR_STRICTLY_ABOVE_2_5_PERCENT",
                "FIB_PROXIMITY_IS_CONTEXT_NOT_GLOBAL_VETO", "ATR_1_5_TRAILING_STOP"]
            if not extension_guard.get("qualified"):
                evidence.append("EXTENSION_WARNING_RETAINED_FOR_RISK_REVIEW")
            if opposing_near:
                evidence.append("OPPOSING_DIVERGENCE_WARNING_OVERRIDDEN_BY_STRONG_OI_AND_ALIGNED_MOMENTUM")
            candidate = {"direction": direction, "setup": cont_setup, "level": spot, "score": score,
                         "evidence": evidence, "distance": 0.0, "touches": 0,
                         "extension_warning": not bool(extension_guard.get("qualified")),
                         "nearest_material_fib_distance_points": (round(nearest_material_fib_dist, 2)
                                                                  if finite(nearest_material_fib_dist) else None),
                         "recent_directional_move_points": round(recent_move, 2)}
            candidates.append(candidate)
            diagnostic_candidates[direction].append(candidate)
    if not candidates:
        signal=Signal("NEUTRAL","NO_QUALIFYING_OI_CONFIRMED_SCENARIO",0.0,0.0,
                      "OI qualified, but none of the four matrix scenarios or continuous-trend conditions passed.",None,
                      tuple(["OI_FIRST_GATE_PASSED_BUT_NO_PRICE_ACTION_SCENARIO"]),
                      ("NO_FIB_DIVERGENCE_REVERSAL_OR_CONFIRMED_BREAK_OR_CONTINUOUS_TREND",))
        base_diag.update({"bullish_candidates":[{"setup":x["setup"],"level":round(x["level"],2),"score":round(x["score"],1)} for x in diagnostic_candidates["BULLISH"]],
                          "bearish_candidates":[{"setup":x["setup"],"level":round(x["level"],2),"score":round(x["score"],1)} for x in diagnostic_candidates["BEARISH"]],
                          "fib_touch_tolerance_points":touch_tolerance,"candidate_oi_gate_checks":candidate_oi_checks,
                          "candidate_oi_gate_failures":candidate_oi_failures,
                          "continuation_price_extension_guard":continuation_guard_diagnostics,
                          "decision_model":"INDEPENDENT_PRICE_AND_OI_ANALYSIS_THEN_SETUP_SPECIFIC_ENTRY_GATES"})
        return signal, base_diag

    candidates.sort(key=lambda x: (-number(x.get("score"),0.0), number(x.get("distance"),99999), -int(x.get("touches",0))))

    # Qualify each candidate independently before ranking the final decision. This avoids a
    # high-scoring breakout that fails the extension guard suppressing a lower-scoring,
    # fully qualified continuation or range-edge reversal.
    candidate_gate_evaluations: list[dict[str, Any]] = []
    qualified_candidates: list[dict[str, Any]] = []
    for candidate in candidates:
        candidate_score = clamp(number(candidate.get("score"), 0.0), 0.0, 100.0)
        candidate_direction = str(candidate.get("direction", "NEUTRAL")).upper()
        candidate_setup = str(candidate.get("setup", "UNKNOWN")).upper()
        candidate_level = number(candidate.get("level"), float("nan"))
        candidate_evidence = tuple(dict.fromkeys(str(x) for x in candidate.get("evidence", [])))
        candidate_signal = Signal(candidate_direction, candidate_setup, round(candidate_score, 1),
                                  round(clamp(candidate_score, 0.0, 92.0), 1),
                                  "; ".join(candidate_evidence[:8]),
                                  float(candidate_level) if finite(candidate_level) else None,
                                  candidate_evidence, ())
        candidate_oi_gate = qualify_local_oi(oi, candidate_signal, spot, step, 2.5)
        candidate_fib_gate = qualify_fib_divergence(candidate_signal, reg, fib_map, div, spot, atr)
        candidate_setup_gate = qualify_setup_rules(candidate_signal, frame, indicators, reg,
                                                   candidate_fib_gate, candidate_oi_gate, now)
        candidate_regime_gate = qualify_regime(candidate_signal, reg, indicators, spot,
                                               candidate_fib_gate, candidate_oi_gate, candidate_setup_gate)
        candidate_risk = calculate_risk_plan(candidate_signal, levels, indicators, min_rr)
        time_allowed = now.astimezone(IST).time() < ENTRY_CUTOFF
        score_allowed = candidate_score >= min_score
        checks = {
            "score_at_or_above_minimum": score_allowed,
            "local_oi_pair_confirmed": bool(candidate_oi_gate.get("qualified")),
            "fib_divergence_gate_passed": bool(candidate_fib_gate.get("qualified")),
            "setup_execution_gate_passed": bool(candidate_setup_gate.get("qualified")),
            "market_regime_gate_passed": bool(candidate_regime_gate.get("qualified")),
            "structural_risk_plan_valid": bool(candidate_risk.valid),
            "before_entry_cutoff": time_allowed,
        }
        failed = [name for name, passed in checks.items() if not passed]
        evaluation = {
            "direction": candidate_direction, "setup": candidate_setup,
            "level": round(candidate_level, 2) if finite(candidate_level) else None,
            "score": round(candidate_score, 1), "distance_points": round(number(candidate.get("distance"), 0.0), 2),
            "touches": int(candidate.get("touches", 0)), "qualified": not failed,
            "checks": checks, "failed_checks": failed,
            "local_oi_reason": candidate_oi_gate.get("reason"),
            "local_oi_pair": candidate_oi_gate.get("paired_flow"),
            "fib_reason": candidate_fib_gate.get("reason"),
            "setup_reason": candidate_setup_gate.get("reason"),
            "setup_failed_checks": candidate_setup_gate.get("failed_checks", []),
            "regime_reason": candidate_regime_gate.get("reason"),
            "risk_valid": bool(candidate_risk.valid), "risk_reason": candidate_risk.reason,
            "risk_plan": safe_json(asdict(candidate_risk)),
        }
        candidate_gate_evaluations.append(evaluation)
        if not failed:
            qualified_candidates.append({**candidate, "_preflight": evaluation})

    base_diag.update({
        "candidate_gate_evaluations": candidate_gate_evaluations,
        "generated_candidate_count": len(candidates),
        "fully_qualified_candidate_count": len(qualified_candidates),
        "candidate_selection_policy": "HIGHEST_SCORE_AMONG_CANDIDATES_PASSING_OI_FIB_SETUP_REGIME_RISK_AND_TIME_GATES",
    })
    if not qualified_candidates:
        first_failures = []
        for evaluation in candidate_gate_evaluations:
            for failure in evaluation.get("failed_checks", []):
                if failure not in first_failures:
                    first_failures.append(failure)
        blockers = tuple(first_failures[:12] or ["NO_CANDIDATE_PASSED_FULL_ENTRY_GATES"])
        signal = Signal("NEUTRAL", "NO_CANDIDATE_PASSED_FULL_ENTRY_GATES", 0.0, 0.0,
                        "No candidate passed all required entry gates.", None,
                        tuple(["OI_FIRST_GATE_PASSED_BUT_NO_FULLY_QUALIFIED_CANDIDATE"] + [f"CANDIDATE_GATE:{x}" for x in blockers]),
                        blockers)
        base_diag.update({
            "selected_candidate": None,
            "candidate_gate_failures_summary": {name: sum(1 for ev in candidate_gate_evaluations if name in ev.get("failed_checks", []))
                                                 for name in first_failures},
            "bullish_candidates": [{"setup":x["setup"],"level":round(x["level"],2),"score":round(x["score"],1),"distance":round(x["distance"],2)} for x in diagnostic_candidates["BULLISH"][:8]],
            "bearish_candidates": [{"setup":x["setup"],"level":round(x["level"],2),"score":round(x["score"],1),"distance":round(x["distance"],2)} for x in diagnostic_candidates["BEARISH"][:8]],
            "fib_touch_tolerance_points": touch_tolerance,
            "candidate_oi_gate_checks": candidate_oi_checks,
            "candidate_oi_gate_failures": candidate_oi_failures,
            "continuation_price_extension_guard": continuation_guard_diagnostics,
            "decision_model": "INDEPENDENT_PRICE_AND_OI_ANALYSIS_THEN_FULL_GATE_PREFLIGHT_AND_RANK",
        })
        return signal, base_diag

    # Sort only the candidates that survived every non-stateful entry gate.
    qualified_candidates.sort(key=lambda x: (-number(x.get("score"),0.0), number(x.get("distance"),99999), -int(x.get("touches",0))))
    best = qualified_candidates[0]
    direction = best["direction"]
    score = clamp(number(best.get("score"), 0.0), 0, 100)
    evidence = tuple(dict.fromkeys(list(best.get("evidence", []))))
    signal = Signal(direction, str(best["setup"]), round(score,1), round(clamp(score,0,92),1),
                    "; ".join(evidence[:8]), float(best["level"]), evidence, ())
    base_diag.update({
        "bullish_candidates":[{"setup":x["setup"],"level":round(x["level"],2),"score":round(x["score"],1),"distance":round(x["distance"],2)} for x in diagnostic_candidates["BULLISH"][:8]],
        "bearish_candidates":[{"setup":x["setup"],"level":round(x["level"],2),"score":round(x["score"],1),"distance":round(x["distance"],2)} for x in diagnostic_candidates["BEARISH"][:8]],
        "fib_touch_tolerance_points":touch_tolerance,
        "selected_candidate":safe_json(best),
        "selected_candidate_preflight": best.get("_preflight"),
        "candidate_oi_gate_checks":candidate_oi_checks,
        "candidate_oi_gate_failures":candidate_oi_failures,
        "continuation_price_extension_guard":continuation_guard_diagnostics,
        "decision_model":"INDEPENDENT_PRICE_AND_OI_ANALYSIS_THEN_FULL_GATE_PREFLIGHT_AND_RANK",
    })
    return signal,base_diag

def classify_market_regime(frame: pd.DataFrame, indicators: Indicators, now: datetime) -> dict[str, Any]:
    """Classify the broader intraday context and recent chop independently of setup scoring."""
    session_bars = completed_candles(frame, now)
    bars = session_bars.tail(24)
    if len(bars) < 8:
        return {"regime": "WARMUP", "reason": "FEWER_THAN_8_COMPLETED_CANDLES", "flip_count": None,
                "efficiency_ratio": None, "session_bias": "UNKNOWN", "ema_fast": None, "ema_slow": None}
    close = bars["close"].astype(float)
    session_close = session_bars["close"].astype(float)
    session_net = float(session_close.iloc[-1] - number(session_bars["open"].iloc[0], session_close.iloc[0]))
    session_path = float(np.sum(np.abs(session_close.diff().dropna().to_numpy(dtype=float)))) if len(session_close) > 1 else 0.0
    session_eff = abs(session_net) / session_path if session_path > 0 else 0.0
    atr_for_bias = max(1.0, indicators.atr if finite(indicators.atr) else 1.0)
    if session_net <= -1.5 * atr_for_bias and session_eff >= 0.22 and finite(indicators.minus_di) and finite(indicators.plus_di) and indicators.minus_di > indicators.plus_di * 1.08:
        session_bias = "BEARISH"
    elif session_net >= 1.5 * atr_for_bias and session_eff >= 0.22 and finite(indicators.minus_di) and finite(indicators.plus_di) and indicators.plus_di > indicators.minus_di * 1.08:
        session_bias = "BULLISH"
    else:
        session_bias = "NEUTRAL"
    changes = close.diff().dropna().to_numpy(dtype=float)
    atr = max(1.0, indicators.atr if finite(indicators.atr) else 1.0)
    noise_floor = max(0.5, 0.035 * atr)
    signs = [int(np.sign(x)) for x in changes if abs(x) >= noise_floor]
    flip_count = sum(1 for a, b in zip(signs, signs[1:]) if a != b)
    path = float(np.sum(np.abs(changes))) if len(changes) else 0.0
    net = float(close.iloc[-1] - close.iloc[0])
    efficiency = abs(net) / path if path > 0 else 0.0
    fast = close.ewm(span=5, adjust=False).mean()
    slow = close.ewm(span=13, adjust=False).mean()
    ema_fast, ema_slow = float(fast.iloc[-1]), float(slow.iloc[-1])
    ema_slope = float(fast.iloc[-1] - fast.iloc[-4]) if len(fast) >= 4 else 0.0
    width = float(bars["high"].max() - bars["low"].min())
    adx = indicators.adx if finite(indicators.adx) else 0.0
    di_bear = finite(indicators.minus_di) and finite(indicators.plus_di) and indicators.minus_di > indicators.plus_di * 1.08
    di_bull = finite(indicators.minus_di) and finite(indicators.plus_di) and indicators.plus_di > indicators.minus_di * 1.08
    mom_bear = indicators.momentum_3m < 0 and indicators.momentum_1m <= 0.0005
    mom_bull = indicators.momentum_3m > 0 and indicators.momentum_1m >= -0.0005
    # A confirmed short-horizon impulse can override the stale flip count, but only when
    # EMA slope, DI dominance, 1m/3m momentum and a meaningful recent price move all align.
    recent_impulse = float(close.iloc[-1] - close.iloc[-4]) if len(close) >= 4 else 0.0
    impulse_floor = max(1.75 * atr, 30.0)
    impulse_bull = (ema_fast > ema_slow and ema_slope > 0 and di_bull and mom_bull
                    and indicators.momentum_1m > 0 and recent_impulse >= impulse_floor)
    impulse_bear = (ema_fast < ema_slow and ema_slope < 0 and di_bear and mom_bear
                    and indicators.momentum_1m < 0 and recent_impulse <= -impulse_floor)
    # Preserve the chop guard unless a completed-bar impulse has strong multi-signal agreement.
    if impulse_bull:
        regime, reason = "TREND_BULLISH", "CONFIRMED_SHORT_HORIZON_BULLISH_IMPULSE_OVERRIDES_STALE_FLIP_COUNT"
    elif impulse_bear:
        regime, reason = "TREND_BEARISH", "CONFIRMED_SHORT_HORIZON_BEARISH_IMPULSE_OVERRIDES_STALE_FLIP_COUNT"
    elif flip_count >= 5 and efficiency < 0.40:
        regime, reason = "WHIPSAW", "FREQUENT_DIRECTION_FLIPS_AND_LOW_EFFICIENCY"
    elif efficiency < 0.25 and (adx < 23 or flip_count >= 2) and width <= max(8.0 * atr, 180.0):
        regime, reason = "SIDEWAYS", "LOW_DIRECTIONAL_EFFICIENCY_WITHIN_INTRADAY_RANGE"
    elif ema_fast < ema_slow and ema_slope < 0 and di_bear and mom_bear and efficiency >= 0.35:
        regime, reason = "TREND_BEARISH", "EMA_DI_AND_MOMENTUM_ALIGN_BEARISH"
    elif ema_fast > ema_slow and ema_slope > 0 and di_bull and mom_bull and efficiency >= 0.35:
        regime, reason = "TREND_BULLISH", "EMA_DI_AND_MOMENTUM_ALIGN_BULLISH"
    elif efficiency < 0.33 and flip_count >= 3:
        regime, reason = "SIDEWAYS", "MIXED_DIRECTIONAL_EVIDENCE_AND_REPEATED_CROSSES"
    else:
        regime, reason = "TRANSITION", "DIRECTIONAL_CONTEXT_NOT_SUFFICIENTLY_ALIGNED"
    range_low = float(bars["low"].min())
    range_high = float(bars["high"].max())
    range_width = max(0.01, range_high - range_low)
    range_location_pct = clamp((float(close.iloc[-1]) - range_low) / range_width * 100.0, 0.0, 100.0)
    prior_range = bars.iloc[:-2] if len(bars) > 4 else bars
    prior_range_low = float(prior_range["low"].min())
    prior_range_high = float(prior_range["high"].max())
    return {"regime": regime, "reason": reason, "flip_count": int(flip_count),
            "efficiency_ratio": round(efficiency, 4), "net_move_points": round(net, 2),
            "range_width_points": round(width, 2), "range_low": round(range_low, 2),
            "range_high": round(range_high, 2), "range_location_pct": round(range_location_pct, 1),
            "prior_range_low": round(prior_range_low, 2), "prior_range_high": round(prior_range_high, 2),
            "session_bias": session_bias,
            "session_net_points": round(session_net, 2), "session_efficiency_ratio": round(session_eff, 4),
            "ema_fast": round(ema_fast, 2), "ema_slow": round(ema_slow, 2), "ema_fast_slope": round(ema_slope, 2),
            "adx": round(adx, 2), "plus_di": round(indicators.plus_di, 2) if finite(indicators.plus_di) else None,
            "minus_di": round(indicators.minus_di, 2) if finite(indicators.minus_di) else None,
            "recent_impulse_points": round(recent_impulse, 2), "impulse_threshold_points": round(impulse_floor, 2),
            "impulse_override": bool(impulse_bull or impulse_bear)}


def qualify_local_oi(oi: Mapping[str, Any], signal: Signal, spot: float, step: float,
                     min_change_pct: float = 2.5) -> dict[str, Any]:
    """Revalidate the exact paired-flow mode attached to a directional price setup.

    Writer-led setups require directional writing paired with short covering. Buyer-led momentum
    setups require dominant option buying (>2.5% OI growth with premium rising) paired with
    opposite-side long unwinding (OI and premium both falling). Buyer-led flow is restricted to
    breakouts/breakdowns and continuous-trend setups; reversal setups continue to require writers.
    """
    threshold = max(0.025, min(0.10, number(min_change_pct, 2.5) / 100.0))
    premium_floor = 0.002
    direction = str(signal.direction).upper()
    setup = str(signal.setup).upper()
    evidence = {str(x).upper() for x in signal.evidence}
    buyer_mode = "OI_FLOW_MODE_BUYER_LED" in evidence
    flow_mode = "BUYER_LED_MOMENTUM" if buyer_mode else "WRITER_COVERING"
    empty = {"qualified": False, "flow_mode": flow_mode,
             "writing_oi_threshold_pct_exclusive": threshold * 100.0,
             "covering_oi_decline_threshold_pct_exclusive": 0.5,
             "premium_change_min_pct": premium_floor * 100.0,
             "supporting_rows": [], "opposing_rows": [], "reference_strikes": [],
             "primary_flow": None, "secondary_flow": None, "pair_distance_points": None,
             "paired_flow": None, "candidate_pairs_considered": 0}
    if direction not in {"BULLISH", "BEARISH"}:
        return {**empty, "reason": "NO_DIRECTIONAL_PRICE_STRUCTURE"}
    if not oi.get("tactical_available"):
        return {**empty, "reason": "SAME_SESSION_LOCAL_OI_BASELINE_UNAVAILABLE_OR_STALE",
                "tactical_age_minutes": oi.get("snapshot_age_minutes")}

    bullish_setups = {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "EARLY_SUPPORT_RECLAIM",
                      "CONFIRMED_BREAKOUT", "CONTINUOUS_BULLISH_TREND"}
    bearish_setups = {"RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION", "EARLY_RESISTANCE_REJECTION",
                      "CONFIRMED_BREAKDOWN", "CONTINUOUS_BEARISH_TREND"}
    if setup in bullish_setups:
        default_primary, default_secondary = "put", "call"
    elif setup in bearish_setups:
        default_primary, default_secondary = "call", "put"
    else:
        return {**empty, "reason": "UNSUPPORTED_SETUP_FOR_LOCAL_OI_PAIR", "setup": setup}
    if buyer_mode and setup not in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN",
                                    "CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"}:
        return {**empty, "reason": "BUYER_LED_FLOW_RESTRICTED_TO_MOMENTUM_SETUPS", "setup": setup}

    if buyer_mode:
        primary_side, secondary_side = ("call", "put") if direction == "BULLISH" else ("put", "call")
    else:
        primary_side, secondary_side = default_primary, default_secondary
    ref = number(signal.level, spot)
    reversal = setup in {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "EARLY_SUPPORT_RECLAIM",
                         "RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION", "EARLY_RESISTANCE_REJECTION"}
    center = ref if reversal else spot
    atm = round_to_grid(spot, step)
    band = max(3.0 * step, 150.0)
    rows = [r for r in oi.get("walls", []) if isinstance(r, Mapping) and finite(r.get("strike"))
            and abs(number(r.get("strike")) - center) <= band + 0.01
            and abs(number(r.get("strike")) - spot) <= max(4.0 * step, 200.0) + 0.01]

    def flow_item(row: Mapping[str, Any], side: str, primary_role: bool) -> Optional[dict[str, Any]]:
        change = number(row.get(f"{side}_change_pct"))
        premium_change = number(row.get(f"{side}_premium_change_pct"))
        delta = number(row.get(f"{side}_delta_oi"))
        baseline = number(row.get(f"{side}_prev_oi"))
        old_premium = number(row.get(f"{side}_prev_ltp"))
        new_premium = number(row.get(f"{side}_ltp"))
        current_oi = number(row.get(f"{side}_oi"))
        if not all(finite(x) for x in (change, premium_change, delta, baseline, old_premium, new_premium, current_oi)):
            return None
        if baseline < 10000 or current_oi < 0 or min(old_premium, new_premium) < 5:
            return None
        flow = classify_oi_flow(change, premium_change)
        if not buyer_mode:
            passed = (change > threshold and premium_change <= -premium_floor and flow == "SHORT_BUILDUP_WRITING"
                      if primary_role else change < -0.005 and premium_change >= premium_floor and flow == "SHORT_COVERING")
        else:
            passed = (change > threshold and premium_change >= premium_floor and flow == "LONG_BUILDUP_BUYING"
                      if primary_role else change < -0.005 and premium_change <= -premium_floor and flow == "LONG_UNWINDING")
        if not passed:
            return None
        return {"strike": number(row.get("strike")), "option_side": side.upper(),
                "oi_change_pct": round(change * 100, 3), "premium_change_pct": round(premium_change * 100, 3),
                "delta_oi": round(delta, 1), "baseline_oi": round(baseline, 1),
                "current_oi": round(current_oi, 1), "flow": flow}

    primary_candidates: list[dict[str, Any]] = []
    secondary_candidates: list[dict[str, Any]] = []
    for row in rows:
        strike = number(row.get("strike"))
        primary = flow_item(row, primary_side, True)
        secondary = flow_item(row, secondary_side, False)
        if primary:
            if buyer_mode:
                location_ok = abs(strike - atm) <= 2.0 * step + 0.01
            elif reversal:
                grid_location_buffer = max(15.0, 0.5 * step)
                location_ok = strike <= ref + grid_location_buffer if direction == "BULLISH" else strike >= ref - grid_location_buffer
            else:
                location_ok = strike <= atm + step + 0.01 if direction == "BULLISH" else strike >= atm - step - 0.01
            if location_ok:
                primary_candidates.append(primary)
        if secondary:
            secondary_candidates.append(secondary)

    pairs: list[dict[str, Any]] = []
    for primary in primary_candidates:
        for secondary in secondary_candidates:
            distance = abs(number(primary.get("strike")) - number(secondary.get("strike")))
            if distance > 2.0 * step + 0.01:
                continue
            proximity = max(0.0, 1.0 - distance / max(1.0, 2.0 * step))
            score = (number(primary.get("oi_change_pct"), 0.0)
                     + 0.20 * abs(number(secondary.get("oi_change_pct"), 0.0))
                     + 0.08 * abs(number(primary.get("premium_change_pct"), 0.0))
                     + 0.05 * abs(number(secondary.get("premium_change_pct"), 0.0))
                     + 1.5 * proximity)
            pairs.append({"primary": primary, "secondary": secondary,
                          "distance": round(distance, 2), "score": score})
    pairs.sort(key=lambda p: (-number(p.get("score"), 0.0),
                              -number(p.get("primary", {}).get("oi_change_pct"), 0.0),
                              number(p.get("distance"), 1e9)))

    # Reject only material counterflow at the setup boundary. For a buyer-led bullish setup,
    # nearby put buying or call writing is counter-directional; inverse for bearish.
    opposing: list[dict[str, Any]] = []
    for row in rows:
        strike = number(row.get("strike"))
        if abs(strike - center) > step + 0.01:
            continue
        for side in ("call", "put"):
            change = number(row.get(f"{side}_change_pct"))
            premium = number(row.get(f"{side}_premium_change_pct"))
            baseline = number(row.get(f"{side}_prev_oi"))
            old = number(row.get(f"{side}_prev_ltp")); new = number(row.get(f"{side}_ltp"))
            if not all(finite(v) for v in (change, premium, baseline, old, new)) or baseline < 10000 or min(old, new) < 5:
                continue
            flow = classify_oi_flow(change, premium)
            opposing_flow = ((direction == "BULLISH" and
                              ((side == "call" and flow == "SHORT_BUILDUP_WRITING") or
                               (side == "put" and flow == "LONG_BUILDUP_BUYING"))) or
                             (direction == "BEARISH" and
                              ((side == "put" and flow == "SHORT_BUILDUP_WRITING") or
                               (side == "call" and flow == "LONG_BUILDUP_BUYING"))))
            # A dominant buyer-led leg itself is expected to be a long buildup; do not classify
            # it as opposing simply because it is on the primary option side.
            if buyer_mode and side == primary_side and flow == "LONG_BUILDUP_BUYING":
                opposing_flow = False
            if opposing_flow and abs(change) > threshold and abs(premium) >= premium_floor:
                opposing.append({"strike": strike, "option_side": side.upper(),
                                 "oi_change_pct": round(change * 100, 3),
                                 "premium_change_pct": round(premium * 100, 3), "flow": flow})
    best = pairs[0] if pairs else None
    opposing_strength = max((abs(number(x.get("oi_change_pct"), 0.0)) for x in opposing), default=0.0)
    primary_strength = abs(number((best or {}).get("primary", {}).get("oi_change_pct"), 0.0))
    conflict = bool(best and opposing_strength >= primary_strength and opposing_strength > threshold * 100)
    qualified = bool(best and not conflict)
    primary = best.get("primary") if best else None
    secondary = best.get("secondary") if best else None
    refs = sorted({number(primary.get("strike")), number(secondary.get("strike"))}) if primary and secondary else []
    if buyer_mode:
        reason = ("LOCAL_OI_PAIRED_BUYER_MOMENTUM_AND_LONG_UNWINDING_CONFIRMED" if qualified else
                  "LOCAL_OI_COUNTERFLOW_CONFLICTS_AT_SETUP_BOUNDARY" if conflict else
                  "BUYER_LED_LOCAL_OI_PAIR_NOT_CONFIRMED_STRICTLY_ABOVE_2_5_PERCENT")
        primary_desc, secondary_desc = "LONG_BUILDUP_BUYING", "LONG_UNWINDING"
    else:
        reason = ("LOCAL_OI_PAIRED_WRITING_COVERING_CONFIRMED" if qualified else
                  "LOCAL_OI_COUNTERFLOW_CONFLICTS_AT_SETUP_BOUNDARY" if conflict else
                  "REQUIRED_LOCAL_OI_PAIR_NOT_CONFIRMED_STRICTLY_ABOVE_2_5_PERCENT")
        primary_desc, secondary_desc = "SHORT_BUILDUP_WRITING", "SHORT_COVERING"
    return {**empty, "qualified": qualified, "reason": reason, "setup": setup, "direction": direction,
            "flow_mode": flow_mode, "reference_level": round(ref, 2), "oi_search_center": round(center, 2),
            "primary_required": {"option_side": primary_side.upper(), "flow": primary_desc},
            "secondary_required": {"option_side": secondary_side.upper(), "flow": secondary_desc},
            "primary_flow": primary, "secondary_flow": secondary,
            "supporting_rows": ([primary, secondary] if primary and secondary else []),
            "opposing_rows": opposing[:5], "reference_strikes": refs,
            "pair_distance_points": best.get("distance") if best else None,
            "paired_flow": {"primary_strike": primary.get("strike"), "secondary_strike": secondary.get("strike"),
                            "distance_points": best.get("distance"), "score": round(number(best.get("score")), 3),
                            "flow_mode": flow_mode} if best and primary and secondary else None,
            "candidate_pairs_considered": len(pairs), "tactical_age_minutes": oi.get("snapshot_age_minutes"),
            "tactical_available": bool(oi.get("tactical_available")), "local_rows_considered": len(rows)}

def qualify_regime(signal: Signal, regime: Mapping[str, Any], indicators: Indicators, spot: float,
                   fib_divergence: Optional[Mapping[str, Any]] = None,
                   local_oi: Optional[Mapping[str, Any]] = None,
                   setup_rules: Optional[Mapping[str, Any]] = None) -> dict[str, Any]:
    """Apply regime policy after explicit OI, Fib/divergence and setup execution gates."""
    direction = str(signal.direction).upper()
    setup = str(signal.setup).upper()
    name = str(regime.get("regime", "TRANSITION")).upper()
    session_bias = str(regime.get("session_bias", "UNKNOWN")).upper()
    fib_ok = bool((fib_divergence or {}).get("qualified"))
    oi_ok = bool((local_oi or {}).get("qualified"))
    setup_ok = bool((setup_rules or {}).get("qualified"))
    if direction not in {"BULLISH", "BEARISH"}:
        return {"qualified": False, "reason": "NO_DIRECTIONAL_STRUCTURE", "regime": name}
    continuous = ((setup == "CONTINUOUS_BULLISH_TREND" and direction == "BULLISH")
                  or (setup == "CONTINUOUS_BEARISH_TREND" and direction == "BEARISH"))
    is_breakout_setup = ((setup == "CONFIRMED_BREAKOUT" and direction == "BULLISH")
                         or (setup == "CONFIRMED_BREAKDOWN" and direction == "BEARISH"))
    watch = regime.get("directional_watch") if isinstance(regime.get("directional_watch"), Mapping) else {}
    scan_time = parse_dt(regime.get("scan_timestamp")) or now_ist()
    watch_time = parse_dt(watch.get("first_seen"))
    watch_aligned = bool(str(watch.get("direction", "")).upper() == direction and watch_time is not None
                         and 0 <= (scan_time.astimezone(IST) - watch_time.astimezone(IST)).total_seconds() <= 15 * 60)
    if not oi_ok:
        return {"qualified": False, "reason": "LOCAL_OI_PAIR_NOT_CONFIRMED", "regime": name}
    if not setup_ok:
        return {"qualified": False, "reason": "SETUP_RULES_NOT_CONFIRMED", "regime": name}
    if not fib_ok:
        return {"qualified": False, "reason": "FIB_DIVERGENCE_OR_OPPOSING_DIVERGENCE_GATE_FAILED", "regime": name}

    # Early-session regime classification can legitimately remain WARMUP even when enough
    # price history exists to evaluate a specific completed-candle breakout. Permit that path
    # only after the setup validator and paired-OI gate have both passed. Reversals and
    # untriggered continuations still require their normal context/watch rules.
    if name == "WARMUP" and not (continuous and watch_aligned) and not is_breakout_setup:
        return {"qualified": False, "reason": "SETUP_SPECIFIC_WARMUP_REQUIRES_CONFIRMED_BREAK_OR_PERSISTENT_WATCH",
                "regime": name, "directional_watch_aligned": watch_aligned}
    if name == "WARMUP" and is_breakout_setup:
        return {"qualified": True, "reason": "WARMUP_BREAKOUT_ALLOWED_BY_COMPLETED_PRICE_TRIGGER_AND_STRICT_LOCAL_OI",
                "regime": name, "session_bias": session_bias, "directional_watch_aligned": watch_aligned,
                "price_trigger_confirmed": True, "local_oi_confirmed": True}

    bullish_reversals = {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "EARLY_SUPPORT_RECLAIM"}
    bearish_reversals = {"RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION", "EARLY_RESISTANCE_REJECTION"}
    reversal = ((setup in bullish_reversals and direction == "BULLISH")
                or (setup in bearish_reversals and direction == "BEARISH"))
    breakout = ((setup == "CONFIRMED_BREAKOUT" and direction == "BULLISH")
                or (setup == "CONFIRMED_BREAKDOWN" and direction == "BEARISH"))
    if continuous:
        expected = "TREND_BULLISH" if direction == "BULLISH" else "TREND_BEARISH"
        writer_change = number((local_oi or {}).get("primary_flow", {}).get("oi_change_pct"), 0.0) if isinstance((local_oi or {}).get("primary_flow"), Mapping) else 0.0
        momentum_aligned = (indicators.momentum_3m > 0.00015 and indicators.momentum_1m >= -0.00015) if direction == "BULLISH" else (indicators.momentum_3m < -0.00015 and indicators.momentum_1m <= 0.00015)
        if name != expected and not (name in {"TRANSITION", "WARMUP"} and watch_aligned and momentum_aligned):
            return {"qualified": False, "reason": "CONTINUOUS_TREND_REQUIRES_MATCHING_REGIME_OR_FRESH_PERSISTENT_WATCH",
                    "regime": name, "session_bias": session_bias, "directional_watch_aligned": watch_aligned}
        if session_bias in {"BULLISH", "BEARISH"} and session_bias != direction and not (writer_change >= 8.0 and momentum_aligned):
            return {"qualified": False, "reason": "CONTINUOUS_TREND_VETOED_BY_OPPOSING_SESSION_BIAS",
                    "regime": name, "session_bias": session_bias}
        return {"qualified": True, "reason": "CONTINUOUS_TREND_WITH_PAIRED_OI_AND_ACTIVE_PRICE_TRIGGER_CONFIRMED",
                "regime": name, "session_bias": session_bias, "directional_watch_aligned": watch_aligned}

    if name in {"SIDEWAYS", "WHIPSAW"}:
        location = number(regime.get("range_location_pct"))
        if reversal:
            edge = ((direction == "BULLISH" and finite(location) and location <= 35.0)
                    or (direction == "BEARISH" and finite(location) and location >= 65.0))
            if edge:
                return {"qualified": True, "reason": "FIB_DIVERGENCE_REVERSAL_AT_OUTER_RANGE_EDGE_WITH_LOCAL_OI",
                        "regime": name, "session_bias": session_bias, "range_location_pct": location}
            return {"qualified": False, "reason": "RANGE_REVERSAL_NOT_AT_OUTER_35_PERCENT_RANGE_EDGE",
                    "regime": name, "session_bias": session_bias, "range_location_pct": location}
        if breakout:
            high = number(regime.get("prior_range_high")); low = number(regime.get("prior_range_low"))
            buffer = max(0.75 * indicators.atr, 15.0)
            beyond = ((direction == "BULLISH" and finite(high) and spot > high + buffer)
                      or (direction == "BEARISH" and finite(low) and spot < low - buffer))
            if beyond:
                return {"qualified": True, "reason": "BREAKOUT_CLEARED_PRIOR_CHOP_RANGE_WITH_BUFFER",
                        "regime": name, "session_bias": session_bias, "range_escape_buffer_points": round(buffer, 2)}
            return {"qualified": False, "reason": "CHOP_BREAK_REQUIRES_CLEAR_ESCAPE_BEYOND_PRIOR_RANGE",
                    "regime": name, "session_bias": session_bias, "range_escape_buffer_points": round(buffer, 2),
                    "prior_range_high": high if finite(high) else None, "prior_range_low": low if finite(low) else None}
        return {"qualified": False, "reason": "SIDEWAYS_WHIPSAW_BLOCKS_NON_EDGE_NON_BREAK_SETUP",
                "regime": name, "session_bias": session_bias}

    if reversal:
        return {"qualified": True, "reason": "CONFIRMED_FIB_DIVERGENCE_REVERSAL_WITH_STRICT_LOCAL_OI",
                "regime": name, "session_bias": session_bias}
    if breakout:
        expected = "TREND_BULLISH" if direction == "BULLISH" else "TREND_BEARISH"
        if name == expected:
            return {"qualified": True, "reason": "TWO_CLOSE_FIB_BREAK_WITH_ALIGNED_TREND_AND_LOCAL_OI",
                    "regime": name, "session_bias": session_bias}
        if name == "TRANSITION":
            high = number(regime.get("prior_range_high")); low = number(regime.get("prior_range_low"))
            buffer = max(0.75 * indicators.atr, 15.0)
            beyond = ((direction == "BULLISH" and finite(high) and spot > high + buffer)
                      or (direction == "BEARISH" and finite(low) and spot < low - buffer))
            if beyond:
                return {"qualified": True, "reason": "TRANSITION_BREAK_WITH_CLEAR_PRIOR_RANGE_ESCAPE",
                        "regime": name, "session_bias": session_bias, "range_escape_buffer_points": round(buffer, 2)}
            return {"qualified": False, "reason": "TRANSITION_BREAK_REQUIRES_CLEAR_ESCAPE_BEYOND_PRIOR_RANGE",
                    "regime": name, "session_bias": session_bias, "range_escape_buffer_points": round(buffer, 2),
                    "prior_range_high": high if finite(high) else None, "prior_range_low": low if finite(low) else None}
        return {"qualified": False, "reason": "BREAKOUT_VETOED_BY_OPPOSING_TREND_REGIME",
                "regime": name, "session_bias": session_bias}
    return {"qualified": False, "reason": "UNSUPPORTED_MATRIX_SCENARIO", "regime": name,
            "session_bias": session_bias}

def diagnose_expiry_pin(oi: Mapping[str, Any], fib: Mapping[str, Any], indicators: Indicators,
                        expiry: str, now: datetime, step: float, min_change_pct: float = 2.5) -> dict[str, Any]:
    """Detect same-strike call+put writing inside a narrow Fib range on/near expiry."""
    try: expiry_date=date.fromisoformat(str(expiry)[:10]); expiry_days=(expiry_date-now.astimezone(IST).date()).days
    except (TypeError,ValueError): expiry_days=999
    up=fib.get("up_leg") if isinstance(fib.get("up_leg"),Mapping) else None
    down=fib.get("down_leg") if isinstance(fib.get("down_leg"),Mapping) else None
    support=number((fib.get("bullish_support_zone") or {}).get("fib_61_8")) if isinstance(fib.get("bullish_support_zone"),Mapping) else number((up or {}).get("retracements",{}).get("61.8"))
    resistance=number((fib.get("bearish_resistance_levels") or {}).get("fib_61_8")) if isinstance(fib.get("bearish_resistance_levels"),Mapping) else number((down or {}).get("retracements",{}).get("61.8"))
    if finite(support) and finite(resistance) and support>resistance: support,resistance=resistance,support
    fib_gap=resistance-support if finite(support) and finite(resistance) else float("nan")
    between=bool(finite(support) and finite(resistance) and support<=indicators.spot<=resistance)
    atm=round_to_grid(indicators.spot,step)
    row=next((r for r in oi.get("walls",[]) if isinstance(r,Mapping) and finite(r.get("strike")) and abs(number(r.get("strike"))-atm)<0.5),None)
    threshold=max(0.025,min(0.10,number(min_change_pct,2.5)/100.0))
    def writing(side: str) -> bool:
        if not row:return False
        change=number(row.get(f"{side}_change_pct")); prem=number(row.get(f"{side}_premium_change_pct"))
        base=number(row.get(f"{side}_prev_oi")); old=number(row.get(f"{side}_prev_ltp")); new=number(row.get(f"{side}_ltp"))
        return bool(all(finite(v) for v in (change,prem,base,old,new)) and base>=10000 and min(old,new)>=5
                    and change>threshold and prem<=-0.002
                    and classify_oi_flow(change,prem)=="SHORT_BUILDUP_WRITING")
    both_writing=writing("call") and writing("put")
    flat_momentum=abs(indicators.momentum_1m)<0.0012 and abs(indicators.momentum_3m)<0.0025
    neutral_rsi=finite(indicators.rsi) and 44<=indicators.rsi<=56
    detected=bool(expiry_days<=1 and finite(fib_gap) and 0<=fib_gap<=max(1.2*indicators.atr,50.0)
                  and between and both_writing and (flat_momentum or neutral_rsi))
    return {"detected":detected,"expiry_days":expiry_days,
            "fib_support_61_8":support if finite(support) else None,
            "fib_resistance_61_8":resistance if finite(resistance) else None,
            "fib_gap_points":round(fib_gap,2) if finite(fib_gap) else None,
            "atm_strike":atm if finite(atm) else None,"price_between_fib_levels":between,
            "same_strike_call_put_writing_gt_threshold":both_writing,
            "oi_change_threshold_pct_exclusive":threshold*100,"flat_momentum":flat_momentum,"neutral_rsi":neutral_rsi,
            "reason":"EXPIRY_PIN_NO_ENTRY" if detected else "PIN_CONDITIONS_NOT_COMPLETE"}

def qualify_fib_divergence(signal: Signal, regime: Mapping[str, Any], fib: Mapping[str, Any],
                            divergence: Mapping[str, Any], spot: float, atr: float) -> dict[str, Any]:
    """Validate matrix reversal Fib/divergence; expose Fib distance for continuation exclusions."""
    direction=str(signal.direction).upper(); setup=str(signal.setup).upper()
    all_fibs=_fib_price_levels(fib); tolerance=_fib_touch_tolerance(spot)
    if setup in {"CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"}:
        all_fibs=_material_fib_price_levels(fib, atr)
    fib_distances=[{"level":round(x,2),"distance_points":round(abs(spot-x),2)} for x in all_fibs]
    closest=min(fib_distances,key=lambda x:x["distance_points"]) if fib_distances else None
    near_fib=bool(closest and number(closest.get("distance_points"))<=tolerance)
    common={"fib_available":bool(fib.get("available")),"divergence_available":bool(divergence.get("available")),
            "fib_touch_tolerance_points":tolerance,"nearest_fib_level":closest.get("level") if closest else None,
            "nearest_fib_distance_points":closest.get("distance_points") if closest else None,
            "near_fib":near_fib,"fib_levels_checked":fib_distances}
    if direction not in {"BULLISH","BEARISH"}:
        return {"qualified":False,"reason":"NO_DIRECTIONAL_SIGNAL","fib_confluence":False,
                "divergence_required":False,"opposing_divergence_confirmed":False,**common}
    matching=divergence.get("bullish") if direction=="BULLISH" else divergence.get("bearish")
    opposing=divergence.get("bearish") if direction=="BULLISH" else divergence.get("bullish")
    opposing=dict(opposing) if isinstance(opposing,Mapping) else None
    trigger=number(signal.level,spot)
    opp_price=number((opposing or {}).get("price_high_2" if direction=="BULLISH" else "price_low_2"))
    opposing_near=bool(opposing and finite(opp_price) and abs(opp_price-trigger)<=max(1.0*atr,45.0))
    if setup in {"CONTINUOUS_BULLISH_TREND","CONTINUOUS_BEARISH_TREND"}:
        # Fibonacci proximity is descriptive context for continuation, not a generic veto.
        # A nearby opposing divergence is recorded for the setup gate, where strong paired OI
        # and aligned momentum can be distinguished from a genuine momentum reversal.
        return {"qualified":True,"reason":"CONTINUATION_FIB_PROXIMITY_IS_CONTEXT_NOT_VETO",
                "fib_confluence":False,"divergence_required":False,"matching_divergence":matching,
                "opposing_divergence_confirmed":opposing_near,"opposing_divergence":opposing,
                "opposing_divergence_distance":round(abs(opp_price-trigger),2) if opposing_near else None,**common}
    if opposing_near:
        return {"qualified":False,"reason":"CONFIRMED_OPPOSING_RSI_DIVERGENCE_NEAR_TRIGGER","fib_confluence":False,
                "divergence_required":False,"matching_divergence":matching,"opposing_divergence_confirmed":True,
                "opposing_divergence":opposing,"opposing_divergence_distance":round(abs(opp_price-trigger),2),**common}
    if setup in {"CONFIRMED_BREAKOUT","CONFIRMED_BREAKDOWN"}:
        return {"qualified":True,"reason":"FIB_BREAK_BOUNDARY_CHECKED_BY_SIGNAL_GENERATOR;NO_OPPOSING_DIVERGENCE",
                "fib_confluence":None,"divergence_required":False,"matching_divergence":matching,
                "opposing_divergence_confirmed":False,**common}
    reversal=((setup in {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "EARLY_SUPPORT_RECLAIM"} and direction=="BULLISH")
              or (setup in {"RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION", "EARLY_RESISTANCE_REJECTION"} and direction=="BEARISH"))
    if not reversal:
        return {"qualified":False,"reason":"UNSUPPORTED_MATRIX_SCENARIO","fib_confluence":False,
                "divergence_required":False,"matching_divergence":matching,"opposing_divergence_confirmed":False,**common}
    if not isinstance(matching,Mapping) or not matching:
        return {"qualified":False,"reason":"REVERSAL_REQUIRES_CONFIRMED_MATCHING_RSI_DIVERGENCE","fib_confluence":False,
                "divergence_required":True,"matching_divergence":None,"opposing_divergence_confirmed":False,**common}
    if direction=="BULLISH":
        zone=fib.get("bullish_support_zone") if isinstance(fib.get("bullish_support_zone"),Mapping) else {}
        levels=[number(zone.get(k)) for k in ("fib_50","fib_61_8")]
        role="BULLISH_FIB_SUPPORT_50_61_8"
    else:
        zone=fib.get("bearish_resistance_levels") if isinstance(fib.get("bearish_resistance_levels"),Mapping) else {}
        levels=[number(zone.get(k)) for k in ("fib_61_8","fib_100")]
        role="BEARISH_FIB_RESISTANCE_61_8_OR_100"
    levels=[x for x in levels if finite(x)]
    distances=[{"level":round(x,2),"spot_distance":round(abs(spot-x),2),"structure_distance":round(abs(trigger-x),2),
                "distance":round(min(abs(spot-x),abs(trigger-x)),2)} for x in levels]
    closest_reversal=min(distances,key=lambda x:x["distance"]) if distances else None
    confluence=bool(closest_reversal and number(closest_reversal.get("distance"))<=tolerance)
    return {"qualified":confluence,"reason":"REVERSAL_CONFIRMED_DIVERGENCE_AND_FIB_TOUCH" if confluence else "REVERSAL_REQUIRES_FIB_TOUCH_WITHIN_TOLERANCE",
            "fib_confluence":confluence,"fib_role":role,"fib_tolerance_points":tolerance,
            "closest_fib_level":closest_reversal.get("level") if closest_reversal else None,
            "closest_fib_distance_points":closest_reversal.get("distance") if closest_reversal else None,
            "divergence_required":True,"matching_divergence":matching,"opposing_divergence_confirmed":False,**common}
def qualify_setup_rules(signal: Signal, frame: pd.DataFrame, indicators: Indicators,
                        regime: Mapping[str, Any], fib_gate: Mapping[str, Any],
                        oi_gate: Mapping[str, Any], now: datetime) -> dict[str, Any]:
    """Apply the execution trigger for four Excel scenarios plus a continuous-trend setup."""
    direction=str(signal.direction).upper(); setup=str(signal.setup).upper()
    bars=completed_candles(frame,now.astimezone(IST))
    reversal_setups = {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "EARLY_SUPPORT_RECLAIM",
                       "RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION", "EARLY_RESISTANCE_REJECTION"}
    continuous_setups = {"CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"}
    required_bars = 8 if setup in reversal_setups else 4
    out={"qualified":False,"setup":setup,"direction":direction,"required_completed_bars":required_bars,
         "completed_bars":int(len(bars)),"checks":[]}
    if direction not in {"BULLISH","BEARISH"}:return {**out,"reason":"NO_DIRECTIONAL_SETUP"}
    if len(bars)<required_bars:return {**out,"reason":"INSUFFICIENT_SETUP_SPECIFIC_COMPLETED_BARS"}
    if not finite(indicators.atr) or indicators.atr<=0:
        return {**out,"reason":"ATR_UNAVAILABLE"}
    if not finite(indicators.rsi) and setup not in continuous_setups:
        return {**out,"reason":"RSI_UNAVAILABLE_FOR_SETUP"}
    if not finite(signal.level):return {**out,"reason":"STRUCTURAL_TRIGGER_LEVEL_UNAVAILABLE"}
    if not oi_gate.get("qualified"):return {**out,"reason":"SETUP_SPECIFIC_LOCAL_OI_PAIR_NOT_CONFIRMED"}
    closes=bars["close"].astype(float).reset_index(drop=True)
    level=float(signal.level); buffer=max(2.0,0.08*indicators.atr)
    last=float(closes.iloc[-1]); prev=float(closes.iloc[-2]); spot_dist=abs(indicators.spot-level)
    current_3m=float(closes.iloc[-1]/closes.iloc[-4]-1.0) if len(closes)>=4 and closes.iloc[-4] else 0.0
    prior_3m=float(closes.iloc[-4]/closes.iloc[-7]-1.0) if len(closes)>=7 and closes.iloc[-7] else 0.0
    expanding_up=current_3m>0 and current_3m>prior_3m
    expanding_down=current_3m<0 and current_3m<prior_3m
    opposing=bool(fib_gate.get("opposing_divergence_confirmed"))
    regime_name=str(regime.get("regime","TRANSITION")).upper()
    session_bias=str(regime.get("session_bias","UNKNOWN")).upper()
    evidence=" ".join(signal.evidence).upper()
    buyer_led = "OI_FLOW_MODE_BUYER_LED" in evidence
    early_buyer_breakout = buyer_led and "BUYER_LED_EARLY_SINGLE_CLOSE_BREAKOUT" in evidence
    early_buyer_breakdown = buyer_led and "BUYER_LED_EARLY_SINGLE_CLOSE_BREAKDOWN" in evidence

    if setup in {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "EARLY_SUPPORT_RECLAIM"} and direction=="BULLISH":
        checks={"confirmed_bullish_rsi_divergence":bool(fib_gate.get("matching_divergence")),
                "fib_50_or_61_8_touch_confirmed":bool(fib_gate.get("qualified") and fib_gate.get("fib_confluence")),
                "completed_close_reclaimed_support":last>level+max(1.5,0.05*indicators.atr),
                "live_spot_near_tested_support":spot_dist<=max(1.25*indicators.atr,45.0),
                "one_minute_momentum_turning_up":indicators.momentum_1m>0,
                "three_minute_momentum_not_materially_bearish":indicators.momentum_3m>-0.0010,
                "no_nearby_opposing_divergence":not opposing}
    elif setup in {"RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION", "EARLY_RESISTANCE_REJECTION"} and direction=="BEARISH":
        checks={"confirmed_bearish_rsi_divergence":bool(fib_gate.get("matching_divergence")),
                "fib_61_8_or_100_touch_confirmed":bool(fib_gate.get("qualified") and fib_gate.get("fib_confluence")),
                "completed_close_rejected_below_resistance":last<level-max(1.5,0.05*indicators.atr),
                "live_spot_near_tested_resistance":spot_dist<=max(1.25*indicators.atr,45.0),
                "one_minute_momentum_turning_down":indicators.momentum_1m<0,
                "three_minute_momentum_not_materially_bullish":indicators.momentum_3m<0.0010,
                "no_nearby_opposing_divergence":not opposing}
    elif setup=="CONFIRMED_BREAKOUT" and direction=="BULLISH":
        early_close_ok = bool(early_buyer_breakout and last>level+buffer and prev<=level+buffer
                              and indicators.spot>=level-max(0.15*indicators.atr,3.0)
                              and indicators.rsi>=60.0 and indicators.momentum_1m>0.00015
                              and indicators.momentum_3m>=0.00065)
        two_close_ok = bool(last>level+buffer and prev>level+buffer)
        checks={"fib_resistance_boundary_confirmed":("TWO_COMPLETED_CLOSES_ABOVE_FIB_RESISTANCE" in evidence
                                                       or early_buyer_breakout),
                "two_closes_or_strict_buyer_led_first_close":two_close_ok or early_close_ok,
                "live_spot_above_or_at_first_close_boundary":(indicators.spot>level+buffer or early_close_ok),
                "rsi_at_least_55":indicators.rsi>=55.0,
                "one_and_three_minute_momentum_positive":indicators.momentum_1m>0 and indicators.momentum_3m>0,
                "momentum_expanding_or_follow_through":expanding_up or (last>prev and indicators.momentum_1m>0),
                "no_confirmed_opposing_divergence_near_trigger":not opposing,
                "not_overextended_from_boundary":spot_dist<=max(1.5*indicators.atr,45.0)}
    elif setup=="CONFIRMED_BREAKDOWN" and direction=="BEARISH":
        early_close_ok = bool(early_buyer_breakdown and last<level-buffer and prev>=level-buffer
                              and indicators.spot<=level+max(0.15*indicators.atr,3.0)
                              and indicators.rsi<=40.0 and indicators.momentum_1m<-0.00015
                              and indicators.momentum_3m<=-0.00065)
        two_close_ok = bool(last<level-buffer and prev<level-buffer)
        checks={"fib_support_boundary_confirmed":("TWO_COMPLETED_CLOSES_BELOW_FIB_SUPPORT" in evidence
                                                    or early_buyer_breakdown),
                "two_closes_or_strict_buyer_led_first_close":two_close_ok or early_close_ok,
                "live_spot_below_or_at_first_close_boundary":(indicators.spot<level-buffer or early_close_ok),
                "rsi_at_most_45":indicators.rsi<=45.0,
                "one_and_three_minute_momentum_negative":indicators.momentum_1m<0 and indicators.momentum_3m<0,
                "momentum_expanding_or_follow_through":expanding_down or (last<prev and indicators.momentum_1m<0),
                "no_confirmed_opposing_divergence_near_trigger":not opposing,
                "not_overextended_from_boundary":spot_dist<=max(1.5*indicators.atr,45.0)}
    elif setup in {"CONTINUOUS_BULLISH_TREND","CONTINUOUS_BEARISH_TREND"}:
        bullish=direction=="BULLISH"
        extension_guard = continuation_price_extension_guard(frame, indicators, indicators.spot, now, direction)
        watch = regime.get("directional_watch") if isinstance(regime.get("directional_watch"), Mapping) else {}
        watch_direction = str(watch.get("direction", "")).upper()
        watch_time = parse_dt(watch.get("first_seen"))
        watch_age_seconds = (now.astimezone(IST)-watch_time.astimezone(IST)).total_seconds() if watch_time else float("inf")
        watch_fresh = bool(0.0 <= watch_age_seconds <= 15*60)
        watch_aligned = watch_direction == direction and watch_fresh
        expected_regime = "TREND_BULLISH" if bullish else "TREND_BEARISH"
        writer_change = number((oi_gate.get("primary_flow") or {}).get("oi_change_pct"), 0.0)
        momentum_aligned = (indicators.momentum_3m>0.00015 and indicators.momentum_1m>=-0.00015) if bullish else (indicators.momentum_3m<-0.00015 and indicators.momentum_1m<=0.00015)
        closes_array = closes.to_numpy(dtype=float)
        recent_move = float(closes_array[-1]-closes_array[-4]) if len(closes_array)>=4 else 0.0
        recent_trigger = ((recent_move >= max(0.15*indicators.atr,3.0) and (last>=prev or indicators.momentum_1m>0)) if bullish
                          else (recent_move <= -max(0.15*indicators.atr,3.0) and (last<=prev or indicators.momentum_1m<0)))
        checks={"trend_regime_or_persistent_watch_matches_direction":regime_name==expected_regime or (regime_name in {"TRANSITION", "WARMUP"} and watch_aligned),
                "session_bias_not_opposing_or_strong_local_flow_override":session_bias not in ({"BEARISH"} if bullish else {"BULLISH"}) or (writer_change>=8.0 and momentum_aligned),
                "three_minute_momentum_matches_trend":indicators.momentum_3m>0.00015 if bullish else indicators.momentum_3m<-0.00015,
                "one_minute_momentum_not_materially_countertrend":indicators.momentum_1m>=-0.00015 if bullish else indicators.momentum_1m<=0.00015,
                "recent_price_trigger_remains_active":recent_trigger,
                "aggressive_local_writing_confirmed":writer_change>2.5,
                "opposing_divergence_not_overpowering_flow":not opposing or (writer_change>=8.0 and momentum_aligned)}
    else:
        return {**out,"reason":"UNSUPPORTED_MATRIX_SCENARIO"}
    failed=[k for k,v in checks.items() if not v]
    return {**out,"qualified":not failed,
            "reason":"SETUP_SPECIFIC_PRICE_ACTION_RULES_PASSED" if not failed else "SETUP_SPECIFIC_REQUIRED_RULES_FAILED",
            "checks":checks,"failed_checks":failed,"last_completed_close":round(last,2),
            "previous_completed_close":round(prev,2),"boundary":round(level,2),"boundary_buffer_points":round(buffer,2),
            "current_3m_return_pct":round(current_3m*100,4),"prior_3m_return_pct":round(prior_3m*100,4),
            "rsi":round(indicators.rsi,2),"fib_confluence":bool(fib_gate.get("fib_confluence")),
            "local_oi_pair_confirmed":bool(oi_gate.get("qualified")),
            "continuation_price_extension_guard":extension_guard if setup in {"CONTINUOUS_BULLISH_TREND","CONTINUOUS_BEARISH_TREND"} else None,
            "extension_is_diagnostic_not_standalone_veto": setup in {"CONTINUOUS_BULLISH_TREND","CONTINUOUS_BEARISH_TREND"}}
def can_issue_signal_v91(state: Mapping[str, Any], signal: Signal, now: datetime,
                         cooldown_minutes: int, regime: Mapping[str, Any],
                         full_confluence: bool = False,
                         regime_confirmation: Optional[Mapping[str, Any]] = None) -> tuple[bool, str]:
    """Prevent signal churn, but permit a fully confirmed opposite edge reaction after an observed stop."""
    active = state.get("active_signal")
    current = now.astimezone(IST)
    edge_setups = {"SUPPORT_CLUSTER_RECLAIM", "RESISTANCE_CLUSTER_REJECTION",
                   "SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"}
    if isinstance(active, Mapping):
        status = str(active.get("status", "")).upper()
        old_direction = str(active.get("direction", "")).upper()
        terminal = parse_dt(active.get("terminal_timestamp"))
        if status in {"TRACKING", "T1_REACHED"}:
            if old_direction == signal.direction:
                return False, "ACTIVE_SIGNAL_ALREADY_TRACKING_SAME_DIRECTION"
            setup = signal.setup.upper()
            confirmed_flip = setup in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN", "CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"}
            regime_name = str(regime.get("regime", ""))
            regime_aligned = (regime_name == "TREND_BULLISH" and signal.direction == "BULLISH") or (regime_name == "TREND_BEARISH" and signal.direction == "BEARISH")
            if status == "T1_REACHED" and full_confluence and setup in edge_setups and bool((regime_confirmation or {}).get("qualified")):
                return True, "OPPOSITE_STRUCTURAL_REACTION_CONFIRMED_AFTER_T1"
            if not (confirmed_flip and regime_aligned and full_confluence):
                return False, "OPPOSITE_SIGNAL_BLOCKED_UNTIL_T1_OR_CONFIRMED_REGIME_FLIP"
            return True, "STRICT_BREAK_AND_REGIME_FLIP_CONFIRMED"
        if terminal:
            elapsed = (current - terminal.astimezone(IST)).total_seconds() / 60.0
            if elapsed < max(1, cooldown_minutes):
                if old_direction == signal.direction:
                    return False, "SAME_DIRECTION_REENTRY_COOLDOWN"
                terminal_status = status
                # A completed stop can immediately free the tracker for a fully qualified,
                # opposite structural reclaim at a persistent level. This is not a blanket flip bypass.
                just_stopped = terminal_status in {"STOPPED", "TERMINAL"} and elapsed <= 4.0
                if just_stopped and signal.setup.upper() in edge_setups and full_confluence and bool((regime_confirmation or {}).get("qualified")):
                    return True, "OPPOSITE_LEVEL_RECLAIM_CONFIRMED_ON_STOP_EVENT"
                setup = signal.setup.upper()
                name = str(regime.get("regime", ""))
                aligned = (name == "TREND_BULLISH" and signal.direction == "BULLISH") or (name == "TREND_BEARISH" and signal.direction == "BEARISH")
                if not (setup in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN", "CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"} and aligned):
                    return False, "POST_TERMINAL_COOLDOWN_BLOCKS_UNCONFIRMED_FLIP"
    return True, "STRUCTURE_OI_AND_REGIME_GATES_PASSED"



def calculate_risk_plan(signal: Signal, levels: Sequence[Level], indicators: Indicators, min_rr: float) -> RiskPlan:
    """Use structural invalidation and the next credible opposing OI/price barrier for index-level risk."""
    if signal.direction not in {"BULLISH", "BEARISH"} or not finite(signal.level):
        return RiskPlan(False, None, None, None, "", "", None, None, None, "No directional structural trigger.")
    direction = signal.direction
    spot, atr, setup = indicators.spot, indicators.atr, str(signal.setup).upper()
    if not finite(spot) or not finite(atr) or atr <= 0:
        return RiskPlan(False, None, None, None, "", "", None, None, None, "Spot or ATR is unavailable.")

    continuous = setup in {"CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"}
    reliable = [level for level in levels if level.strength >= 0.55 or level.touches >= 2]
    buffer = max(5.0, min(20.0, 0.30 * atr))

    def is_live_writing(level: Level, expected_kind: str) -> bool:
        return (level.kind == expected_kind and str(level.flow_state).upper() == "SHORT_BUILDUP_WRITING"
                and finite(level.oi_change_pct) and number(level.oi_change_pct) > 0.025)

    if continuous:
        sl = spot - 1.5 * atr if direction == "BULLISH" else spot + 1.5 * atr
        stop_source = "INITIAL_ATR_1_5X_TRAILING_STOP"
    else:
        if direction == "BULLISH":
            supports = [level for level in reliable if level.kind == "SUPPORT" and level.price < spot - max(8.0, 0.20 * atr)]
            live_supports = [level for level in supports if is_live_writing(level, "SUPPORT")]
            chosen_supports = live_supports or supports
            protect_candidates = [(level.price, level.source) for level in chosen_supports]
            if signal.level < spot - 0.5:
                protect_candidates.append((signal.level, "SIGNAL_TRIGGER_LEVEL"))
            protect_price, stop_source = (max(protect_candidates, key=lambda item: item[0])
                                          if protect_candidates else (min(indicators.swing_low, spot - atr), "SWING_LOW_FALLBACK"))
            sl = protect_price - buffer
        else:
            resistances = [level for level in reliable if level.kind == "RESISTANCE" and level.price > spot + max(8.0, 0.20 * atr)]
            live_resistances = [level for level in resistances if is_live_writing(level, "RESISTANCE")]
            chosen_resistances = live_resistances or resistances
            protect_candidates = [(level.price, level.source) for level in chosen_resistances]
            if signal.level > spot + 0.5:
                protect_candidates.append((signal.level, "SIGNAL_TRIGGER_LEVEL"))
            protect_price, stop_source = (min(protect_candidates, key=lambda item: item[0])
                                          if protect_candidates else (max(indicators.swing_high, spot + atr), "SWING_HIGH_FALLBACK"))
            sl = protect_price + buffer

    risk = abs(spot - sl)
    max_risk = max(4.0 * atr, 150.0) if not continuous else max(2.0 * atr, 100.0)
    sl_source = stop_source if continuous else f"{stop_source}_PLUS_ATR_BUFFER"
    if not finite(sl) or sl <= 0 or risk < 4 or risk > max_risk:
        return RiskPlan(False, None, None, round(sl, 2) if finite(sl) else None, sl_source,
                        "NEXT_OPPOSING_OI_OR_PRICE_STRUCTURE", None,
                        round(risk, 2) if finite(risk) else None, None,
                        "Stop is invalid or structurally too distant for current volatility.")

    min_t1 = max(1.0 * atr, 25.0)
    if direction == "BULLISH":
        raw_targets = [level for level in reliable if level.kind == "RESISTANCE" and level.price > spot + min_t1]
        dynamic_targets = [level for level in raw_targets if is_live_writing(level, "RESISTANCE")]
        secondary_fib = [level for level in raw_targets if "FIB_UP_EXTENSION" in level.source]
    else:
        raw_targets = [level for level in reliable if level.kind == "SUPPORT" and level.price < spot - min_t1]
        dynamic_targets = [level for level in raw_targets if is_live_writing(level, "SUPPORT")]
        secondary_fib = [level for level in raw_targets if "FIB_DOWN_EXTENSION" in level.source]

    def viable_targets(candidates: Sequence[Level]) -> list[tuple[Level, float, float]]:
        viable: list[tuple[Level, float, float]] = []
        for level in candidates:
            reward = abs(level.price - spot)
            rr = reward / risk if risk > 0 else 0.0
            if reward >= min_t1 and rr >= min_rr:
                viable.append((level, reward, rr))
        viable.sort(key=lambda item: item[0].price if direction == "BULLISH" else -item[0].price)
        return viable

    dynamic_viable = viable_targets(dynamic_targets)
    all_viable = viable_targets(raw_targets)
    fib_viable = viable_targets(secondary_fib)
    # A live opposing writing wall is the preferred target when one offers acceptable risk/reward.
    # Otherwise the nearest credible price structure is used; a target is never fabricated.
    viable = dynamic_viable or all_viable
    if not viable and fib_viable and setup in {"SUPPORT_BOUNCE", "SUPPORT_CLUSTER_RECLAIM", "RESISTANCE_REJECTION", "RESISTANCE_CLUSTER_REJECTION"}:
        viable = fib_viable
    if not viable:
        return RiskPlan(False, None, None, round(sl, 2), sl_source, "NEXT_OPPOSING_OI_OR_PRICE_STRUCTURE",
                        None, round(risk, 2), None,
                        f"No observed target meets distance >= {min_t1:.1f} points and reward/risk >= {min_rr:.2f}; no arbitrary target is substituted.")

    first = viable[0]
    separation = max(0.75 * atr, 25.0)
    # Prefer the next live OI barrier for T2 when it is distinct; otherwise use the next credible structure.
    second_candidates = [item for item in all_viable if abs(item[0].price - first[0].price) >= separation]
    second_candidates.sort(key=lambda item: item[0].price if direction == "BULLISH" else -item[0].price)
    second = second_candidates[0] if second_candidates else None
    if second is not None:
        farther_dynamic = [item for item in dynamic_viable if abs(item[0].price - first[0].price) >= separation]
        if farther_dynamic:
            farther_dynamic.sort(key=lambda item: item[0].price if direction == "BULLISH" else -item[0].price)
            second = farther_dynamic[0]

    explanation = ("Continuous trend uses an initial 1.5x ATR stop that ratchets only in the favourable direction. "
                   if continuous else "Stop follows structural invalidation plus a volatility buffer. ")
    explanation += ("T1 prefers the nearest viable opposing level with live writing OI and compatible premium behaviour; "
                    "T2 uses the next separated qualifying OI/price barrier. "
                    if dynamic_viable else
                    "No qualifying live opposing writing wall passed target checks, so T1/T2 use observed price structure/Fib levels. ")
    if second is None:
        explanation += "T2 unavailable because no sufficiently separated credible second target exists."
    return RiskPlan(True, round(first[0].price, 2), round(second[0].price, 2) if second else None,
                    round(sl, 2), sl_source, "NEXT_OPPOSING_OI_OR_PRICE_STRUCTURE",
                    round(first[1], 2), round(risk, 2), round(first[2], 2), explanation)

def _candidate_strikes(spot: float, contracts: Mapping[tuple[float, str], Contract], direction: str,
                       step: float, fallback_otm: bool = False) -> list[Contract]:
    """Use the NIFTY grid intentionally: ATM, ITM1, ITM2; one-step OTM only on reversal fallback."""
    side = "CE" if direction == "BULLISH" else "PE"
    atm = round_to_grid(spot, step)
    if not finite(atm):
        return []
    if fallback_otm:
        strikes = [atm + step if side == "CE" else atm - step]
    elif side == "CE":
        strikes = [atm, atm - step, atm - 2.0 * step]
    else:
        strikes = [atm, atm + step, atm + 2.0 * step]
    picked = []
    for strike in strikes:
        contract = contracts.get((float(strike), side))
        if contract and contract.instrument_key:
            picked.append(contract)
    return picked


def score_contracts(candidates: Sequence[Contract], quotes: Mapping[str, Quote], spot: float, direction: str,
                    oi: Mapping[str, Any], config: Config, target_delta: float = 0.62,
                    authorized_oi_pair: Optional[Mapping[str, Any]] = None) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]]]:
    """Rank eligible options using the exact authorized paired-flow mode plus safety checks.

    Flow receives 55% of the score and is the primary sort key. Writer-led and buyer-led modes
    use different, explicit option-side roles; neither mode can be scored using unrelated raw OI.
    """
    rows: list[dict[str, Any]] = []
    if not candidates:
        return None, rows
    vol_max = max((c.volume for c in candidates), default=0.0)
    step = config.strike_step
    walls = [w for w in oi.get("walls", []) if isinstance(w, Mapping) and finite(w.get("strike"))]
    bullish = str(direction).upper() == "BULLISH"
    auth = authorized_oi_pair if isinstance(authorized_oi_pair, Mapping) and authorized_oi_pair.get("qualified") else {}
    flow_mode = str(auth.get("flow_mode", "WRITER_COVERING")).upper()
    buyer_mode = flow_mode == "BUYER_LED_MOMENTUM"
    if buyer_mode:
        primary_side, secondary_side = (("call", "put") if bullish else ("put", "call"))
    else:
        primary_side, secondary_side = (("put", "call") if bullish else ("call", "put"))
    auth_primary = auth.get("primary_flow") if isinstance(auth.get("primary_flow"), Mapping) else {}
    auth_secondary = auth.get("secondary_flow") if isinstance(auth.get("secondary_flow"), Mapping) else {}
    authorized_pair_present = bool(auth_primary and auth_secondary
        and finite(auth_primary.get("strike")) and finite(auth_secondary.get("strike"))
        and str(auth_primary.get("option_side", "")).lower() == primary_side
        and str(auth_secondary.get("option_side", "")).lower() == secondary_side)
    auth_primary_strike = number(auth_primary.get("strike"))
    auth_secondary_strike = number(auth_secondary.get("strike"))

    def valid_leg(row: Mapping[str, Any], side: str, role: str) -> Optional[dict[str, Any]]:
        change = number(row.get(f"{side}_change_pct"))
        premium_change = number(row.get(f"{side}_premium_change_pct"))
        base = number(row.get(f"{side}_prev_oi"))
        old_premium = number(row.get(f"{side}_prev_ltp"))
        new_premium = number(row.get(f"{side}_ltp"))
        current_oi = number(row.get(f"{side}_oi"))
        delta_oi = number(row.get(f"{side}_delta_oi"))
        if not all(finite(v) for v in (change, premium_change, base, old_premium, new_premium, current_oi, delta_oi)):
            return None
        if base < 10000 or min(old_premium, new_premium) < 5 or current_oi < 0:
            return None
        flow = classify_oi_flow(change, premium_change)
        if role == "PRIMARY":
            if buyer_mode:
                passed = change > 0.025 and premium_change >= 0.002 and flow == "LONG_BUILDUP_BUYING"
            else:
                passed = change > 0.025 and premium_change <= -0.002 and flow == "SHORT_BUILDUP_WRITING"
        else:
            if buyer_mode:
                passed = change < -0.005 and premium_change <= -0.002 and flow == "LONG_UNWINDING"
            else:
                passed = change < -0.005 and premium_change >= 0.002 and flow == "SHORT_COVERING"
        if not passed:
            return None
        return {"strike": number(row.get("strike")), "flow": flow,
                "oi_change_pct": change * 100.0, "premium_change_pct": premium_change * 100.0,
                "oi_delta": delta_oi, "baseline_oi": base, "current_oi": current_oi}

    def locality(distance: float) -> float:
        return max(0.65, 1.0 - distance / max(1.0, 2.0 * step) * 0.35)

    for c in candidates:
        q = quotes.get(c.instrument_key)
        reasons: list[str] = []
        warnings: list[str] = []
        ltp = q.ltp if q and finite(q.ltp) and q.ltp > 0 else c.ltp
        bid, ask = (q.bid, q.ask) if q and finite(q.bid) and finite(q.ask) and 0 < q.bid <= q.ask else (c.bid, c.ask)
        volume = max(c.volume, q.volume if q else 0.0)
        spread = (ask - bid) / ((ask + bid) / 2.0) if finite(bid) and finite(ask) and 0 < bid <= ask else float("inf")
        delta = c.delta
        if not finite(delta) or delta == 0:
            delta_score = 0.0
            reasons.append("DELTA_UNAVAILABLE")
        else:
            delta_score = clamp(1.0 - abs(abs(delta) - target_delta) / 0.32, 0.0, 1.0)
            if abs(delta) < 0.50 or abs(delta) > 0.85:
                warnings.append("DELTA_OUTSIDE_PREFERRED_RANGE")
        age_ok = bool(q and q.freshness == "FRESH" and finite(q.age_seconds)
                      and -5 <= q.age_seconds <= config.max_quote_age)
        if not age_ok:
            reasons.append("QUOTE_STALE_OR_UNVERIFIED")
        if not finite(ltp) or ltp <= 0:
            reasons.append("INVALID_OPTION_PREMIUM")
        if not finite(spread) or spread > config.max_spread:
            reasons.append("SPREAD_LIMIT_EXCEEDED")
        if volume <= 0:
            reasons.append("NO_OPTION_VOLUME")

        selected_side = "call" if c.side.upper() == "CE" else "put"
        expected_contract_side = primary_side if buyer_mode else secondary_side
        if selected_side != expected_contract_side:
            reasons.append("CONTRACT_SIDE_DOES_NOT_MATCH_AUTHORIZED_FLOW_MODE")
        primary_legs: list[dict[str, Any]] = []
        secondary_legs: list[dict[str, Any]] = []
        for wall in walls:
            distance = abs(number(wall.get("strike")) - c.strike)
            if distance > 2.0 * step + 0.01:
                continue
            primary = valid_leg(wall, primary_side, "PRIMARY")
            secondary = valid_leg(wall, secondary_side, "SECONDARY")
            if authorized_pair_present:
                if abs(number(wall.get("strike")) - auth_primary_strike) > 0.01:
                    primary = None
                if abs(number(wall.get("strike")) - auth_secondary_strike) > 0.01:
                    secondary = None
            if primary:
                primary["distance_to_contract"] = distance
                primary_legs.append(primary)
            if secondary:
                secondary["distance_to_contract"] = distance
                secondary_legs.append(secondary)
        flow_pairs: list[tuple[float, dict[str, Any], dict[str, Any]]] = []
        for primary in primary_legs:
            for secondary in secondary_legs:
                if abs(number(primary.get("strike")) - number(secondary.get("strike"))) > 2.0 * step + 0.01:
                    continue
                primary_locality = locality(number(primary.get("distance_to_contract"), 0.0))
                secondary_locality = locality(number(secondary.get("distance_to_contract"), 0.0))
                primary_intensity = clamp(abs(number(primary.get("oi_change_pct"), 0.0)) / 10.0, 0.0, 1.0)
                secondary_intensity = clamp(abs(number(secondary.get("oi_change_pct"), 0.0)) / 10.0, 0.0, 1.0)
                pair_locality = 0.5 * primary_locality + 0.5 * secondary_locality
                flow_score = clamp(0.25 * pair_locality + 0.55 * primary_intensity + 0.20 * secondary_intensity, 0.0, 1.0)
                flow_pairs.append((flow_score, primary, secondary))
        flow_pairs.sort(key=lambda item: (-item[0],
                                          number(item[1].get("distance_to_contract"), 1e9)
                                          + number(item[2].get("distance_to_contract"), 1e9),
                                          -number(item[1].get("oi_change_pct"), 0.0)))
        supportive_flow_confirmed = bool(flow_pairs) and (authorized_pair_present or not auth)
        if flow_pairs:
            flow_score, chosen_primary, chosen_secondary = flow_pairs[0]
            primary_flow = str(chosen_primary.get("flow"))
            secondary_flow = str(chosen_secondary.get("flow"))
            primary_change = number(chosen_primary.get("oi_change_pct"), 0.0)
            primary_premium_change = number(chosen_primary.get("premium_change_pct"), 0.0)
            flow_reference_strikes = sorted({number(chosen_primary.get("strike")), number(chosen_secondary.get("strike"))})
            flow_distance = round(number(chosen_primary.get("distance_to_contract"), 0.0)
                                  + number(chosen_secondary.get("distance_to_contract"), 0.0), 2)
        else:
            flow_score = 0.0
            primary_flow = secondary_flow = "UNKNOWN"
            primary_change = primary_premium_change = float("nan")
            flow_reference_strikes = []
            flow_distance = None
            reasons.append("NO_NEARBY_PAIRED_SUPPORTIVE_LOCAL_OI_FLOW")

        volume_score = clamp(volume / vol_max, 0.0, 1.0) if vol_max > 0 else 0.0
        spread_score = clamp(1.0 - spread / config.max_spread, 0.0, 1.0) if finite(spread) else 0.0
        depth = q.depth_imbalance if q else 0.0
        liquidity_score = 0.60 * spread_score + 0.25 * volume_score + 0.15 * clamp((depth + 1.0) / 2.0, 0.0, 1.0)
        moneyness_score = clamp(1.0 - abs(spot - c.strike) / (3.0 * step), 0.0, 1.0)
        total = 100.0 * (0.55 * flow_score + 0.15 * delta_score + 0.20 * liquidity_score + 0.10 * moneyness_score)
        hard_ok = (age_ok and finite(ltp) and ltp > 0 and finite(spread) and spread <= config.max_spread
                   and volume > 0 and finite(delta) and 0.45 <= abs(delta) <= 0.90
                   and selected_side == expected_contract_side and supportive_flow_confirmed)
        rows.append({"instrument_key": c.instrument_key, "trading_symbol": c.symbol, "side": c.side,
            "strike": c.strike, "expiry": c.expiry, "ltp": round(ltp, 2) if finite(ltp) else None,
            "delta": round(delta, 4) if finite(delta) else None, "target_abs_delta": round(target_delta, 3),
            "spread_ratio_pct": round(spread * 100.0, 3) if finite(spread) else None,
            "quote_age_seconds": round(q.age_seconds, 2) if q and finite(q.age_seconds) else None,
            "quote_timestamp": q.timestamp if q else None,
            "quote_freshness": q.freshness if q else "UNAVAILABLE", "volume": volume, "oi": c.oi,
            "local_oi_flow": secondary_flow, "supporting_oi_flow": primary_flow,
            "flow_mode": flow_mode,
            "supporting_primary_oi_change_pct": round(primary_change, 3) if finite(primary_change) else None,
            "supporting_primary_premium_change_pct": round(primary_premium_change, 3) if finite(primary_premium_change) else None,
            "oi_reference_strikes": flow_reference_strikes, "oi_reference_distance_points": flow_distance,
            "flow_score_pct": round(flow_score * 100.0, 2), "delta_score_pct": round(delta_score * 100.0, 2),
            "liquidity_score_pct": round(liquidity_score * 100.0, 2), "score": round(total, 2),
            "execution_eligible": bool(hard_ok),
            "score_weights": {"supportive_local_oi_flow": 0.55, "delta": 0.15, "liquidity": 0.20, "moneyness": 0.10},
            "authorized_oi_pair_enforced": bool(authorized_pair_present),
            "warnings": warnings, "vetoes": reasons})
    eligible = [r for r in rows if r["execution_eligible"]]
    eligible.sort(key=lambda x: (-number(x.get("flow_score_pct"), 0.0), -number(x.get("score"), 0.0),
                                 abs(spot - number(x.get("strike"), spot)), number(x.get("spread_ratio_pct"), 999.0)))
    rows.sort(key=lambda x: (-number(x.get("flow_score_pct"), 0.0), -number(x.get("score"), 0.0),
                             abs(spot - number(x.get("strike"), spot))))
    return (eligible[0] if eligible else None), rows

def update_active_signal(state: dict[str, Any], frame: pd.DataFrame, now: datetime) -> list[dict[str, Any]]:
    tracker=state.get("active_signal")
    if not isinstance(tracker,dict) or tracker.get("status") not in {"TRACKING","T1_REACHED"}:return []
    signal_time=parse_dt(tracker.get("signal_timestamp")); levels={name:number(tracker.get(name)) for name in ("T1","T2","SL")}
    if not signal_time:tracker["status"]="INVALID_TRACKER_TIMESTAMP";return []
    bars=completed_candles(frame,now);last_checked=parse_dt(tracker.get("last_checked_candle"))
    boundary=max(signal_time,last_checked) if last_checked else signal_time
    bars=bars.loc[bars["timestamp"]>pd.Timestamp(boundary).tz_convert("UTC")] if not bars.empty else bars
    events=[];direction=str(tracker.get("direction"," ")).upper()
    continuous=bool(tracker.get("trailing_stop_enabled")) or str(tracker.get("setup","")).upper() in {"CONTINUOUS_BULLISH_TREND","CONTINUOUS_BEARISH_TREND"}
    # For a trailing stop, test each candle against the prior stop first, then ratchet for the next candle.
    for idx,(_,bar) in enumerate(bars.iterrows()):
        high,low=number(bar["high"]),number(bar["low"])
        stamp=bar["timestamp"].to_pydatetime().astimezone(IST).isoformat()
        sl_hit=finite(levels["SL"]) and ((low<=levels["SL"]) if direction=="BULLISH" else (high>=levels["SL"]))
        t1_hit=finite(levels["T1"]) and ((high>=levels["T1"]) if direction=="BULLISH" else (low<=levels["T1"]))
        t2_hit=finite(levels["T2"]) and ((high>=levels["T2"]) if direction=="BULLISH" else (low<=levels["T2"]))
        if sl_hit:
            events.append({"type":"STRUCTURAL_STOP_REACHED","timestamp":stamp,"level":levels["SL"],
                           "note":"Stop-first when bar order is unknowable; continuous stop is trailed between completed candles."})
            tracker["status"]="STOPPED";tracker["terminal_timestamp"]=stamp;break
        if t1_hit and not tracker.get("T1_reached"):
            events.append({"type":"T1_REACHED","timestamp":stamp,"level":levels["T1"]})
            tracker["T1_reached"]=True;tracker["status"]="T1_REACHED"
        if t2_hit and not tracker.get("T2_reached"):
            events.append({"type":"T2_REACHED","timestamp":stamp,"level":levels["T2"]})
            tracker["T2_reached"]=True;tracker["status"]="T2_REACHED";tracker["terminal_timestamp"]=stamp;break
        if continuous and finite(levels["SL"]):
            # ATR is estimated only through the just-completed candle; it never loosens the stop.
            history=completed_candles(frame,bar["timestamp"].to_pydatetime().astimezone(IST)+timedelta(minutes=1))
            if len(history)>=2:
                atr_now=number(true_range(history).tail(14).mean())
                close_now=number(bar["close"])
                if finite(atr_now) and atr_now>0 and finite(close_now):
                    candidate=close_now-(1.5*atr_now) if direction=="BULLISH" else close_now+(1.5*atr_now)
                    levels["SL"]=max(levels["SL"],candidate) if direction=="BULLISH" else min(levels["SL"],candidate)
                    tracker["SL"]=round(levels["SL"],2)
                    tracker["trailing_stop_last_updated_at"]=stamp
        tracker["last_checked_candle"]=stamp
    return events
def audit_append(config: Config, report: Mapping[str, Any]) -> None:
    config.audit_dir.mkdir(parents=True, exist_ok=True)
    local_date = parse_date(report.get("timestamp")) or now_ist().date()
    path = config.audit_dir / f"market_scan_{local_date.isoformat()}_v91.jsonl"
    record = {"audit_schema_version": 1, "recorded_at": report.get("timestamp"), "scanner_version": VERSION, "scan": safe_json(report)}
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(record, ensure_ascii=False, separators=(",", ":"), allow_nan=False) + "\n")


def send_email(config: Config, subject: str, body: str) -> bool:
    if not (config.email_sender and config.email_password and config.email_receiver):
        return False
    msg = MIMEMultipart()
    msg["From"], msg["To"], msg["Subject"] = config.email_sender, config.email_receiver, subject
    msg.attach(MIMEText(body, "plain", "utf-8"))
    try:
        if config.smtp_port == 465:
            with smtplib.SMTP_SSL(config.smtp_host, config.smtp_port, timeout=15, context=ssl.create_default_context()) as smtp:
                smtp.login(config.email_sender, config.email_password); smtp.send_message(msg)
        else:
            with smtplib.SMTP(config.smtp_host, config.smtp_port, timeout=15) as smtp:
                smtp.ehlo(); smtp.starttls(context=ssl.create_default_context()); smtp.ehlo()
                smtp.login(config.email_sender, config.email_password); smtp.send_message(msg)
        return True
    except (OSError, smtplib.SMTPException) as exc:
        LOG.error("Email delivery failed (signal remains in state/audit): %s", exc)
        return False


class PredictiveScanner:
    def __init__(self, config: Config, client: Optional[UpstoxClient] = None):
        self.config = config
        self.client = client or UpstoxClient(config)
        self.store = AtomicState(config.state_file)

    def _monitor_active_option(self, state: dict[str, Any], now: datetime) -> dict[str, Any]:
        """Fetch and persist the selected option quote once per scan without replacing stale data."""
        tracker = state.get("active_signal")
        if not isinstance(tracker, dict) or str(tracker.get("status", "")).upper() not in {"TRACKING", "T1_REACHED"}:
            return {"status": "NO_ACTIVE_OPTION_TO_MONITOR"}
        key = str(tracker.get("instrument_key", "")).strip()
        if not key:
            return {"status": "ACTIVE_TRACKER_MISSING_INSTRUMENT_KEY", "signal_timestamp": tracker.get("signal_timestamp")}
        try:
            quote = self.client.quotes([key]).get(key)
        except (ScannerError, requests.RequestException, ValueError) as exc:
            message = f"OPTION_QUOTE_UNAVAILABLE:{type(exc).__name__}:{str(exc)[:180]}"
            tracker["last_option_quote_error"] = message
            tracker["last_option_quote_check_at"] = now.astimezone(IST).isoformat()
            return {"status": "QUOTE_UNAVAILABLE", "instrument_key": key, "reason": message}
        if quote is None:
            return {"status": "QUOTE_MISSING", "instrument_key": key}
        fresh = bool(quote.freshness == "FRESH" and finite(quote.age_seconds)
                     and -5 <= quote.age_seconds <= self.config.max_quote_age and finite(quote.ltp) and quote.ltp > 0)
        result = {"status": "FRESH_QUOTE" if fresh else "STALE_OR_UNVERIFIED_QUOTE",
                  "instrument_key": key, "symbol": tracker.get("symbol"), "strike": tracker.get("strike"),
                  "side": tracker.get("side"), "ltp": round(quote.ltp, 2) if finite(quote.ltp) else None,
                  "bid": round(quote.bid, 2) if finite(quote.bid) else None,
                  "ask": round(quote.ask, 2) if finite(quote.ask) else None,
                  "spread_ratio_pct": round(quote.spread_ratio * 100.0, 3) if finite(quote.spread_ratio) else None,
                  "quote_timestamp": quote.timestamp, "quote_age_seconds": round(quote.age_seconds, 2) if finite(quote.age_seconds) else None,
                  "freshness": quote.freshness}
        tracker["last_option_quote_check_at"] = now.astimezone(IST).isoformat()
        if fresh:
            previous = number(tracker.get("last_option_ltp"), number(tracker.get("initial_option_ltp"), float("nan")))
            tracker["previous_option_ltp"] = previous if finite(previous) else None
            tracker["last_option_ltp"] = round(quote.ltp, 2)
            tracker["last_option_quote_timestamp"] = quote.timestamp
            tracker["last_option_quote_age_seconds"] = round(quote.age_seconds, 2)
            tracker["last_option_bid"] = round(quote.bid, 2) if finite(quote.bid) else None
            tracker["last_option_ask"] = round(quote.ask, 2) if finite(quote.ask) else None
            tracker["last_option_spread_ratio"] = quote.spread_ratio if finite(quote.spread_ratio) else None
            tracker.pop("last_option_quote_error", None)
            if finite(previous) and previous > 0:
                tracker["option_ltp_change_since_previous_scan_pct"] = round((quote.ltp / previous - 1.0) * 100.0, 3)
        else:
            tracker["last_option_quote_warning"] = result["status"]
        return result

    def scan_once(self, now: Optional[datetime] = None) -> dict[str, Any]:
        current = parse_dt(now) if now is not None else now_ist()
        if current is None:
            current = now_ist()
        current = current.astimezone(IST)
        self.store.load(current.date())
        state = self.store.data
        report: dict[str, Any] = {"timestamp": current.isoformat(), "scanner_version": VERSION,
                                  "execution_mode": "SIGNAL_ONLY_NO_ORDER_PLACEMENT", "signal_ready": False,
                                  "selected_option": None, "vetoes": [], "events": [],
                                  "state_file_path": state.get("state_file_path"),
                                  "state_load_status": state.get("state_load_status"),
                                  "state_integrity_ok": state.get("state_integrity_ok", True)}
        try:
            in_market_clock = MARKET_OPEN <= current.time() < MARKET_CLOSE
            if not in_market_clock:
                report.update({"market_state": "OUTSIDE_MARKET", "scenario": "MONITOR_ONLY", "direction": "NEUTRAL",
                               "vetoes": ["OUTSIDE_NSE_MARKET_HOURS"]})
                return self._finish(report, state)
            market_status = self.client.market_status()
            report["market_status"] = market_status
            if market_status != "OPEN":
                report.update({"market_state": "MARKET_CLOSED", "scenario": "MONITOR_ONLY", "direction": "NEUTRAL",
                               "vetoes": [f"UPSTOX_MARKET_STATUS_{market_status}"]})
                return self._finish(report, state)
            expiry = self.client.expiry(state, current.date())
            chain = self.client.chain(expiry)
            rows_by_strike, contracts = chain_to_contracts(chain, expiry)
            strikes = sorted(rows_by_strike)
            strike_step = self.config.strike_step
            diffs = [b-a for a, b in zip(strikes, strikes[1:]) if 1 <= b-a <= 100]
            if diffs:
                # User's NIFTY contract grid is 50 points; only accept observed spacing consistent with that grid.
                observed = float(np.median(diffs))
                strike_step = 50.0 if abs(observed-50.0) <= 1.0 else observed
            index_quote_map = self.client.quotes([self.config.nifty_key])
            index_quote = index_quote_map.get(self.config.nifty_key)
            spot = index_quote.ltp if index_quote and finite(index_quote.ltp) and index_quote.ltp > 0 else float("nan")
            if not finite(spot):
                raise ScannerError("Fresh NIFTY index LTP was not returned; refusing a stale or inferred spot.")
            if not index_quote or index_quote.freshness != "FRESH" or not finite(index_quote.age_seconds) or not (-5 <= index_quote.age_seconds <= self.config.max_quote_age):
                raise ScannerError("NIFTY index quote is stale or its timestamp cannot be verified; refusing to build levels from it.")
            # Current-session index bars drive triggers; cached prior-session bars warm indicators
            # without contaminating current-session momentum or session range measurements.
            frame_raw = self.client.candles(self.config.nifty_key, 1)
            frame = completed_candles(frame_raw, current)
            initial_snapshot = oi_snapshot(chain, expiry, current)
            if frame.empty:
                snaps = state.setdefault("chain_snapshots", [])
                if not snaps or str(snaps[-1].get("timestamp")) != str(initial_snapshot.get("timestamp")):
                    snaps.append(initial_snapshot)
                state["chain_snapshots"] = [x for x in snaps if isinstance(x, dict) and parse_dt(x.get("timestamp"))
                                            and parse_dt(x.get("timestamp")).date() == current.date()][-60:]
                report.update({"market_state": "OPENING_CANDLE_NOT_CLOSED", "scenario": "BASELINE_CAPTURE",
                               "direction": "NEUTRAL", "signal_ready": False, "selected_option": None,
                               "confidence_pct": 0.0, "expiry": expiry,
                               "market_data_quality": {"completed_current_session_candles": 0,
                                                        "oi_snapshot_persisted": True,
                                                        "reason": "No completed current-session candle yet; no synthetic price trigger is inferred."},
                               "vetoes": ["NO_COMPLETED_CURRENT_SESSION_CANDLE"]})
                return self._finish(report, state)

            latest_candle_time = frame["timestamp"].iloc[-1].to_pydatetime().astimezone(IST)
            candle_age_seconds = (current - latest_candle_time).total_seconds()
            if candle_age_seconds < -5 or candle_age_seconds > self.config.max_candle_age:
                raise ScannerError(f"Latest completed NIFTY candle is stale or future-dated (age={candle_age_seconds:.1f}s; limit={self.config.max_candle_age:.1f}s).")

            # Cache prior-session one-minute candles across short-lived GitHub Actions runs.
            history_records = state.get("historical_context", []) if isinstance(state.get("historical_context"), list) else []
            history_ok = (state.get("historical_context_date") == current.date().isoformat()
                          and state.get("historical_context_instrument_key") == self.config.nifty_key
                          and bool(history_records))
            if not history_ok:
                history_frame = pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
                try:
                    history_frame = self.client.historical_candles(
                        self.config.nifty_key, 1, current.date() - timedelta(days=1), current.date() - timedelta(days=8))
                    if not history_frame.empty:
                        history_frame = history_frame.loc[
                            history_frame["timestamp"].dt.tz_convert(IST).dt.date < current.date()].reset_index(drop=True)
                    history_records = frame_to_records(history_frame, limit=3500)
                except (ScannerError, requests.RequestException, ValueError) as history_exc:
                    LOG.warning("Prior-session indicator context unavailable; current-session structure remains active: %s", history_exc)
                    history_records = []
                state["historical_context"] = history_records
                state["historical_context_date"] = current.date().isoformat()
                state["historical_context_instrument_key"] = self.config.nifty_key
            history_frame = records_to_frame(history_records)
            if not history_frame.empty:
                history_dates = history_frame["timestamp"].dt.tz_convert(IST).dt.date
                history_frame = history_frame.loc[history_dates < current.date()].reset_index(drop=True)
            analysis_parts = [part for part in (history_frame, frame_raw) if isinstance(part, pd.DataFrame) and not part.empty]
            analysis_raw = (pd.concat(analysis_parts, ignore_index=True).sort_values("timestamp")
                            .drop_duplicates("timestamp", keep="last").reset_index(drop=True)
                            if analysis_parts else frame_raw)

            # NIFTY spot has no meaningful traded volume. Use the configured active futures
            # contract for VWAP; do not substitute index volume or guessed futures symbols.
            futures_frame_raw = None
            futures_vwap_warning = None
            if self.config.futures_key:
                try:
                    futures_frame_raw = self.client.candles(self.config.futures_key, 1)
                except (ScannerError, requests.RequestException, ValueError) as futures_exc:
                    futures_vwap_warning = f"FUTURES_VWAP_UNAVAILABLE:{type(futures_exc).__name__}:{str(futures_exc)[:180]}"
                    LOG.warning("NIFTY futures VWAP input unavailable: %s", futures_exc)
            else:
                futures_vwap_warning = "NIFTY_FUTURES_INSTRUMENT_KEY_NOT_CONFIGURED"

            snapshots = state.get("chain_snapshots", []) if isinstance(state.get("chain_snapshots", []), list) else []
            oi = analyze_oi(chain, snapshots, spot, expiry, current, strike_step, self.config.scan_interval)
            # Calculate every available price indicator before OI qualification. This allows the
            # buyer-led momentum path to require aligned price context without making OI gate the
            # calculation of price structure, momentum, divergence or Fibonacci.
            indicators = indicator_set(analysis_raw, spot, current, calculate_rsi=True, vwap_frame=futures_frame_raw)
            fib = analyze_fibonacci(analysis_raw, indicators.atr, current)
            # Divergence is an intraday trigger; do not compare pivots across an overnight gap.
            divergence = detect_rsi_divergence(frame_raw, indicators.atr, current)
            levels = make_structure_levels(analysis_raw, indicators, oi, strike_step, current, fib)
            regime = classify_market_regime(frame_raw, indicators, current)
            regime["scan_timestamp"] = current.isoformat()
            oi_first = qualify_oi_first(oi, spot, strike_step, self.config.min_local_oi_change_pct,
                                        indicators=indicators, regime=regime)
            directional_watch_diagnostics = update_directional_watch(state, frame_raw, indicators, regime, oi_first, current)
            regime["directional_watch"] = safe_json(state.get("directional_watch")) if isinstance(state.get("directional_watch"), Mapping) else {}
            signal, signal_diagnostics = score_market_signal(frame_raw, indicators, oi, levels, current,
                                                              self.config.min_signal_score, strike_step, fib, divergence,
                                                              regime=regime, oi_first=oi_first, min_rr=self.config.min_t1_rr)
            if oi_first.get("qualified"):
                signal, structure_watch_resolution = resolve_pending_structure_watch(state, signal, indicators, current)
            else:
                structure_watch_resolution = {"status": "NOT_EVALUATED_OI_FIRST_GATE", "reason": oi_first.get("reason")}
            expiry_pin = diagnose_expiry_pin(oi, fib, indicators, expiry, current, strike_step,
                                             self.config.min_local_oi_change_pct)
            if expiry_pin.get("detected"):
                state.pop("pending_structure_setup", None)
                structure_watch_resolution = {"status": "DISCARDED", "reason": "EXPIRY_PIN_NO_ENTRY"}
                signal = Signal("NEUTRAL", "RANGE_BOUND_EXPIRY_PIN", 0.0, 0.0,
                                "No Entry - Range-Bound / Expiry Pin", None,
                                tuple(list(signal.evidence) + ["EXPIRY_PIN_SAME_STRIKE_CALL_PUT_WRITING"]),
                                ("No Entry - Range-Bound / Expiry Pin",))
            local_oi_confirmation = qualify_local_oi(oi, signal, spot, strike_step, self.config.min_local_oi_change_pct)
            fib_divergence_confirmation = qualify_fib_divergence(signal, regime, fib, divergence, spot, indicators.atr)
            setup_confirmation = qualify_setup_rules(signal, frame_raw, indicators, regime,
                                                     fib_divergence_confirmation, local_oi_confirmation, current)
            regime_confirmation = qualify_regime(signal, regime, indicators, spot,
                                                 fib_divergence_confirmation, local_oi_confirmation, setup_confirmation)
            raw_signal = signal
            structure_watch_update = {"status": "NOT_APPLICABLE"}
            watchable_setups = {"SUPPORT_CLUSTER_RECLAIM", "RESISTANCE_CLUSTER_REJECTION",
                                "SUPPORT_BOUNCE", "RESISTANCE_REJECTION"}
            if raw_signal.direction in {"BULLISH", "BEARISH"} and raw_signal.setup in watchable_setups:
                structure_watch_update = persist_structure_watch(state, raw_signal, current, local_oi_confirmation)
            gate_failures = []
            if not bool(state.get("state_integrity_ok", True)):
                gate_failures.append("CANONICAL_STATE_CORRUPT_OR_UNREADABLE_ENTRIES_SUPPRESSED_FOR_RECOVERY_SCAN")
            if signal.direction in {"BULLISH", "BEARISH"}:
                if expiry_pin.get("detected"):
                    gate_failures.append("No Entry - Range-Bound / Expiry Pin")
                if not local_oi_confirmation.get("qualified"):
                    gate_failures.append(str(local_oi_confirmation.get("reason", "LOCAL_OI_GATE_FAILED")))
                if not regime_confirmation.get("qualified"):
                    gate_failures.append(str(regime_confirmation.get("reason", "REGIME_GATE_FAILED")))
                if not fib_divergence_confirmation.get("qualified"):
                    gate_failures.append(str(fib_divergence_confirmation.get("reason", "FIB_DIVERGENCE_GATE_FAILED")))
                if not setup_confirmation.get("qualified"):
                    gate_failures.append(str(setup_confirmation.get("reason", "SETUP_RULE_GATE_FAILED")))
                if gate_failures:
                    gate_evidence = tuple(dict.fromkeys(list(signal.evidence) + [f"V91_HARD_GATE:{x}" for x in gate_failures]))
                    signal = Signal("NEUTRAL", "V91_ENTRY_GATES_BLOCKED", signal.score, 0.0,
                                    "; ".join(gate_evidence[:8]), signal.level, gate_evidence, tuple(gate_failures))
            risk = calculate_risk_plan(signal, levels, indicators, self.config.min_t1_rr)
            events = update_active_signal(state, frame_raw, current)
            report["events"].extend(events)
            report["active_option_monitor"] = self._monitor_active_option(state, current)
            if events:
                event_tracker = dict(state.get("active_signal") or {})
                report["_pending_event_notifications"] = [{**event, "_tracker": event_tracker.copy()} for event in events]
            direction = signal.direction
            watch_direction = str((state.get("directional_watch") or {}).get("direction", "NEUTRAL")).upper() if isinstance(state.get("directional_watch"), Mapping) else "NEUTRAL"
            report.update({
                "market_state": "DIRECTIONAL_SETUP" if direction != "NEUTRAL" else "DIRECTIONAL_WATCH" if watch_direction in {"BULLISH", "BEARISH"} else "WATCH",
                "scenario": signal.setup, "direction": direction, "confidence_pct": signal.confidence_pct,
                "trigger": signal.trigger, "signal_evidence": list(signal.evidence), "signal_blockers": list(signal.blockers),
                "indicators": safe_json(asdict(indicators)), "structure_levels": [safe_json(asdict(l)) for l in levels],
                "oi_analysis": {k: safe_json(v) for k, v in oi.items() if k != "snapshot"},
                "signal_diagnostics": signal_diagnostics, "risk_plan": safe_json(asdict(risk)),
                "market_regime": regime, "local_oi_confirmation": local_oi_confirmation,
                "regime_confirmation": regime_confirmation,
                "setup_rule_confirmation": setup_confirmation,
                "fibonacci_analysis": safe_json(fib), "rsi_divergence": safe_json(divergence),
                "fib_divergence_confirmation": safe_json(fib_divergence_confirmation),
                "expiry_pin_diagnostics": safe_json(expiry_pin),
                "directional_watch": {"diagnostics": directional_watch_diagnostics,
                                      "active": safe_json(state.get("directional_watch"))},
                "structure_watch": {"resolution": structure_watch_resolution, "update": structure_watch_update,
                                    "active": safe_json(state.get("pending_structure_setup")),
                                    "ttl_minutes": STRUCTURE_WATCH_TTL_MINUTES,
                                    "max_extension_atr": STRUCTURE_WATCH_MAX_EXTENSION_ATR},
                "v91_policy": {"price_analysis_runs_independently_of_oi_gate": True, "persistent_setup_state": True,
                               "local_writing_oi_change_min_pct_exclusive": self.config.min_local_oi_change_pct,
                               "paired_covering_oi_decline_min_pct_exclusive": 0.5,
                               "expiry_pin": "NO_ENTRY_WHEN_EXPIRY_PIN_CONFIRMED",
                               "reversal_fib_rule": "BULLISH_FIB_50_61_8;BEARISH_FIB_61_8_OR_100;MATCHING_CONFIRMED_RSI_DIVERGENCE",
                               "breakout_breakdown_divergence_policy": "ONLY_CONFIRMED_OPPOSING_DIVERGENCE_VETOES; UNAVAILABLE_DIVERGENCE_IS_NOT_A_VETO",
                               "oi_flow_requires_premium_confirmation": True,
                               "trend_countertrend_entries": "PRICE_STRUCTURE_CONTINUOUS;ENTRY_REQUIRES_STRICT_LOCAL_OI;CONTINUATION_FIB_PROXIMITY_IS_CONTEXT_NOT_VETO",
                               "sideways_whipsaw_entries": "PERSISTENT_RANGE_EDGE_RECLAIM_WITH_STRICT_LOCAL_OI_ALLOWED;MIDRANGE_CHASE_BLOCKED",
                               "opposite_signal_lifecycle": "CONFIRMED_BREAK_AND_REGIME_ALIGNMENT_REQUIRED_WHILE_TRACKING_OR_AFTER_T1",
                               "same_direction_reentry_cooldown_minutes": self.config.reentry_cooldown_minutes},
                "oi_first_gate": oi_first,
                "candidate_before_v91_gates": _candidate_before_audit(raw_signal, signal_diagnostics),
                "v91_gate_failures": gate_failures,
                "active_signal": safe_json(state.get("active_signal")), "expiry": expiry,
                "state_integrity": {"ok": bool(state.get("state_integrity_ok", True)),
                                     "load_status": state.get("state_load_status"),
                                     "snapshots_available": len(state.get("chain_snapshots", [])),
                                     "state_path": state.get("state_file_path")},
                "market_data_quality": {"index_quote_freshness": index_quote.freshness if index_quote else "UNAVAILABLE",
                                        "index_quote_age_seconds": index_quote.age_seconds if index_quote else None,
                                        "completed_1m_candles": len(frame), "historical_context_candles": len(history_frame), "last_completed_candle_timestamp": latest_candle_time.isoformat(),
                                        "last_completed_candle_age_seconds": round(candle_age_seconds, 2),
                                        "volume_source": indicators.volume_source, "futures_instrument_key": self.config.futures_key or None,
                                        "futures_vwap_warning": futures_vwap_warning,
                                        "same_session_tactical_oi_available": oi["tactical_available"]},
            })
            if expiry_pin.get("detected"):
                report["vetoes"].append("No Entry - Range-Bound / Expiry Pin")
                report["suppress_signal_email"] = True
            elif current.time() < ENTRY_OPEN:
                report["vetoes"].append("BEFORE_ENTRY_WINDOW")
            elif current.time() >= ENTRY_CUTOFF:
                report["vetoes"].append("ENTRY_CUTOFF_15_15_MONITOR_ONLY")
            elif direction == "NEUTRAL":
                if raw_signal.direction in {"BULLISH", "BEARISH"}:
                    if gate_failures:
                        report["vetoes"].extend(gate_failures)
                    else:
                        report["vetoes"].append("DIRECTIONAL_CANDIDATE_BLOCKED_BY_SCORE_RISK_OR_LIFECYCLE")
                else:
                    if signal_diagnostics.get("generated_candidate_count", 0) > 0:
                        report["vetoes"].append("ALL_PRICE_ACTION_CANDIDATES_REJECTED_BY_FULL_GATES")
                        failures = signal_diagnostics.get("candidate_gate_failures_summary", {})
                        if isinstance(failures, Mapping):
                            report["vetoes"].extend(
                                f"CANDIDATE_GATE_FAILED:{name}:{count}"
                                for name, count in sorted(failures.items(), key=lambda item: (-item[1], item[0]))[:6]
                            )
                    else:
                        report["vetoes"].append("NO_QUALIFYING_PRICE_ACTION")
            elif signal.score < self.config.min_signal_score:
                report["vetoes"].append("MARKET_SETUP_SCORE_BELOW_THRESHOLD")
            elif not risk.valid:
                report["vetoes"].append(f"STRUCTURAL_RISK_PLAN_INVALID:{risk.reason}")
            else:
                allowed, allow_reason = can_issue_signal_v91(
                    state, signal, current, self.config.reentry_cooldown_minutes, regime,
                    full_confluence=not gate_failures, regime_confirmation=regime_confirmation)
                report["active_signal_gate"] = {"allowed": allowed, "reason": allow_reason}
                if not allowed:
                    report["vetoes"].append(allow_reason)
                else:
                    candidates = _candidate_strikes(spot, contracts, direction, strike_step)
                    # Keep strike choice near the same local OI cluster that authorized the setup.
                    reference_strikes = local_oi_confirmation.get("reference_strikes", [])
                    if reference_strikes:
                        matched = [c for c in candidates if any(abs(c.strike - number(x, 1e9)) <= 2.0 * strike_step for x in reference_strikes)]
                        if matched:
                            candidates = matched
                        else:
                            report["vetoes"].append("NO_CONTRACT_WITHIN_2_STRIKES_OF_QUALIFYING_LOCAL_OI_CLUSTER")
                            candidates = []
                    candidate_keys = [c.instrument_key for c in candidates]
                    option_quotes = self.client.quotes(candidate_keys) if candidate_keys else {}
                    # Near-ATM reversals may use target delta ~0.55; established continuation
                    # uses a higher delta for closer underlying tracking.
                    reversal_setups = {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION",
                                       "SUPPORT_CLUSTER_RECLAIM", "RESISTANCE_CLUSTER_REJECTION"}
                    target_delta = 0.55 if signal.setup in reversal_setups else 0.62
                    selected, ranked = score_contracts(candidates, option_quotes, spot, direction, oi, self.config, target_delta,
                                                      authorized_oi_pair=local_oi_confirmation)
                    candidate_diagnostics = [{**row, "route": "ATM_ITM1_ITM2"} for row in ranked]
                    if not selected and signal.setup in reversal_setups:
                        fallback = _candidate_strikes(spot, contracts, direction, strike_step, fallback_otm=True)
                        if reference_strikes:
                            fallback = [c for c in fallback if any(abs(c.strike - number(x, 1e9)) <= 2.0 * strike_step for x in reference_strikes)]
                        fallback_keys = [c.instrument_key for c in fallback]
                        fallback_quotes = self.client.quotes(fallback_keys) if fallback_keys else {}
                        fallback_selected, fallback_ranked = score_contracts(fallback, fallback_quotes, spot, direction, oi, self.config, target_delta,
                                                                    authorized_oi_pair=local_oi_confirmation)
                        candidate_diagnostics.extend([{**row, "route": "SINGLE_OTM_REVERSAL_FALLBACK"} for row in fallback_ranked])
                        if fallback_selected:
                            selected = fallback_selected
                    report["candidate_diagnostics"] = candidate_diagnostics
                    if not selected:
                        report["vetoes"].append("NO_ATM_ITM_CONTRACT_PASSED;REVERSAL_OTM_FALLBACK_UNAVAILABLE_OR_FAILED" if signal.setup in reversal_setups else "NO_ATM_ITM_CONTRACT_PASSED_QUOTE_SPREAD_VOLUME_AND_DELTA_GATES")
                    else:
                        report["signal_ready"] = True
                        report["selected_option"] = selected
                        event_key = f"{current.date()}|{direction}|{selected['strike']}|{selected['side']}|{risk.t1}|{risk.sl}"
                        tracker = {
                            "signal_timestamp": current.isoformat(), "direction": direction, "setup": signal.setup,
                            "confidence_pct": signal.confidence_pct, "spot": spot,
                            "instrument_key": selected["instrument_key"], "symbol": selected["trading_symbol"],
                            "strike": selected["strike"], "side": selected["side"], "expiry": expiry,
                            "T1": risk.t1, "T2": risk.t2, "SL": risk.sl,
                            "initial_option_ltp": selected.get("ltp"), "last_option_ltp": selected.get("ltp"),
                            "last_option_quote_timestamp": selected.get("quote_timestamp"),
                            "last_option_quote_age_seconds": selected.get("quote_age_seconds"),
                            "last_option_bid": selected.get("bid"), "last_option_ask": selected.get("ask"),
                            "last_option_spread_ratio": (number(selected.get("spread_ratio_pct")) / 100.0
                                                          if finite(selected.get("spread_ratio_pct")) else None),
                            "status": "TRACKING", "T1_reached": False, "T2_reached": False,
                            "trailing_stop_enabled": signal.setup in {"CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"},
                            "trailing_stop_atr_multiple": 1.5 if signal.setup in {"CONTINUOUS_BULLISH_TREND", "CONTINUOUS_BEARISH_TREND"} else None,
                            "last_checked_candle": current.isoformat(), "event_key": event_key,
                        }
                        prior = state.get("active_signal")
                        if isinstance(prior, dict):
                            hist = state.setdefault("signal_history", [])
                            hist.append(prior); state["signal_history"] = hist[-20:]
                        state["active_signal"] = tracker
                        state.pop("pending_structure_setup", None)
                        structure_watch_update = {"status": "CONSUMED_BY_FINAL_SELECTION", "level": round(number(signal.level), 2) if finite(signal.level) else None}
                        report["_pending_signal_email"] = {"selected": selected, "signal": signal, "risk": risk, "now": current}
                        report["email_status"] = "PENDING_STATE_SAVE"
                        report["active_signal"] = safe_json(tracker)
                        report["active_option_monitor"] = {"status": "INITIAL_QUOTE_CAPTURED",
                            "instrument_key": selected.get("instrument_key"), "symbol": selected.get("trading_symbol"),
                            "strike": selected.get("strike"), "side": selected.get("side"),
                            "ltp": selected.get("ltp"), "quote_timestamp": selected.get("quote_timestamp"),
                            "quote_age_seconds": selected.get("quote_age_seconds"),
                            "freshness": selected.get("quote_freshness")}
            # Append only snapshots that represent a valid chain, and cap memory/state size.
            if chain:
                snaps = state.setdefault("chain_snapshots", [])
                snap = oi["snapshot"]
                if not snaps or str(snaps[-1].get("timestamp")) != str(snap.get("timestamp")):
                    snaps.append(snap)
                state["chain_snapshots"] = [s for s in snaps if isinstance(s, dict) and parse_dt(s.get("timestamp")) and parse_dt(s.get("timestamp")).date() == current.date()][-40:]
            report["strike_grid"] = {"step_points": strike_step, "nearby_available_strikes": [s for s in strikes if abs(s-spot) <= 300]}
            report["risk_disclaimer"] = "Rule-based scenario score is a ranking heuristic, not a calibrated probability or guarantee. Scanner provides signal research only; it places no orders. Price-action watch paths and the >2.5% local-OI rule require multi-session replay before any expectancy claim."
            return self._finish(report, state)
        except Exception as exc:
            # The scan boundary is fail-closed: an unforeseen provider/schema error must not create a selection.
            LOG.exception("V91 scan failed safely")
            report.update({"market_state": "DATA_OR_SCAN_ERROR", "scenario": "NO_SELECTION", "direction": "NEUTRAL",
                           "signal_ready": False, "selected_option": None, "confidence_pct": 0.0,
                           "vetoes": [f"SCAN_ERROR:{type(exc).__name__}:{str(exc)[:350]}"]})
            report.pop("_pending_signal_email", None)
            return self._finish(report, state)

    def _signal_notification(self, report: Mapping[str, Any], selected: Mapping[str, Any],
                             signal: Signal, risk: RiskPlan, now: datetime,
                             tracker: Mapping[str, Any]) -> Optional[dict[str, Any]]:
        pin_diag=report.get("expiry_pin_diagnostics") if isinstance(report.get("expiry_pin_diagnostics"),Mapping) else {}
        if report.get("suppress_signal_email") or pin_diag.get("detected"):
            return None
        event_key=str(tracker.get("event_key",""))
        subject=f"NIFTY V91 {signal.direction}: {selected['strike']:.0f}{selected['side']}"
        spot_value=number(report.get("indicators",{}).get("spot")) if isinstance(report.get("indicators"),Mapping) else float("nan")
        spot_text=f"{spot_value:.2f}" if finite(spot_value) else "Unavailable"
        strike_value=number(selected.get("strike")); strike_text=f"{strike_value:.0f}" if finite(strike_value) else "Unavailable"
        ltp_value=number(selected.get("ltp")); ltp_text=f"{ltp_value:.2f}" if finite(ltp_value) else "Unavailable"
        score_text=f"{number(signal.confidence_pct,0.0):.1f}"
        t1_text=f"{number(risk.t1):.2f}" if finite(risk.t1) else "Unavailable"
        t2_text=f"{number(risk.t2):.2f}" if finite(risk.t2) else "Unavailable"
        sl_text=f"{number(risk.sl):.2f}" if finite(risk.sl) else "Unavailable"
        body=(f"Nifty Spot Price: {spot_text}\n"
              f"Time (IST): {now.astimezone(IST).strftime('%Y-%m-%d %H:%M:%S')}\n"
              f"Strike Selected: {strike_text} {selected.get('side','')}\n"
              f"Confidance: {score_text}%\n"
              f"Strike Selected Price: {ltp_text}\n"
              f"T1: {t1_text}\n"
              f"T2: {t2_text}\n"
              f"SL: {sl_text}")
        return {"notification_key":f"SIGNAL|{event_key}","kind":"SIGNAL","event_key":event_key,
                "created_at":now.astimezone(IST).isoformat(),"subject":subject,"body":body}
    def _event_notification(self, event: Mapping[str, Any]) -> Optional[dict[str, Any]]:
        tracker = event.get("_tracker") if isinstance(event.get("_tracker"), dict) else {}
        if not tracker:
            return None
        event_type = str(event.get("type", "EVENT"))
        timestamp = str(event.get("timestamp", ""))
        event_key = str(tracker.get("event_key", ""))
        key = f"EVENT|{event_key}|{event_type}|{timestamp}"
        subject = f"NIFTY V91 {event_type}: {tracker.get('strike')}{tracker.get('side')}"
        body = (f"Time (IST): {timestamp}\nEvent: {event_type}\nDirection: {tracker.get('direction')}\n"
                f"Strike: {tracker.get('strike')} {tracker.get('side')}\nLevel: {event.get('level')}\n"
                f"Original T1/T2/SL: {tracker.get('T1')} / {tracker.get('T2')} / {tracker.get('SL')}\n"
                "Signal only: no order was placed.")
        return {"notification_key": key, "kind": "EVENT", "event_key": event_key,
                "created_at": timestamp, "subject": subject, "body": body}

    def _finish(self, report: dict[str, Any], state: dict[str, Any]) -> dict[str, Any]:
        state["last_scan_timestamp"] = report.get("timestamp")
        pending_events = report.pop("_pending_event_notifications", [])
        pending_signal = report.pop("_pending_signal_email", None)
        if report.get("suppress_signal_email"):
            existing_queue = state.get("pending_email_notifications", [])
            if isinstance(existing_queue, list):
                state["pending_email_notifications"] = [x for x in existing_queue
                    if not (isinstance(x, dict) and x.get("kind") == "SIGNAL")]
        has_email_config = bool(self.config.email_sender and self.config.email_password and self.config.email_receiver)
        current_signal_key = ""
        current_event_keys: set[str] = set()
        if has_email_config:
            queue = state.get("pending_email_notifications", [])
            if not isinstance(queue, list):
                queue = []
            if report.get("suppress_signal_email"):
                # Expiry pin invalidates pending entry notifications; event lifecycle notices remain eligible.
                queue = [x for x in queue if not (isinstance(x, dict) and x.get("kind") == "SIGNAL")]
            known_keys = {str(x.get("notification_key", "")) for x in queue if isinstance(x, dict)}
            emailed = set(str(x) for x in state.get("emailed_notification_keys", []) if isinstance(x, str))
            for event in pending_events if isinstance(pending_events, list) else []:
                if not isinstance(event, dict):
                    continue
                item = self._event_notification(event)
                if item and item["notification_key"] not in emailed and item["notification_key"] not in known_keys:
                    queue.append(item); known_keys.add(item["notification_key"]); current_event_keys.add(item["notification_key"])
            if isinstance(pending_signal, dict) and report.get("signal_ready"):
                active = state.get("active_signal") if isinstance(state.get("active_signal"), dict) else {}
                item = self._signal_notification(report, pending_signal["selected"], pending_signal["signal"],
                                                 pending_signal["risk"], pending_signal["now"], active)
                if item is not None:
                    current_signal_key = item["notification_key"]
                    if current_signal_key not in emailed and current_signal_key not in known_keys:
                        queue.append(item); known_keys.add(current_signal_key)
            state["pending_email_notifications"] = queue[-100:]
        elif isinstance(pending_signal, dict):
            report["email_status"] = "NOT_CONFIGURED"

        state_saved = True
        try:
            self.store.save()
        except OSError as exc:
            state_saved = False
            LOG.error("State save failed: %s", exc)
            report.setdefault("vetoes", []).append(f"STATE_SAVE_FAILED:{exc}")
            # A selection without durable tracking is not released to the user.
            if report.get("signal_ready"):
                report["signal_ready"] = False
                report["selected_option"] = None
                report["market_state"] = "DATA_OR_SCAN_ERROR"
                report["email_status"] = "SUPPRESSED_STATE_SAVE_FAILED"

        sent_now: set[str] = set()
        if state_saved and has_email_config:
            queue = state.get("pending_email_notifications", [])
            remaining = []
            emailed = state.setdefault("emailed_notification_keys", [])
            emailed_set = set(str(x) for x in emailed if isinstance(x, str))
            for item in queue if isinstance(queue, list) else []:
                if not isinstance(item, dict):
                    continue
                key = str(item.get("notification_key", ""))
                if not key or key in emailed_set:
                    continue
                if send_email(self.config, str(item.get("subject", "NIFTY V91 notification")), str(item.get("body", ""))):
                    emailed.append(key); emailed_set.add(key); sent_now.add(key)
                    if item.get("kind") == "SIGNAL":
                        state["last_email_key"] = str(item.get("event_key", ""))
                    elif item.get("kind") == "EVENT":
                        sent_events = state.setdefault("emailed_event_keys", [])
                        sent_events.append(key); state["emailed_event_keys"] = sent_events[-100:]
                else:
                    # Keep failed deliveries so a later scan can retry without recreating the signal.
                    remaining.append(item)
            state["pending_email_notifications"] = remaining[-100:]
            state["emailed_notification_keys"] = emailed[-200:]
            try:
                self.store.save()
            except OSError as exc:
                LOG.error("State save after notification attempts failed: %s", exc)
            report["pending_email_notifications"] = len(state.get("pending_email_notifications", []))
            if isinstance(pending_signal, dict) and not report.get("suppress_signal_email"):
                if current_signal_key in sent_now or current_signal_key in state.get("emailed_notification_keys", []):
                    report["email_status"] = "SENT"
                elif any(isinstance(x, dict) and x.get("notification_key") == current_signal_key for x in state.get("pending_email_notifications", [])):
                    report["email_status"] = "PENDING_RETRY"
                else:
                    report["email_status"] = "NOT_SENT"
            if current_event_keys:
                report["event_email_status"] = {"queued_or_sent": len(current_event_keys),
                                                  "sent_this_scan": len(current_event_keys & sent_now),
                                                  "pending_retry": len(current_event_keys - sent_now)}
        elif not has_email_config:
            report["pending_email_notifications"] = len(state.get("pending_email_notifications", []))

        try:
            audit_append(self.config, report)
        except OSError as exc:
            LOG.error("Audit append failed: %s", exc)
            report.setdefault("vetoes", []).append(f"AUDIT_WRITE_FAILED:{exc}")
        return report


def _candidate_before_audit(raw_signal: Signal, diagnostics: Mapping[str, Any]) -> dict[str, Any]:
    """Preserve the best rejected candidate and explicit failure reasons in every audit."""
    base = {"direction": raw_signal.direction, "setup": raw_signal.setup,
            "score": raw_signal.score, "trigger": raw_signal.trigger,
            "qualification_status": "RAW_SIGNAL"}
    evaluations = diagnostics.get("candidate_gate_evaluations", []) if isinstance(diagnostics, Mapping) else []
    if raw_signal.direction == "NEUTRAL" and isinstance(evaluations, list) and evaluations:
        ranked = sorted(evaluations, key=lambda x: (-number(x.get("score"), 0.0), number(x.get("distance_points"), 99999)))
        candidate = ranked[0]
        return {"direction": candidate.get("direction"), "setup": candidate.get("setup"),
                "score": candidate.get("score"), "trigger": candidate.get("level"),
                "qualification_status": "REJECTED_BY_FULL_ENTRY_GATES",
                "failed_checks": candidate.get("failed_checks", []),
                "local_oi_reason": candidate.get("local_oi_reason"),
                "fib_reason": candidate.get("fib_reason"),
                "setup_reason": candidate.get("setup_reason"),
                "regime_reason": candidate.get("regime_reason"),
                "risk_reason": candidate.get("risk_reason")}
    return base


def print_report(report: Mapping[str, Any]) -> None:
    """Print one compact workflow line; the detailed per-scan audit remains in JSONL."""
    ts = str(report.get("timestamp", ""))
    indicators = report.get("indicators", {}) if isinstance(report.get("indicators"), Mapping) else {}
    selected = report.get("selected_option") if isinstance(report.get("selected_option"), Mapping) else None
    regime = report.get("market_regime", {}) if isinstance(report.get("market_regime"), Mapping) else {}
    oi_gate = report.get("local_oi_confirmation", {}) if isinstance(report.get("local_oi_confirmation"), Mapping) else {}
    risk = report.get("risk_plan", {}) if isinstance(report.get("risk_plan"), Mapping) else {}
    vetoes = report.get("vetoes", []) if isinstance(report.get("vetoes"), list) else []
    payload = {
        "time_ist": ts,
        "state": report.get("market_state"),
        "setup": report.get("scenario"),
        "direction": report.get("direction"),
        "spot": number(indicators.get("spot")) if finite(indicators.get("spot")) else None,
        "regime": regime.get("regime"),
        "local_oi": "CONFIRMED" if oi_gate.get("qualified") else oi_gate.get("reason", "NOT_EVALUATED"),
        "selection": (f"{selected.get('strike'):.0f}{selected.get('side')}" if selected and finite(selected.get("strike")) else None),
        "T1": risk.get("t1"), "T2": risk.get("t2"), "SL": risk.get("sl"),
        "reason": (str(vetoes[0])[:120] if vetoes else str(report.get("trigger", ""))[:120]),
    }
    print(json.dumps(safe_json(payload), separators=(",", ":"), ensure_ascii=False, allow_nan=False))



def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="V91 persistent-structure NIFTY options scanner (signal only)")
    parser.add_argument("--loop", action="store_true", help="run continuously at SCAN_INTERVAL_SECONDS")
    parser.add_argument("--interval", type=int, default=None, help="override the loop interval in seconds")
    args = parser.parse_args(argv)
    try:
        config = Config()
        config.validate()
    except (ScannerError, OSError, ValueError) as exc:
        LOG.error("Configuration error: %s", exc)
        return 2
    scanner = PredictiveScanner(config)
    interval = int(clamp(args.interval if args.interval is not None else config.scan_interval, 60, 900))
    while True:
        report = scanner.scan_once()
        print_report(report)
        if not args.loop:
            return 0 if report.get("market_state") != "DATA_OR_SCAN_ERROR" else 1
        time_module.sleep(interval)


if __name__ == "__main__":
    raise SystemExit(main())
