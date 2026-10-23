#!/usr/bin/env python3
"""NIFTY 50 market-structure, regime and strict local-OI scanner — V86.

V86 is a regime-first NIFTY scanner with setup-specific local OI-flow confirmation. It preserves
reliable Upstox transport/state/reporting primitives and uses one canonical unversioned market_state
file (explicit STATE_FILE overrides discovery). Its entry authorization requires:
(1) a stable higher-context market regime, (2) a price-structure setup, (3) same-session,
nearby strike OI change strictly greater than 2% with premium-confirmed directional flow,
(4) a non-whipsaw-consistent setup, (5) tradable contract quality, and (6) a valid structural
risk plan. It never places orders. Early-session candle warm-up is monitor-only, not a scan error.

Required environment: UPSTOX_ANALYTICS_TOKEN
Optional: NIFTY_INSTRUMENT_KEY, STATE_FILE, AUDIT_DIR, SCAN_INTERVAL_SECONDS,
REQUEST_TIMEOUT, API_RETRIES, MAX_QUOTE_AGE_SECONDS, MAX_CANDLE_AGE_SECONDS, MIN_SIGNAL_SCORE,
MIN_T1_REWARD_RISK_RATIO, REENTRY_COOLDOWN_MINUTES, MAX_SPREAD_RATIO, MIN_LOCAL_OI_CHANGE_PCT (minimum enforced at 2%), DIVERGENCE_RSI_DELTA,
EMAIL_SENDER, EMAIL_PASSWORD, EMAIL_RECEIVER, SMTP_HOST, SMTP_PORT, LOG_LEVEL.

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
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, time, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests

VERSION = "V86-STRUCTURE-REGIME-SETUP-OI-CONFLUENCE"
BASE_URL = "https://api.upstox.com"
IST = ZoneInfo("Asia/Kolkata")
NIFTY_KEY_DEFAULT = "NSE_INDEX|Nifty 50"
MARKET_OPEN = time(9, 15)
ENTRY_OPEN = time(9, 16)
ENTRY_CUTOFF = time(15, 15)
MARKET_CLOSE = time(15, 30)
LOG = logging.getLogger("market_scanner_v86")
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
    timeout: float = field(default_factory=lambda: clamp(env_float("REQUEST_TIMEOUT", 12.0), 2.0, 30.0))
    retries: int = field(default_factory=lambda: int(clamp(env_int("API_RETRIES", 3), 1, 5)))
    max_quote_age: float = field(default_factory=lambda: clamp(env_float("MAX_QUOTE_AGE_SECONDS", 30.0), 5.0, 90.0))
    max_candle_age: float = field(default_factory=lambda: clamp(env_float("MAX_CANDLE_AGE_SECONDS", 180.0), 60.0, 300.0))
    min_signal_score: float = field(default_factory=lambda: clamp(env_float("MIN_SIGNAL_SCORE", 74.0), 70.0, 88.0))
    min_local_oi_change_pct: float = field(default_factory=lambda: max(2.0, clamp(env_float("MIN_LOCAL_OI_CHANGE_PCT", 2.0), 2.0, 10.0)))
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
    SNAPSHOT_SCHEMAS = {80, 81, 82, 83, 84, 85, 86}

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
        current_schema = same_session and schema == 86 and loaded.get("scanner_version") == VERSION
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
            "schema_version": 86,
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
            # bodies/selection assumptions must not be sent by V86.
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


def completed_candles(frame: pd.DataFrame, now: datetime) -> pd.DataFrame:
    """Exclude the currently forming minute candle; decisions use closed candles only."""
    if frame is None or frame.empty:
        return pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
    stamps = frame["timestamp"].dt.tz_convert(IST)
    minute_start = now.astimezone(IST).replace(second=0, microsecond=0)
    return frame.loc[stamps < minute_start].copy().reset_index(drop=True)


def _rsi_series(close: pd.Series, period: int = 14) -> pd.Series:
    """Wilder-smoothed RSI values aligned to the supplied candle indices."""
    values = close.astype(float)
    delta = values.diff()
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
    rsi = _rsi_series(bars["close"])
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


def rsi_value(close: pd.Series, period: int = 14) -> float:
    if len(close) < period + 1:
        return float("nan")
    diff = close.diff().dropna()
    gain = diff.clip(lower=0).ewm(alpha=1/period, adjust=False, min_periods=period).mean()
    loss = (-diff.clip(upper=0)).ewm(alpha=1/period, adjust=False, min_periods=period).mean()
    if len(gain) == 0:
        return float("nan")
    g, l = number(gain.iloc[-1]), number(loss.iloc[-1])
    if l == 0 and g == 0: return 50.0
    if l == 0: return 100.0
    return 100 - 100/(1 + g/l)


def indicator_set(frame: pd.DataFrame, live_spot: float, now: Optional[datetime] = None) -> Indicators:
    effective_now = (now or now_ist()).astimezone(IST)
    bars = completed_candles(frame, effective_now)
    if bars.empty:
        raise ScannerError("No completed NIFTY one-minute candles are available.")
    closes = bars["close"].astype(float)
    trs = true_range(bars)
    atr = number(trs.tail(14).mean(), number((bars["high"] - bars["low"]).tail(14).mean(), 25.0))
    atr = max(8.0, atr) if finite(atr) else 25.0
    momentum_1m = (closes.iloc[-1] / closes.iloc[-2] - 1) if len(closes) >= 2 and closes.iloc[-2] else 0.0
    momentum_3m = (closes.iloc[-1] / closes.iloc[-4] - 1) if len(closes) >= 4 and closes.iloc[-4] else 0.0
    # Session VWAP is only produced when actual price-bar volume is meaningful.
    volume = bars["volume"].clip(lower=0)
    if volume.tail(10).sum() > 0:
        typical = (bars["high"] + bars["low"] + bars["close"]) / 3
        vwap = number((typical * volume).sum() / volume.sum())
        prior_n = max(1, len(bars) - 5)
        vwap_prior = number((typical.iloc[:prior_n] * volume.iloc[:prior_n]).sum() / volume.iloc[:prior_n].sum()) if volume.iloc[:prior_n].sum() > 0 else float("nan")
        vwap_slope = (vwap - vwap_prior) if finite(vwap) and finite(vwap_prior) else 0.0
        volume_source = "INDEX_CANDLE_VOLUME"
    else:
        vwap, vwap_slope, volume_source = float("nan"), float("nan"), "UNAVAILABLE_INDEX_VOLUME_ZERO"
    # Wilder-style directional movement with a smoothed DX series for ADX.
    if len(bars) >= 15:
        up_move = bars["high"].diff()
        down_move = -bars["low"].diff()
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
    session_bars = bars.loc[bars["timestamp"].dt.tz_convert(IST).dt.date == effective_now.date()]
    return Indicators(
        spot=float(live_spot), vwap=vwap, vwap_slope=vwap_slope, atr=atr, rsi=rsi_value(closes),
        adx=adx, plus_di=plus_di, minus_di=minus_di, momentum_1m=momentum_1m, momentum_3m=momentum_3m,
        last_close=float(closes.iloc[-1]), prev_close=float(closes.iloc[-2]) if len(closes) > 1 else float(closes.iloc[-1]),
        session_high=float(session_bars["high"].max()) if not session_bars.empty else float(bars["high"].max()),
        session_low=float(session_bars["low"].min()) if not session_bars.empty else float(bars["low"].min()),
        swing_high=max(recent_pivot_highs) if recent_pivot_highs else float(recent["high"].max()),
        swing_low=min(recent_pivot_lows) if recent_pivot_lows else float(recent["low"].min()),
        candles=len(bars), volume_source=volume_source,
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


def score_market_signal(frame: pd.DataFrame, indicators: Indicators, oi: Mapping[str, Any], levels: Sequence[Level],
                        now: datetime, min_score: float, step: float) -> tuple[Signal, dict[str, Any]]:
    spot, atr = indicators.spot, indicators.atr
    support = nearest_level(levels, spot + 0.5, "SUPPORT")
    resistance = nearest_level(levels, spot - 0.5, "RESISTANCE")
    # Relevant interaction level may sit very near spot or have just been crossed.
    all_supports = sorted([l for l in levels if l.kind == "SUPPORT"], key=lambda l: abs(spot-l.price))
    all_resists = sorted([l for l in levels if l.kind == "RESISTANCE"], key=lambda l: abs(spot-l.price))
    near_support = all_supports[0] if all_supports and abs(spot-all_supports[0].price) <= max(1.8*atr, 100) else support
    near_resistance = all_resists[0] if all_resists and abs(spot-all_resists[0].price) <= max(1.8*atr, 100) else resistance
    last = indicators.last_close
    closes = completed_candles(frame, now)["close"]
    buf = max(2.0, atr * 0.06)
    # Structure and momentum are measured separately from OI; OI is confluence, not the only trigger.
    bull_struct = 0.0; bear_struct = 0.0
    bull_ev: list[str] = []; bear_ev: list[str] = []
    setup_bull = "NONE"; setup_bear = "NONE"; level_bull = None; level_bear = None
    if near_support:
        touches, away, _ = _touch_evidence(frame, near_support.price, "SUPPORT", atr, now)
        dist = abs(spot-near_support.price)
        if touches >= 2 and away and last > near_support.price:
            bull_struct += 33 + min(8, 2*touches)
            bull_ev += [f"REPEATED_SUPPORT_TESTS_{touches}", f"SUPPORT_RECLAIM_{near_support.price:.2f}"]
            setup_bull, level_bull = "SUPPORT_BOUNCE", near_support.price
        elif dist <= max(0.45*atr, 18) and last >= near_support.price - buf:
            bull_struct += 17
            bull_ev.append(f"SUPPORT_TEST_WATCH_{near_support.price:.2f}")
            setup_bull, level_bull = "EARLY_SUPPORT_RECLAIM", near_support.price
    if near_resistance:
        touches, away, _ = _touch_evidence(frame, near_resistance.price, "RESISTANCE", atr, now)
        dist = abs(spot-near_resistance.price)
        if touches >= 2 and away and last < near_resistance.price:
            bear_struct += 33 + min(8, 2*touches)
            bear_ev += [f"REPEATED_RESISTANCE_TESTS_{touches}", f"RESISTANCE_REJECTION_{near_resistance.price:.2f}"]
            setup_bear, level_bear = "RESISTANCE_REJECTION", near_resistance.price
        elif (near_resistance.price > spot + 0.5 and dist <= max(0.45*atr, 18)
              and last <= near_resistance.price + max(buf, 6.0)
              and indicators.momentum_1m < 0 and indicators.momentum_3m < 0):
            # A repeated-test rejection watch may qualify before two closes below resistance,
            # but only when live spot is back below the level and both short horizons weaken.
            bear_struct += 30 if touches >= 2 else 19
            if touches >= 2:
                bear_ev.append(f"REPEATED_RESISTANCE_REJECTION_WATCH_{touches}_{near_resistance.price:.2f}")
            else:
                bear_ev.append(f"RESISTANCE_REJECTION_WATCH_{near_resistance.price:.2f}")
            bear_ev.append("LIVE_SPOT_BACK_BELOW_RESISTANCE_WITH_NEGATIVE_1M_3M_MOMENTUM")
            setup_bear, level_bear = "EARLY_RESISTANCE_REJECTION", near_resistance.price
        elif (near_resistance.price > spot + 0.5 and dist <= max(0.65*atr, 25.0)
              and indicators.momentum_1m > 0 and indicators.momentum_3m > 0
              and len(closes) >= 3 and float(closes.iloc[-1]) > float(closes.iloc[-3]) and bull_struct < 25):
            # Pressure beneath a confirmed resistance level is the predictive path; it still
            # needs supportive local OI flow/score and a complete structural risk plan.
            bull_struct = max(bull_struct, 22)
            bull_ev.append(f"PREBREAKOUT_PRESSURE_BELOW_{near_resistance.price:.2f}")
            setup_bull, level_bull = "PREBREAKOUT_RESISTANCE_PRESSURE", near_resistance.price
    if near_support:
        dist_to_support = abs(spot-near_support.price)
        if (near_support.price < spot - 0.5 and dist_to_support <= max(0.65*atr, 25.0)
                and indicators.momentum_1m < 0 and indicators.momentum_3m < 0
                and len(closes) >= 3 and float(closes.iloc[-1]) < float(closes.iloc[-3]) and bear_struct < 25):
            # Pressure above support is not labelled a breakdown until price closes through;
            # it is a predictive watch that can qualify only with OI and risk confluence.
            bear_struct = max(bear_struct, 22)
            bear_ev.append(f"PREBREAKDOWN_PRESSURE_ABOVE_{near_support.price:.2f}")
            setup_bear, level_bear = "PREBREAKDOWN_SUPPORT_PRESSURE", near_support.price
    crossed_resistances = [l for l in levels if l.kind == "RESISTANCE" and l.price < spot
                           and spot - l.price <= max(1.5 * atr, 45.0)]
    crossed_supports = [l for l in levels if l.kind == "SUPPORT" and l.price > spot
                        and l.price - spot <= max(1.5 * atr, 45.0)]
    crossed_resistance = max(crossed_resistances, key=lambda l: l.price, default=None)
    crossed_support = min(crossed_supports, key=lambda l: l.price, default=None)
    if (crossed_resistance and len(closes) >= 2
            and float(closes.iloc[-1]) > crossed_resistance.price + buf
            and float(closes.iloc[-2]) > crossed_resistance.price + buf
            and spot - crossed_resistance.price <= max(1.5 * atr, 45.0)):
        bull_struct = max(bull_struct, 52)
        bull_ev += [f"TWO_CLOSE_BREAKOUT_{crossed_resistance.price:.2f}"]
        setup_bull, level_bull = "CONFIRMED_BREAKOUT", crossed_resistance.price
    if (crossed_support and len(closes) >= 2
            and float(closes.iloc[-1]) < crossed_support.price - buf
            and float(closes.iloc[-2]) < crossed_support.price - buf
            and crossed_support.price - spot <= max(1.5 * atr, 45.0)):
        bear_struct = max(bear_struct, 52)
        bear_ev += [f"TWO_CLOSE_BREAKDOWN_{crossed_support.price:.2f}"]
        setup_bear, level_bear = "CONFIRMED_BREAKDOWN", crossed_support.price
    # Smooth momentum component avoids requiring every indicator to be available.
    bull_momentum = (12 if indicators.momentum_1m > 0 else 0) + (8 if indicators.momentum_3m > 0 else 0)
    bear_momentum = (12 if indicators.momentum_1m < 0 else 0) + (8 if indicators.momentum_3m < 0 else 0)
    if finite(indicators.rsi):
        bull_momentum += 5 if 48 <= indicators.rsi <= 75 else 0
        bear_momentum += 5 if 25 <= indicators.rsi <= 52 else 0
    if finite(indicators.plus_di) and finite(indicators.minus_di):
        bull_momentum += 5 if indicators.plus_di > indicators.minus_di else 0
        bear_momentum += 5 if indicators.minus_di > indicators.plus_di else 0
    if finite(indicators.vwap):
        bull_momentum += 5 if spot > indicators.vwap and indicators.vwap_slope >= 0 else 0
        bear_momentum += 5 if spot < indicators.vwap and indicators.vwap_slope <= 0 else 0
    else:
        bull_ev.append("VWAP_UNAVAILABLE_NOT_ASSUMED")
        bear_ev.append("VWAP_UNAVAILABLE_NOT_ASSUMED")
    bull_oi, bull_oi_ev = _oi_local_evidence(oi, "BULLISH", spot, step)
    bear_oi, bear_oi_ev = _oi_local_evidence(oi, "BEARISH", spot, step)
    # Market structure is the anchor. The setup cannot be created from OI alone.
    bull_score = clamp(bull_struct + bull_momentum + bull_oi, 0, 100)
    bear_score = clamp(bear_struct + bear_momentum + bear_oi, 0, 100)
    bull_ev += bull_oi_ev; bear_ev += bear_oi_ev
    # Open-auction/late-session safeguards, avoid first-minute noisy selections.
    clock = now.astimezone(IST).time()
    blockers = []
    if clock < ENTRY_OPEN:
        blockers.append("BEFORE_ENTRY_WINDOW")
    if clock >= ENTRY_CUTOFF:
        blockers.append("ENTRY_CUTOFF_MONITOR_ONLY")
    if indicators.candles < 8:
        blockers.append("INSUFFICIENT_COMPLETED_CANDLES")
    if max(bull_score, bear_score) < min_score:
        direction, setup, score, level, evidence = "NEUTRAL", "NO_QUALIFYING_STRUCTURE", max(bull_score, bear_score), None, ["MARKET_STRUCTURE_SCORE_BELOW_THRESHOLD"]
    elif abs(bull_score - bear_score) < 7:
        direction, setup, score, level, evidence = "NEUTRAL", "CONFLICTING_DIRECTIONAL_EVIDENCE", max(bull_score, bear_score), None, ["BULL_BEAR_SCORE_SPREAD_LT_7", f"BULL={bull_score:.1f}", f"BEAR={bear_score:.1f}"]
    elif bull_score > bear_score:
        direction, setup, score, level, evidence = "BULLISH", setup_bull, bull_score, level_bull, bull_ev
    else:
        direction, setup, score, level, evidence = "BEARISH", setup_bear, bear_score, level_bear, bear_ev
    if direction != "NEUTRAL" and not setup or setup == "NONE":
        direction, setup, level = "NEUTRAL", "NO_STRUCTURAL_TRIGGER", None
    if direction != "NEUTRAL" and blockers:
        evidence.extend(blockers)
    signal = Signal(direction, setup, round(score, 1), round(clamp(score, 0, 92), 1),
                    "; ".join(evidence[:8]), level, tuple(dict.fromkeys(evidence)), tuple(blockers))
    diag = {"bull_score": round(bull_score, 1), "bear_score": round(bear_score, 1),
            "nearest_support": asdict(support) if support else None, "nearest_resistance": asdict(resistance) if resistance else None,
            "interaction_support": asdict(near_support) if near_support else None, "interaction_resistance": asdict(near_resistance) if near_resistance else None,
            "bull_momentum_score": round(bull_momentum, 1), "bear_momentum_score": round(bear_momentum, 1),
            "bull_oi_score": round(bull_oi, 1), "bear_oi_score": round(bear_oi, 1), "threshold": min_score}
    return signal, diag


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
    # Choppy signs plus poor directional efficiency take precedence over a single DI/ADX reading.
    if flip_count >= 5 and efficiency < 0.40:
        regime, reason = "WHIPSAW", "FREQUENT_DIRECTION_FLIPS_AND_LOW_EFFICIENCY"
    elif efficiency < 0.25 and (adx < 23 or flip_count >= 2) and width <= max(8.0 * atr, 180.0):
        regime, reason = "SIDEWAYS", "LOW_DIRECTIONAL_EFFICIENCY_WITHIN_INTRADAY_RANGE"
    elif ema_fast < ema_slow and ema_slope < 0 and di_bear and mom_bear and efficiency >= 0.25:
        regime, reason = "TREND_BEARISH", "EMA_DI_AND_MOMENTUM_ALIGN_BEARISH"
    elif ema_fast > ema_slow and ema_slope > 0 and di_bull and mom_bull and efficiency >= 0.25:
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
            "minus_di": round(indicators.minus_di, 2) if finite(indicators.minus_di) else None}


def qualify_local_oi(oi: Mapping[str, Any], signal: Signal, spot: float, step: float,
                     min_change_pct: float = 2.0) -> dict[str, Any]:
    """Require a setup-specific local OI pair, not any one positive OI number.

    The spreadsheet's directional pairs are applied at the tested structural level:
    bullish = put writing + call short-covering; bearish = call writing + put short-covering.
    The *writing/build-up* leg must exceed +2% OI with falling premium. The paired
    short-covering leg must show a real OI decline (at least 0.5%) with rising premium;
    requiring both legs to exceed 2% would reject many realistic but valid covering patterns.
    Aggregate PCR/session OI cannot substitute for the local pair.
    """
    threshold = max(0.02, min(0.10, number(min_change_pct, 2.0) / 100.0))
    premium_floor = 0.005  # at least 0.5% option-premium movement to classify a local flow
    min_abs_delta_oi = 1300.0
    direction = str(signal.direction).upper()
    setup = str(signal.setup).upper()
    empty = {"qualified": False, "writing_oi_threshold_pct_exclusive": threshold * 100,
             "covering_oi_decline_threshold_pct_exclusive": 0.5,
             "premium_change_min_pct": premium_floor * 100, "min_absolute_delta_oi": min_abs_delta_oi,
             "supporting_rows": [], "opposing_rows": [], "reference_strikes": [],
             "primary_flow": None, "secondary_flow": None}
    if direction not in {"BULLISH", "BEARISH"}:
        return {**empty, "reason": "NO_DIRECTIONAL_PRICE_STRUCTURE"}
    if not bool(oi.get("tactical_available")):
        return {**empty, "reason": "SAME_SESSION_LOCAL_OI_BASELINE_UNAVAILABLE_OR_STALE",
                "tactical_age_minutes": oi.get("snapshot_age_minutes")}
    if setup in {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "CONFIRMED_BREAKOUT", "PREBREAKOUT_RESISTANCE_PRESSURE"}:
        primary_side, primary_flow = "put", "SHORT_BUILDUP_WRITING"
        secondary_side, secondary_flow = "call", "SHORT_COVERING"
    elif setup in {"RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION", "CONFIRMED_BREAKDOWN", "PREBREAKDOWN_SUPPORT_PRESSURE"}:
        primary_side, primary_flow = "call", "SHORT_BUILDUP_WRITING"
        secondary_side, secondary_flow = "put", "SHORT_COVERING"
    else:
        return {**empty, "reason": "UNSUPPORTED_SETUP_FOR_LOCAL_OI_PAIR", "setup": setup}
    ref = number(signal.level, spot)
    max_level_distance = max(2.0 * step, 100.0)
    max_spot_distance = max(4.0 * step, 200.0)
    rows = [r for r in oi.get("walls", []) if isinstance(r, Mapping) and finite(r.get("strike"))
            and abs(number(r.get("strike")) - ref) <= max_level_distance
            and abs(number(r.get("strike")) - spot) <= max_spot_distance]

    def item(row: Mapping[str, Any], side: str, expected_flow: str) -> Optional[dict[str, Any]]:
        change = number(row.get(f"{side}_change_pct"))
        premium_change = number(row.get(f"{side}_premium_change_pct"))
        delta_oi = number(row.get(f"{side}_delta_oi"))
        base_oi = number(row.get(f"{side}_prev_oi"))
        old_premium = number(row.get(f"{side}_prev_ltp"))
        current_premium = number(row.get(f"{side}_ltp"))
        if not all(finite(v) for v in (change, premium_change, delta_oi, base_oi, old_premium, current_premium)):
            return None
        if base_oi < 10000 or old_premium < 5 or current_premium < 5 or abs(delta_oi) < min_abs_delta_oi:
            return None
        if expected_flow == "SHORT_BUILDUP_WRITING":
            passed = change > threshold and premium_change <= -premium_floor
        else:
            passed = change < -0.005 and premium_change >= premium_floor
        if not passed:
            return None
        computed_flow = classify_oi_flow(change, premium_change)
        if computed_flow != expected_flow:
            return None
        return {"strike": float(row["strike"]), "option_side": side.upper(),
                "oi_change_pct": round(change * 100.0, 3),
                "premium_change_pct": round(premium_change * 100.0, 3),
                "delta_oi": round(delta_oi, 1), "baseline_oi": round(base_oi, 1),
                "current_oi": round(number(row.get(f"{side}_oi"), 0.0), 1),
                "flow": computed_flow}

    primary: list[dict[str, Any]] = []
    secondary: list[dict[str, Any]] = []
    opposing: list[dict[str, Any]] = []
    for row in rows:
        strike = number(row.get("strike"))
        p = item(row, primary_side, primary_flow)
        s = item(row, secondary_side, secondary_flow)
        if p:
            # Put writing must be at/below the bullish tested boundary (allow one grid
            # step for round-grid/Fib alignment); call writing must be at/above resistance.
            if direction == "BULLISH" and strike <= ref + step + 0.01:
                primary.append(p)
            elif direction == "BEARISH" and strike >= ref - step - 0.01:
                primary.append(p)
        if s and abs(strike - ref) <= 2.0 * step + 0.01:
            secondary.append(s)
        for side in ("call", "put"):
            change = number(row.get(f"{side}_change_pct"))
            prem = number(row.get(f"{side}_premium_change_pct"))
            delta = number(row.get(f"{side}_delta_oi"))
            base = number(row.get(f"{side}_prev_oi"))
            old_ltp = number(row.get(f"{side}_prev_ltp"))
            new_ltp = number(row.get(f"{side}_ltp"))
            if not all(finite(v) for v in (change, prem, delta, base, old_ltp, new_ltp)):
                continue
            if base < 10000 or min(old_ltp, new_ltp) < 5 or abs(delta) < min_abs_delta_oi or abs(change) <= threshold or abs(prem) < premium_floor:
                continue
            flow = classify_oi_flow(change, prem)
            if direction == "BULLISH":
                is_opposing = ((side == "call" and flow == "SHORT_BUILDUP_WRITING") or
                               (side == "put" and flow in {"LONG_BUILDUP_BUYING", "SHORT_COVERING"}))
            else:
                is_opposing = ((side == "put" and flow == "SHORT_BUILDUP_WRITING") or
                               (side == "call" and flow in {"LONG_BUILDUP_BUYING", "SHORT_COVERING"}))
            # A clear opposite buildup one strike from the tested boundary cancels the pair.
            if is_opposing and abs(strike - ref) <= step + 0.01:
                opposing.append({"strike": strike, "option_side": side.upper(),
                                 "oi_change_pct": round(change * 100.0, 3),
                                 "premium_change_pct": round(prem * 100.0, 3),
                                 "delta_oi": round(delta, 1), "flow": flow})

    primary.sort(key=lambda x: (abs(x["strike"] - ref), -abs(x["oi_change_pct"])))
    secondary.sort(key=lambda x: (abs(x["strike"] - ref), -abs(x["oi_change_pct"])))
    opposing.sort(key=lambda x: (abs(x["strike"] - ref), -abs(x["oi_change_pct"])))
    pair_exists = bool(primary and secondary)
    conflict = bool(pair_exists and any(
        abs(o["strike"] - ref) <= step + 0.01 and abs(o["oi_change_pct"]) >=
        min(abs(primary[0]["oi_change_pct"]), abs(secondary[0]["oi_change_pct"]))
        for o in opposing
    ))
    qualified = pair_exists and not conflict
    reason = ("LOCAL_OI_PAIR_CONFIRMED_STRICTLY_ABOVE_2PCT" if qualified else
              "LOCAL_OI_COUNTERFLOW_CONFLICTS_AT_TESTED_BOUNDARY" if conflict else
              "REQUIRED_LOCAL_OI_PAIR_NOT_CONFIRMED_STRICTLY_ABOVE_2PCT")
    return {**empty, "qualified": qualified, "reason": reason,
            "setup": setup, "direction": direction, "reference_level": round(ref, 2),
            "primary_required": {"option_side": primary_side.upper(), "flow": primary_flow},
            "secondary_required": {"option_side": secondary_side.upper(), "flow": secondary_flow},
            "primary_flow": primary[0] if primary else None,
            "secondary_flow": secondary[0] if secondary else None,
            "supporting_rows": primary[:5] + secondary[:5], "opposing_rows": opposing[:5],
            "reference_strikes": sorted({x["strike"] for x in (primary[:3] + secondary[:3])}),
            "tactical_age_minutes": oi.get("snapshot_age_minutes"),
            "tactical_available": bool(oi.get("tactical_available")),
            "local_rows_considered": len(rows)}


def qualify_regime(signal: Signal, regime: Mapping[str, Any], indicators: Indicators, spot: float,
                   fib_divergence: Optional[Mapping[str, Any]] = None,
                   local_oi: Optional[Mapping[str, Any]] = None,
                   setup_rules: Optional[Mapping[str, Any]] = None) -> dict[str, Any]:
    """Require higher-context alignment, or very high-confluence structural reversal/range edge."""
    direction = str(signal.direction).upper()
    name = str(regime.get("regime", "TRANSITION")).upper()
    setup = str(signal.setup).upper()
    session_bias = str(regime.get("session_bias", "UNKNOWN")).upper()
    fib_ok = bool((fib_divergence or {}).get("qualified"))
    oi_ok = bool((local_oi or {}).get("qualified"))
    setup_ok = bool((setup_rules or {}).get("qualified"))
    evidence = " ".join(signal.evidence).upper()
    reversal_setups = {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"}
    bullish_reversal = direction == "BULLISH" and setup in {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM"}
    bearish_reversal = direction == "BEARISH" and setup in {"RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"}
    reversal = bullish_reversal or bearish_reversal
    if direction not in {"BULLISH", "BEARISH"}:
        return {"qualified": False, "reason": "NO_DIRECTIONAL_STRUCTURE", "regime": name}
    if name == "WARMUP":
        return {"qualified": False, "reason": "CANDLE_WARMUP_MONITOR_ONLY", "regime": name}

    # Countertrend trades are possible only at a real reversal: confirmed matching RSI divergence,
    # Fib support/resistance confluence, paired local OI flow, and price already turning off the level.
    reversal_confluence = bool(reversal and fib_ok and oi_ok and finite(signal.level) and
        abs(spot - float(signal.level)) <= max(1.0 * indicators.atr, 45.0) and
        ((direction == "BULLISH" and indicators.momentum_1m > 0 and indicators.momentum_3m > -0.0010) or
         (direction == "BEARISH" and indicators.momentum_1m < 0 and indicators.momentum_3m < 0.0010)))

    strict_break_setup = setup in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN"} and setup_ok and oi_ok
    strong_break = bool(
        (direction == "BULLISH" and setup == "CONFIRMED_BREAKOUT" and finite(indicators.rsi) and indicators.rsi > 60
         and indicators.momentum_1m > 0 and indicators.momentum_3m > 0) or
        (direction == "BEARISH" and setup == "CONFIRMED_BREAKDOWN" and finite(indicators.rsi) and indicators.rsi < 40
         and indicators.momentum_1m < 0 and indicators.momentum_3m < 0))

    if name in {"TREND_BULLISH", "TREND_BEARISH"}:
        trend_direction = "BULLISH" if name == "TREND_BULLISH" else "BEARISH"
        aligned = direction == trend_direction
        session_opposes = session_bias in {"BULLISH", "BEARISH"} and session_bias != direction
        if aligned and not session_opposes:
            return {"qualified": True, "reason": "ALIGNED_WITH_DOMINANT_TREND_AND_SESSION", "regime": name,
                    "session_bias": session_bias, "countertrend_reversal_confluence": False}
        if aligned and session_opposes and (strict_break_setup or reversal_confluence):
            return {"qualified": True, "reason": "LOCAL_STRUCTURE_AND_SETUP_GATES_OVERRIDE_LAGGING_SESSION_BIAS",
                    "regime": name, "session_bias": session_bias,
                    "strict_two_close_break_with_oi": strict_break_setup,
                    "countertrend_reversal_confluence": reversal_confluence}
        if not aligned and strict_break_setup:
            return {"qualified": True, "reason": "STRICT_TWO_CLOSE_BREAK_AND_LOCAL_OI_OVERRIDE_LAGGING_TREND_CLASSIFIER",
                    "regime": name, "session_bias": session_bias,
                    "strict_two_close_break_with_oi": True}
        if not aligned and reversal_confluence:
            return {"qualified": True, "reason": "COUNTERTREND_REVERSAL_CONFIRMED_BY_FIB_DIVERGENCE_LOCAL_OI_AND_PRICE",
                    "regime": name, "session_bias": session_bias, "countertrend_reversal_confluence": True}
        return {"qualified": False,
                "reason": "TREND_OR_SESSION_CONFLICT_WITHOUT_CONFIRMED_REVERSAL_OR_TWO_CLOSE_FLIP",
                "regime": name, "session_bias": session_bias, "strong_break": strong_break,
                "countertrend_reversal_confluence": reversal_confluence}

    if name in {"SIDEWAYS", "WHIPSAW"}:
        location = number(regime.get("range_location_pct"))
        lower_edge = finite(location) and location <= 32.0
        upper_edge = finite(location) and location >= 68.0
        repeated_support = "REPEATED_SUPPORT_TESTS" in evidence
        repeated_resistance = "REPEATED_RESISTANCE_TESTS" in evidence or "REPEATED_RESISTANCE_REJECTION_WATCH" in evidence
        bull_fade = (bullish_reversal and repeated_support and lower_edge and
                     indicators.momentum_1m > 0 and indicators.momentum_3m > -0.0005 and fib_ok and oi_ok)
        bear_fade = (bearish_reversal and repeated_resistance and upper_edge and
                     indicators.momentum_1m < 0 and indicators.momentum_3m < 0.0005 and fib_ok and oi_ok)
        prior_high = number(regime.get("prior_range_high"))
        prior_low = number(regime.get("prior_range_low"))
        buffer = max(3.0, 0.10 * indicators.atr)
        bull_range_break = (setup == "CONFIRMED_BREAKOUT" and direction == "BULLISH" and strict_break_setup and
                            strong_break and finite(prior_high) and spot > prior_high + buffer)
        bear_range_break = (setup == "CONFIRMED_BREAKDOWN" and direction == "BEARISH" and strict_break_setup and
                            strong_break and finite(prior_low) and spot < prior_low - buffer)
        if bull_fade or bear_fade:
            return {"qualified": True, "reason": "CONFIRMED_RANGE_EDGE_FADE_WITH_OI_FIB_DIVERGENCE",
                    "regime": name, "session_bias": session_bias, "range_location_pct": location}
        if bull_range_break or bear_range_break:
            return {"qualified": True, "reason": "TWO_CLOSE_BREAKOUT_OF_PRIOR_RANGE_WITH_STRICT_MOMENTUM",
                    "regime": name, "session_bias": session_bias, "range_location_pct": location}
        return {"qualified": False,
                "reason": "SIDEWAYS_WHIPSAW_BLOCKS_MIDRANGE_AND_UNCONFIRMED_ENTRIES",
                "regime": name, "session_bias": session_bias, "range_location_pct": location,
                "lower_edge": lower_edge, "upper_edge": upper_edge}

    # TRANSITION is not assigned an arbitrary direction. Permit a confirmed break only when
    # its own strict breakout/breakdown rule is met, or a complete reversal at a structural level.
    if reversal_confluence:
        return {"qualified": True, "reason": "TRANSITION_REVERSAL_CONFIRMED_BY_FULL_CONFLUENCE",
                "regime": name, "session_bias": session_bias}
    if setup in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN"} and strict_break_setup and strong_break:
        return {"qualified": True, "reason": "TRANSITION_CONFIRMED_BREAK_WITH_ALIGNED_MOMENTUM_AND_OI",
                "regime": name, "session_bias": session_bias}
    return {"qualified": False, "reason": "TRANSITION_REQUIRES_CONFIRMED_BREAK_OR_FULL_REVERSAL_CONFLUENCE",
            "regime": name, "session_bias": session_bias}


def diagnose_expiry_pin(oi: Mapping[str, Any], fib: Mapping[str, Any], indicators: Indicators,
                        expiry: str, now: datetime, step: float, min_change_pct: float = 2.0) -> dict[str, Any]:
    """Detect a high-confidence expiry pin without turning ordinary sideways tape into a pin veto."""
    try:
        expiry_date = date.fromisoformat(str(expiry)[:10])
        expiry_days = (expiry_date - now.astimezone(IST).date()).days
    except (TypeError, ValueError):
        expiry_days = 999
    up = fib.get("up_leg") if isinstance(fib.get("up_leg"), Mapping) else None
    down = fib.get("down_leg") if isinstance(fib.get("down_leg"), Mapping) else None
    support = number((up or {}).get("retracements", {}).get("61.8"))
    resistance = number((down or {}).get("retracements", {}).get("61.8"))
    if finite(support) and finite(resistance) and support > resistance:
        support, resistance = resistance, support
    fib_gap = resistance - support if finite(support) and finite(resistance) else float("nan")
    between = bool(finite(support) and finite(resistance) and support <= indicators.spot <= resistance)
    grid = round_to_grid(indicators.spot, step)
    row = next((r for r in oi.get("walls", []) if isinstance(r, Mapping)
                and finite(r.get("strike")) and abs(number(r.get("strike")) - grid) < 0.5), None)
    cutoff = max(0.02, min(0.10, min_change_pct / 100.0))
    both_writing = bool(row and
        number(row.get("call_change_pct")) > cutoff and number(row.get("put_change_pct")) > cutoff and
        str(row.get("call_flow", "")).upper() == "SHORT_BUILDUP_WRITING" and
        str(row.get("put_flow", "")).upper() == "SHORT_BUILDUP_WRITING")
    flat_momentum = abs(indicators.momentum_1m) < 0.0012 and abs(indicators.momentum_3m) < 0.0025
    neutral_rsi = finite(indicators.rsi) and 44 <= indicators.rsi <= 56
    detected = bool(expiry_days <= 1 and finite(fib_gap) and 0 <= fib_gap <= max(1.2 * indicators.atr, 50.0)
                    and between and both_writing and (flat_momentum or neutral_rsi))
    return {"detected": detected, "expiry_days": expiry_days,
            "fib_support_61_8": support if finite(support) else None,
            "fib_resistance_61_8": resistance if finite(resistance) else None,
            "fib_gap_points": round(fib_gap, 2) if finite(fib_gap) else None,
            "atm_strike": grid if finite(grid) else None, "price_between_fib_levels": between,
            "same_strike_call_put_writing_gt_threshold": both_writing,
            "oi_change_threshold_pct_exclusive": cutoff * 100,
            "flat_momentum": flat_momentum, "neutral_rsi": neutral_rsi,
            "reason": "EXPIRY_PIN_NO_ENTRY" if detected else "PIN_CONDITIONS_NOT_COMPLETE"}


def qualify_fib_divergence(signal: Signal, regime: Mapping[str, Any], fib: Mapping[str, Any],
                            divergence: Mapping[str, Any], spot: float, atr: float) -> dict[str, Any]:
    """Apply Fib/divergence only where structurally relevant; missing data is not an opposing signal.

    Spreadsheet-derived policy: reversals require confirmed matching RSI divergence plus a nearby
    50/61.8% Fibonacci zone. Breakouts/breakdowns do not require divergence to be available, but a
    *confirmed* opposing divergence blocks them. No signal can bypass the independent >2% local-OI
    or overall-regime gates.
    """
    direction = str(signal.direction).upper()
    setup = str(signal.setup).upper()
    regime_name = str(regime.get("regime", "TRANSITION")).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        return {"qualified": False, "reason": "NO_DIRECTIONAL_SIGNAL", "fib_confluence": False,
                "divergence_required": False, "opposing_divergence_confirmed": False}

    matching_div = divergence.get("bullish") if direction == "BULLISH" else divergence.get("bearish")
    opposing_div = divergence.get("bearish") if direction == "BULLISH" else divergence.get("bullish")
    opposing_confirmed = isinstance(opposing_div, Mapping) and bool(opposing_div)
    if opposing_confirmed:
        return {"qualified": False, "reason": "CONFIRMED_OPPOSING_RSI_DIVERGENCE",
                "fib_confluence": False, "divergence_required": False,
                "matching_divergence": matching_div, "opposing_divergence_confirmed": True,
                "opposing_divergence": opposing_div, "fib_levels_checked": []}

    reversal_setups = {
        "SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"
    }
    # In choppy conditions only genuine boundary fades can qualify; generic pre-break pressure remains vetoed by regime gate.
    reversal = setup in reversal_setups
    if not reversal:
        return {"qualified": True,
                "reason": "NO_OPPOSING_DIVERGENCE_CONFIRMED; DIVERGENCE_UNAVAILABLE_IS_NOT_A_VETO",
                "fib_confluence": None, "divergence_required": False,
                "matching_divergence": matching_div, "opposing_divergence_confirmed": False,
                "fib_levels_checked": [], "fib_available": bool(fib.get("available")),
                "divergence_available": bool(divergence.get("available"))}

    # Reversal signals need a fresh, confirmed same-direction divergence; no divergence and
    # unavailable divergence are different states and both conservatively fail reversal entry.
    if not isinstance(matching_div, Mapping) or not matching_div:
        return {"qualified": False, "reason": "REVERSAL_REQUIRES_CONFIRMED_MATCHING_RSI_DIVERGENCE",
                "fib_confluence": False, "divergence_required": True,
                "matching_divergence": None, "opposing_divergence_confirmed": False,
                "fib_levels_checked": [], "fib_available": bool(fib.get("available")),
                "divergence_available": bool(divergence.get("available"))}

    if direction == "BULLISH":
        zone = fib.get("bullish_support_zone")
        # If the latest qualified leg's support map is missing, no synthetic level is substituted.
        raw_levels = []
        if isinstance(zone, Mapping):
            raw_levels = [number(zone.get("fib_50")), number(zone.get("fib_61_8")), number(zone.get("fib_100"))]
        level_role = "BULLISH_FIB_SUPPORT_50_61_8"
    else:
        zone = fib.get("bearish_resistance_levels")
        raw_levels = []
        if isinstance(zone, Mapping):
            raw_levels = [number(zone.get("fib_50")), number(zone.get("fib_61_8")), number(zone.get("fib_100"))]
        level_role = "BEARISH_FIB_RESISTANCE_50_61_8"
    fib_levels = [x for x in raw_levels if finite(x)]
    if not bool(fib.get("available")) or not fib_levels:
        return {"qualified": False, "reason": "REVERSAL_REQUIRES_AVAILABLE_CONFIRMED_FIB_ZONE",
                "fib_confluence": False, "divergence_required": True,
                "matching_divergence": matching_div, "opposing_divergence_confirmed": False,
                "fib_levels_checked": fib_levels, "fib_available": bool(fib.get("available")),
                "divergence_available": bool(divergence.get("available"))}

    # Compare both live spot and detected price-structure boundary to avoid missing a valid touch
    # because spot has already moved a little off the pivot. The tolerance is volatility-scaled.
    anchor = number(signal.level, spot)
    tolerance = max(12.0, min(28.0, 0.45 * atr if finite(atr) else 12.0))
    distances = [{"level": round(level, 2), "spot_distance": round(abs(spot-level), 2),
                  "structure_distance": round(abs(anchor-level), 2),
                  "distance": round(min(abs(spot-level), abs(anchor-level)), 2)} for level in fib_levels]
    closest = min(distances, key=lambda item: item["distance"])
    confluence = closest["distance"] <= tolerance
    return {"qualified": bool(confluence),
            "reason": ("REVERSAL_CONFIRMED_DIVERGENCE_AND_FIB_CONFLUENCE" if confluence else
                       "REVERSAL_DIVERGENCE_CONFIRMED_BUT_PRICE_STRUCTURE_NOT_NEAR_FIB_ZONE"),
            "fib_confluence": bool(confluence), "fib_role": level_role, "fib_tolerance_points": round(tolerance, 2),
            "closest_fib_level": closest["level"], "closest_fib_distance_points": closest["distance"],
            "fib_levels_checked": distances, "divergence_required": True,
            "matching_divergence": matching_div, "opposing_divergence_confirmed": False,
            "fib_available": bool(fib.get("available")), "divergence_available": bool(divergence.get("available"))}



def qualify_setup_rules(signal: Signal, frame: pd.DataFrame, indicators: Indicators,
                        regime: Mapping[str, Any], fib_gate: Mapping[str, Any],
                        oi_gate: Mapping[str, Any], now: datetime) -> dict[str, Any]:
    """Apply the distinct spreadsheet entry rules after detection and before authorization."""
    direction = str(signal.direction).upper()
    setup = str(signal.setup).upper()
    bars = completed_candles(frame, now.astimezone(IST))
    out = {"qualified": False, "setup": setup, "direction": direction,
           "required_completed_bars": 20, "completed_bars": int(len(bars)), "checks": []}
    if direction not in {"BULLISH", "BEARISH"}:
        return {**out, "reason": "NO_DIRECTIONAL_SETUP"}
    if len(bars) < 20:
        return {**out, "reason": "INSUFFICIENT_BARS_FOR_RELIABLE_ENTRY"}
    if not finite(indicators.rsi) or not finite(indicators.atr) or indicators.atr <= 0:
        return {**out, "reason": "RSI_OR_ATR_UNAVAILABLE"}
    if not finite(signal.level):
        return {**out, "reason": "STRUCTURAL_TRIGGER_LEVEL_UNAVAILABLE"}
    if not bool(oi_gate.get("qualified")):
        return {**out, "reason": "SETUP_SPECIFIC_LOCAL_OI_PAIR_NOT_CONFIRMED"}

    closes = bars["close"].astype(float).reset_index(drop=True)
    level = float(signal.level)
    buffer = max(2.0, 0.08 * indicators.atr)
    max_entry_extension = max(1.5 * indicators.atr, 45.0)
    spot_dist = abs(indicators.spot - level)
    if spot_dist > max_entry_extension:
        return {**out, "reason": "PRICE_TOO_EXTENDED_FROM_TRIGGER_LEVEL",
                "distance_from_level_points": round(spot_dist, 2),
                "max_allowed_distance_points": round(max_entry_extension, 2)}

    current_3m = float(closes.iloc[-1] / closes.iloc[-4] - 1.0) if len(closes) >= 4 and closes.iloc[-4] else 0.0
    prior_3m = float(closes.iloc[-4] / closes.iloc[-7] - 1.0) if len(closes) >= 7 and closes.iloc[-7] else 0.0
    expanding_up = current_3m > 0 and current_3m > prior_3m
    expanding_down = current_3m < 0 and current_3m < prior_3m
    last_close = float(closes.iloc[-1])
    prev_close = float(closes.iloc[-2])
    matching_div = (fib_gate.get("matching_divergence") if isinstance(fib_gate.get("matching_divergence"), Mapping) else None)
    fib_ok = bool(fib_gate.get("qualified")) and bool(fib_gate.get("fib_confluence"))
    rsi = float(indicators.rsi)

    if setup == "CONFIRMED_BREAKOUT" and direction == "BULLISH":
        checks = {
            "two_closes_above_boundary": last_close > level + buffer and prev_close > level + buffer,
            "live_spot_above_boundary": indicators.spot > level + buffer,
            "rsi_strictly_above_60": rsi > 60.0,
            "momentum_positive_1m_3m": indicators.momentum_1m > 0 and indicators.momentum_3m > 0,
            "upward_momentum_expanding": expanding_up,
            "no_confirmed_opposing_divergence": not bool(fib_gate.get("opposing_divergence_confirmed")),
        }
    elif setup == "CONFIRMED_BREAKDOWN" and direction == "BEARISH":
        checks = {
            "two_closes_below_boundary": last_close < level - buffer and prev_close < level - buffer,
            "live_spot_below_boundary": indicators.spot < level - buffer,
            "rsi_strictly_below_40": rsi < 40.0,
            "momentum_negative_1m_3m": indicators.momentum_1m < 0 and indicators.momentum_3m < 0,
            "downward_momentum_expanding": expanding_down,
            "no_confirmed_opposing_divergence": not bool(fib_gate.get("opposing_divergence_confirmed")),
        }
    elif setup in {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM"} and direction == "BULLISH":
        checks = {
            "confirmed_bullish_divergence": bool(matching_div) and str(matching_div.get("type", "BULLISH")) == "BULLISH",
            "fib_50_61_8_support_confluence": fib_ok,
            "completed_close_reclaimed_support": last_close > level + buffer * 0.25,
            "live_spot_not_materially_below_support": indicators.spot >= level - buffer,
            "1m_momentum_turning_up": indicators.momentum_1m > 0,
            "3m_momentum_not_strongly_bearish": indicators.momentum_3m > -0.0010,
        }
    elif setup in {"RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"} and direction == "BEARISH":
        checks = {
            "confirmed_bearish_divergence": bool(matching_div) and str(matching_div.get("type", "BEARISH")) == "BEARISH",
            "fib_50_61_8_or_100_resistance_confluence": fib_ok,
            "completed_close_rejected_below_resistance": last_close < level - buffer * 0.25,
            "live_spot_not_materially_above_resistance": indicators.spot <= level + buffer,
            "1m_momentum_turning_down": indicators.momentum_1m < 0,
            "3m_momentum_not_strongly_bullish": indicators.momentum_3m < 0.0010,
        }
    elif setup == "PREBREAKOUT_RESISTANCE_PRESSURE" and direction == "BULLISH":
        checks = {
            "overall_bullish_context": str(regime.get("regime")) == "TREND_BULLISH" or str(regime.get("session_bias")) == "BULLISH",
            "price_near_but_not_far_above_resistance": indicators.spot <= level + buffer and level - indicators.spot <= max(0.75*indicators.atr, 35.0),
            "rsi_supports_upside_pressure": rsi >= 55.0,
            "momentum_positive_and_expanding": indicators.momentum_1m > 0 and indicators.momentum_3m > 0 and expanding_up,
            "no_confirmed_opposing_divergence": not bool(fib_gate.get("opposing_divergence_confirmed")),
        }
    elif setup == "PREBREAKDOWN_SUPPORT_PRESSURE" and direction == "BEARISH":
        checks = {
            "overall_bearish_context": str(regime.get("regime")) == "TREND_BEARISH" or str(regime.get("session_bias")) == "BEARISH",
            "price_near_but_not_far_below_support": indicators.spot >= level - buffer and indicators.spot - level <= max(0.75*indicators.atr, 35.0),
            "rsi_supports_downside_pressure": rsi <= 45.0,
            "momentum_negative_and_expanding": indicators.momentum_1m < 0 and indicators.momentum_3m < 0 and expanding_down,
            "no_confirmed_opposing_divergence": not bool(fib_gate.get("opposing_divergence_confirmed")),
        }
    else:
        return {**out, "reason": "UNSUPPORTED_SETUP_DIRECTION_PAIR"}

    failed = [name for name, passed in checks.items() if not passed]
    return {**out, "qualified": not failed,
            "reason": "SETUP_SPECIFIC_SPREADSHEET_RULES_PASSED" if not failed else "SETUP_SPECIFIC_REQUIRED_RULES_FAILED",
            "checks": checks, "failed_checks": failed,
            "last_completed_close": round(last_close, 2), "previous_completed_close": round(prev_close, 2),
            "boundary": round(level, 2), "boundary_buffer_points": round(buffer, 2),
            "current_3m_return_pct": round(current_3m * 100.0, 4),
            "prior_3m_return_pct": round(prior_3m * 100.0, 4),
            "rsi": round(rsi, 2), "fib_confluence": fib_ok,
            "local_oi_pair_confirmed": bool(oi_gate.get("qualified"))}

def can_issue_signal_v86(state: Mapping[str, Any], signal: Signal, now: datetime,
                         cooldown_minutes: int, regime: Mapping[str, Any],
                         full_confluence: bool = False,
                         regime_confirmation: Optional[Mapping[str, Any]] = None) -> tuple[bool, str]:
    """Anti-churn lifecycle: no opposite flip from a live/T1 signal without structure changing regime."""
    active = state.get("active_signal")
    current = now.astimezone(IST)
    if isinstance(active, Mapping):
        status = str(active.get("status", "")).upper()
        old_direction = str(active.get("direction", "")).upper()
        terminal = parse_dt(active.get("terminal_timestamp"))
        if status in {"TRACKING", "T1_REACHED"}:
            if old_direction == signal.direction:
                return False, "ACTIVE_SIGNAL_ALREADY_TRACKING_SAME_DIRECTION"
            setup = signal.setup.upper()
            confirmed_flip = setup in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN"}
            reversal = setup in {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"}
            regime_name = str(regime.get("regime", ""))
            regime_aligned = (regime_name == "TREND_BULLISH" and signal.direction == "BULLISH") or (regime_name == "TREND_BEARISH" and signal.direction == "BEARISH")
            # While the first target has not printed, do not churn into an opposite signal.
            # After T1, allow an opposite signal only if all structural/Fib/OI/market gates
            # already passed; otherwise require a trend-aligned two-close break.
            if status == "T1_REACHED" and full_confluence and reversal and bool((regime_confirmation or {}).get("qualified")):
                return True, "OPPOSITE_REVERSAL_CONFIRMED_AFTER_T1_WITH_FULL_CONFLUENCE"
            if not (confirmed_flip and regime_aligned and full_confluence):
                return False, "OPPOSITE_SIGNAL_BLOCKED_UNTIL_T1_OR_CONFIRMED_REGIME_FLIP"
            return True, "STRICT_BREAK_AND_REGIME_FLIP_CONFIRMED"
        if terminal:
            elapsed = (current - terminal.astimezone(IST)).total_seconds() / 60.0
            if elapsed < max(1, cooldown_minutes):
                if old_direction == signal.direction:
                    return False, "SAME_DIRECTION_REENTRY_COOLDOWN"
                # Opposite side can enter during the cooldown only on a clean break and regime alignment.
                setup = signal.setup.upper()
                name = str(regime.get("regime", ""))
                aligned = (name == "TREND_BULLISH" and signal.direction == "BULLISH") or (name == "TREND_BEARISH" and signal.direction == "BEARISH")
                if not (setup in {"CONFIRMED_BREAKOUT", "CONFIRMED_BREAKDOWN"} and aligned):
                    return False, "POST_TERMINAL_COOLDOWN_BLOCKS_UNCONFIRMED_FLIP"
    return True, "STRUCTURE_OI_AND_REGIME_GATES_PASSED"


def calculate_risk_plan(signal: Signal, levels: Sequence[Level], indicators: Indicators, min_rr: float) -> RiskPlan:
    if signal.direction not in {"BULLISH", "BEARISH"} or not finite(signal.level):
        return RiskPlan(False, None, None, None, "", "", None, None, None, "No directional structural trigger.")
    direction = signal.direction
    spot, atr = indicators.spot, indicators.atr
    if not finite(spot) or not finite(atr) or atr <= 0:
        return RiskPlan(False, None, None, None, "", "", None, None, None, "Spot or ATR is unavailable.")
    meaningful_buffer = max(8.0, 0.20 * atr)
    reliable_levels = [l for l in levels if l.strength >= 0.58 or l.touches >= 2]
    supports = sorted([l for l in reliable_levels if l.kind == "SUPPORT" and l.price < spot - meaningful_buffer],
                      key=lambda x: x.price, reverse=True)
    resistances = sorted([l for l in reliable_levels if l.kind == "RESISTANCE" and l.price > spot + meaningful_buffer],
                         key=lambda x: x.price)
    buffer = max(5.0, min(20.0, atr * 0.30))
    if direction == "BULLISH":
        protect_candidates: list[tuple[float, str]] = [(l.price, l.source) for l in supports]
        if signal.level < spot - 0.5:
            protect_candidates.append((signal.level, "SIGNAL_TRIGGER_LEVEL"))
        protect_price, protect_source = max(protect_candidates, key=lambda x: x[0]) if protect_candidates else (min(indicators.swing_low, spot-atr), "SWING_LOW_FALLBACK")
        sl = protect_price - buffer
        raw_targets = [l for l in resistances if l.price > spot + max(1.0*atr, 25.0)]
        target_source_base = "MEANINGFUL_OPPOSING_STRUCTURE_OR_FIB_EXTENSION"
    else:
        protect_candidates = [(l.price, l.source) for l in resistances]
        if signal.level > spot + 0.5:
            protect_candidates.append((signal.level, "SIGNAL_TRIGGER_LEVEL"))
        protect_price, protect_source = min(protect_candidates, key=lambda x: x[0]) if protect_candidates else (max(indicators.swing_high, spot+atr), "SWING_HIGH_FALLBACK")
        sl = protect_price + buffer
        raw_targets = [l for l in supports if l.price < spot - max(1.0*atr, 25.0)]
        target_source_base = "MEANINGFUL_OPPOSING_STRUCTURE_OR_FIB_EXTENSION"
    risk = abs(spot - sl)
    if not finite(sl) or sl <= 0 or risk < 4 or risk > max(4*atr, 150):
        return RiskPlan(False, None, None, round(sl, 2) if finite(sl) else None, "STRUCTURAL_INVALIDATION", target_source_base, None,
                        round(risk, 2) if finite(risk) else None, None,
                        "Stop is invalid or structurally too distant for current volatility.")
    viable = []
    min_t1_distance = max(1.0 * atr, 25.0)
    for level in raw_targets:
        reward = abs(level.price - spot)
        rr = reward / risk if risk > 0 else 0
        if reward >= min_t1_distance and rr >= min_rr:
            viable.append((level, reward, rr))
    viable.sort(key=lambda x: x[0].price if direction == "BULLISH" else -x[0].price)
    if not viable:
        return RiskPlan(False, None, None, round(sl, 2), "STRUCTURAL_INVALIDATION", target_source_base, None, round(risk, 2), None,
                        f"No observed target meets T1 distance >= {min_t1_distance:.1f} points and reward/risk >= {min_rr:.2f}; no arbitrary target is substituted.")
    first = viable[0]
    min_t2_separation = max(0.75 * atr, 25.0)
    second = next((item for item in viable[1:] if abs(item[0].price - first[0].price) >= min_t2_separation), None)
    return RiskPlan(True, round(first[0].price, 2), round(second[0].price, 2) if second else None,
                    round(sl, 2), f"{protect_source}_PLUS_ATR_BUFFER", target_source_base,
                    round(first[1], 2), round(risk, 2), round(first[2], 2),
                    "T1 is a structural level beyond the minimum distance and reward/risk floor." +
                    (" T2 is a distinct farther structural target." if second else " T2 unavailable because no sufficiently separated credible second level exists."))


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
                    oi: Mapping[str, Any], config: Config, target_delta: float = 0.62) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    if not candidates: return None, rows
    vol_max = max((c.volume for c in candidates), default=0.0)
    step = config.strike_step
    for c in candidates:
        q = quotes.get(c.instrument_key)
        reasons: list[str] = []
        warnings: list[str] = []
        ltp = q.ltp if q and finite(q.ltp) and q.ltp > 0 else c.ltp
        if q and finite(q.bid) and finite(q.ask) and 0 < q.bid <= q.ask:
            bid, ask = q.bid, q.ask
        else:
            bid, ask = c.bid, c.ask
        volume = max(c.volume, q.volume if q else 0.0)
        spread = (ask-bid)/((ask+bid)/2) if finite(bid) and finite(ask) and 0 < bid <= ask else float("inf")
        delta = c.delta
        if not finite(delta) or delta == 0:
            reasons.append("DELTA_UNAVAILABLE")
            delta_score = 0.0
        else:
            abs_delta = abs(delta)
            delta_score = clamp(1.0 - abs(abs_delta - target_delta) / 0.32, 0, 1)
            if abs_delta < 0.50 or abs_delta > 0.85:
                warnings.append("DELTA_OUTSIDE_PREFERRED_RANGE")
        age_ok = bool(q and q.freshness == "FRESH" and finite(q.age_seconds) and -5 <= q.age_seconds <= config.max_quote_age)
        if not age_ok: reasons.append("QUOTE_STALE_OR_UNVERIFIED")
        if not finite(ltp) or ltp <= 0: reasons.append("INVALID_OPTION_PREMIUM")
        if not finite(spread) or spread > config.max_spread: reasons.append("SPREAD_LIMIT_EXCEEDED")
        if volume <= 0: reasons.append("NO_OPTION_VOLUME")
        # Contract-level options flow: growing OI with rising premium is buying activity; avoid equating OI rise with bullish writing.
        flow_score = 0.45
        wall = next((w for w in oi.get("walls", []) if abs(number(w.get("strike"), -99999)-c.strike) < 0.01), {})
        side_flow = str(wall.get("call_flow" if direction == "BULLISH" else "put_flow", "UNKNOWN"))
        if side_flow == "LONG_BUILDUP_BUYING": flow_score += 0.35
        elif side_flow == "SHORT_COVERING": flow_score += 0.25
        elif side_flow == "SHORT_BUILDUP_WRITING": flow_score -= 0.15
        else: flow_score += 0.05 if finite(c.prev_oi) and c.prev_oi > 0 and c.oi > c.prev_oi else 0.0
        volume_score = clamp(volume / vol_max, 0, 1) if vol_max > 0 else 0.0
        spread_score = clamp(1.0 - spread / config.max_spread, 0, 1) if finite(spread) else 0.0
        depth_imbalance = q.depth_imbalance if q else 0.0
        liquidity_score = 0.60*spread_score + 0.25*volume_score + 0.15*clamp((depth_imbalance + 1)/2, 0, 1)
        # Rank: contract selection quality is distinct from market setup confidence.
        total = 100 * (0.40*delta_score + 0.30*liquidity_score + 0.22*clamp(flow_score, 0, 1) + 0.08*clamp(1 - abs(spot-c.strike)/(3*step), 0, 1))
        hard_ok = (age_ok and finite(ltp) and ltp > 0 and finite(spread) and spread <= config.max_spread
                   and volume > 0 and finite(delta) and 0.45 <= abs(delta) <= 0.90)
        rows.append({
            "instrument_key": c.instrument_key, "trading_symbol": c.symbol, "side": c.side,
            "strike": c.strike, "expiry": c.expiry, "ltp": round(ltp, 2) if finite(ltp) else None,
            "delta": round(delta, 4) if finite(delta) else None, "target_abs_delta": round(target_delta, 3),
            "spread_ratio_pct": round(spread*100, 3) if finite(spread) else None,
            "quote_age_seconds": round(q.age_seconds, 2) if q and finite(q.age_seconds) else None,
            "quote_freshness": q.freshness if q else "UNAVAILABLE", "volume": volume,
            "oi": c.oi, "local_oi_flow": side_flow, "score": round(total, 2), "execution_eligible": bool(hard_ok),
            "warnings": warnings, "vetoes": reasons,
        })
    eligible = [r for r in rows if r["execution_eligible"]]
    eligible.sort(key=lambda x: (-x["score"], abs(spot-x["strike"]), x["spread_ratio_pct"] or 999))
    rows.sort(key=lambda x: (-x["score"], abs(spot-x["strike"])) )
    return (eligible[0] if eligible else None), rows


def update_active_signal(state: dict[str, Any], frame: pd.DataFrame, now: datetime) -> list[dict[str, Any]]:
    tracker = state.get("active_signal")
    if not isinstance(tracker, dict) or tracker.get("status") not in {"TRACKING", "T1_REACHED"}:
        return []
    signal_time = parse_dt(tracker.get("signal_timestamp"))
    levels = {name: number(tracker.get(name)) for name in ("T1", "T2", "SL")}
    if not signal_time:
        tracker["status"] = "INVALID_TRACKER_TIMESTAMP"
        return []
    bars = completed_candles(frame, now)
    last_checked = parse_dt(tracker.get("last_checked_candle"))
    boundary = max(signal_time, last_checked) if last_checked else signal_time
    bars = bars.loc[bars["timestamp"] > pd.Timestamp(boundary).tz_convert("UTC")] if not bars.empty else bars
    events = []
    direction = str(tracker.get("direction", "")).upper()
    for _, bar in bars.iterrows():
        high, low = number(bar["high"]), number(bar["low"])
        stamp = bar["timestamp"].to_pydatetime().astimezone(IST).isoformat()
        sl_hit = finite(levels["SL"]) and ((low <= levels["SL"]) if direction == "BULLISH" else (high >= levels["SL"]))
        t1_hit = finite(levels["T1"]) and ((high >= levels["T1"]) if direction == "BULLISH" else (low <= levels["T1"]))
        t2_hit = finite(levels["T2"]) and ((high >= levels["T2"]) if direction == "BULLISH" else (low <= levels["T2"]))
        # Conservative ambiguity policy: stop wins if stop and target occur in the same OHLC bar.
        if sl_hit:
            events.append({"type": "STRUCTURAL_STOP_REACHED", "timestamp": stamp, "level": levels["SL"], "note": "Stop-first when bar order is unknowable."})
            tracker["status"] = "STOPPED"
            tracker["terminal_timestamp"] = stamp
            break
        if t1_hit and not tracker.get("T1_reached"):
            tracker["T1_reached"] = True; tracker["status"] = "T1_REACHED"
            events.append({"type": "T1_REACHED", "timestamp": stamp, "level": levels["T1"]})
        if t2_hit and not tracker.get("T2_reached"):
            tracker["T2_reached"] = True; tracker["status"] = "T2_REACHED"
            events.append({"type": "T2_REACHED", "timestamp": stamp, "level": levels["T2"]})
            tracker["terminal_timestamp"] = stamp
            break
        tracker["last_checked_candle"] = stamp
    return events




def audit_append(config: Config, report: Mapping[str, Any]) -> None:
    config.audit_dir.mkdir(parents=True, exist_ok=True)
    local_date = parse_date(report.get("timestamp")) or now_ist().date()
    path = config.audit_dir / f"market_scan_{local_date.isoformat()}_v86.jsonl"
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
            frame_raw = self.client.candles(self.config.nifty_key, 1)
            frame = completed_candles(frame_raw, current)
            if len(frame) < 20:
                # Early-session history is a normal warm-up state, not an exception.
                # 20 closed candles provide a minimum structure/RSI context. OI snapshots
                # continue to persist, but no directional selection is permitted in warm-up.
                snap = oi_snapshot(chain, expiry, current)
                snaps = state.setdefault("chain_snapshots", [])
                if not snaps or str(snaps[-1].get("timestamp")) != str(snap.get("timestamp")):
                    snaps.append(snap)
                state["chain_snapshots"] = [x for x in snaps if isinstance(x, dict) and parse_dt(x.get("timestamp"))
                                            and parse_dt(x.get("timestamp")).date() == current.date()][-40:]
                report.update({"market_state": "WARMUP_MONITOR_ONLY", "scenario": "INSUFFICIENT_CANDLE_HISTORY",
                               "direction": "NEUTRAL", "signal_ready": False, "selected_option": None,
                               "confidence_pct": 0.0, "expiry": expiry,
                               "state_integrity": {"ok": bool(state.get("state_integrity_ok", True)),
                                                    "load_status": state.get("state_load_status"),
                                                    "snapshots_available": len(state.get("chain_snapshots", [])),
                                                    "state_path": state.get("state_file_path")},
                               "market_data_quality": {"completed_1m_candles": len(frame), "required_for_entries": 20,
                                                        "status": "WARMUP_NO_SCAN_ERROR", "oi_snapshot_persisted": True},
                               "vetoes": [f"WARMUP_ONLY_{len(frame)}_OF_20_REQUIRED_COMPLETED_1M_CANDLES;NO_ENTRY_OR_EMAIL"]})
                return self._finish(report, state)
            latest_candle_time = frame["timestamp"].iloc[-1].to_pydatetime().astimezone(IST)
            candle_age_seconds = (current - latest_candle_time).total_seconds()
            if candle_age_seconds < -5 or candle_age_seconds > self.config.max_candle_age:
                raise ScannerError(f"Latest completed NIFTY candle is stale or future-dated (age={candle_age_seconds:.1f}s; limit={self.config.max_candle_age:.1f}s).")
            indicators = indicator_set(frame_raw, spot, current)
            snapshots = state.get("chain_snapshots", []) if isinstance(state.get("chain_snapshots", []), list) else []
            oi = analyze_oi(chain, snapshots, spot, expiry, current, strike_step, self.config.scan_interval)
            fib = analyze_fibonacci(frame_raw, indicators.atr, current)
            levels = make_structure_levels(frame_raw, indicators, oi, strike_step, current, fib)
            signal, signal_diagnostics = score_market_signal(frame_raw, indicators, oi, levels, current, self.config.min_signal_score, strike_step)
            regime = classify_market_regime(frame_raw, indicators, current)
            divergence = detect_rsi_divergence(frame_raw, indicators.atr, current)
            expiry_pin = diagnose_expiry_pin(oi, fib, indicators, expiry, current, strike_step,
                                             self.config.min_local_oi_change_pct)
            local_oi_confirmation = qualify_local_oi(oi, signal, spot, strike_step, self.config.min_local_oi_change_pct)
            fib_divergence_confirmation = qualify_fib_divergence(signal, regime, fib, divergence, spot, indicators.atr)
            setup_confirmation = qualify_setup_rules(signal, frame_raw, indicators, regime,
                                                     fib_divergence_confirmation, local_oi_confirmation, current)
            regime_confirmation = qualify_regime(signal, regime, indicators, spot,
                                                 fib_divergence_confirmation, local_oi_confirmation, setup_confirmation)
            raw_signal = signal
            gate_failures = []
            if not bool(state.get("state_integrity_ok", True)):
                gate_failures.append("CANONICAL_STATE_CORRUPT_OR_UNREADABLE_ENTRIES_SUPPRESSED_FOR_RECOVERY_SCAN")
            if signal.direction in {"BULLISH", "BEARISH"}:
                if expiry_pin.get("detected"):
                    gate_failures.append("EXPIRY_PIN_NO_ENTRY")
                if not local_oi_confirmation.get("qualified"):
                    gate_failures.append(str(local_oi_confirmation.get("reason", "LOCAL_OI_GATE_FAILED")))
                if not regime_confirmation.get("qualified"):
                    gate_failures.append(str(regime_confirmation.get("reason", "REGIME_GATE_FAILED")))
                if not fib_divergence_confirmation.get("qualified"):
                    gate_failures.append(str(fib_divergence_confirmation.get("reason", "FIB_DIVERGENCE_GATE_FAILED")))
                if not setup_confirmation.get("qualified"):
                    gate_failures.append(str(setup_confirmation.get("reason", "SETUP_RULE_GATE_FAILED")))
                if gate_failures:
                    gate_evidence = tuple(dict.fromkeys(list(signal.evidence) + [f"V86_HARD_GATE:{x}" for x in gate_failures]))
                    signal = Signal("NEUTRAL", "V86_ENTRY_GATES_BLOCKED", signal.score, 0.0,
                                    "; ".join(gate_evidence[:8]), signal.level, gate_evidence, tuple(gate_failures))
            risk = calculate_risk_plan(signal, levels, indicators, self.config.min_t1_rr)
            events = update_active_signal(state, frame_raw, current)
            report["events"].extend(events)
            if events:
                event_tracker = dict(state.get("active_signal") or {})
                report["_pending_event_notifications"] = [{**event, "_tracker": event_tracker.copy()} for event in events]
            direction = signal.direction
            report.update({
                "market_state": "DIRECTIONAL_SETUP" if direction != "NEUTRAL" else "WATCH",
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
                "v86_policy": {"local_writing_oi_change_min_pct_exclusive": self.config.min_local_oi_change_pct,
                               "paired_covering_oi_decline_min_pct_exclusive": 0.5,
                               "expiry_pin": "NO_ENTRY_WHEN_EXPIRY_PIN_CONFIRMED",
                               "reversals_require_matching_confirmed_rsi_divergence_and_fib_50_61_8_confluence": True,
                               "breakout_breakdown_divergence_policy": "ONLY_CONFIRMED_OPPOSING_DIVERGENCE_VETOES; UNAVAILABLE_DIVERGENCE_IS_NOT_A_VETO",
                               "oi_flow_requires_premium_confirmation": True,
                               "trend_countertrend_entries": "FULL_FIB_DIVERGENCE_LOCAL_OI_REVERSAL_OR_STRICT_TWO_CLOSE_BREAK",
                               "sideways_whipsaw_entries": "RANGE_EDGE_FADE_WITH_FULL_CONFLUENCE_OR_STRICT_RANGE_BREAK",
                               "opposite_signal_lifecycle": "CONFIRMED_BREAK_AND_REGIME_ALIGNMENT_REQUIRED_WHILE_TRACKING_OR_AFTER_T1",
                               "same_direction_reentry_cooldown_minutes": self.config.reentry_cooldown_minutes},
                "candidate_before_v86_gates": {"direction": raw_signal.direction, "setup": raw_signal.setup,
                                                "score": raw_signal.score, "trigger": raw_signal.trigger},
                "v86_gate_failures": gate_failures,
                "active_signal": safe_json(state.get("active_signal")), "expiry": expiry,
                "state_integrity": {"ok": bool(state.get("state_integrity_ok", True)),
                                     "load_status": state.get("state_load_status"),
                                     "snapshots_available": len(state.get("chain_snapshots", [])),
                                     "state_path": state.get("state_file_path")},
                "market_data_quality": {"index_quote_freshness": index_quote.freshness if index_quote else "UNAVAILABLE",
                                        "index_quote_age_seconds": index_quote.age_seconds if index_quote else None,
                                        "completed_1m_candles": len(frame), "last_completed_candle_timestamp": latest_candle_time.isoformat(),
                                        "last_completed_candle_age_seconds": round(candle_age_seconds, 2),
                                        "volume_source": indicators.volume_source,
                                        "same_session_tactical_oi_available": oi["tactical_available"]},
            })
            if current.time() < ENTRY_OPEN:
                report["vetoes"].append("BEFORE_ENTRY_WINDOW")
            elif current.time() >= ENTRY_CUTOFF:
                report["vetoes"].append("ENTRY_CUTOFF_15_15_MONITOR_ONLY")
            elif direction == "NEUTRAL":
                report["vetoes"].append("NO_DIRECTIONAL_STRUCTURAL_SETUP")
            elif signal.score < self.config.min_signal_score:
                report["vetoes"].append("MARKET_SETUP_SCORE_BELOW_THRESHOLD")
            elif not risk.valid:
                report["vetoes"].append(f"STRUCTURAL_RISK_PLAN_INVALID:{risk.reason}")
            else:
                allowed, allow_reason = can_issue_signal_v86(
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
                    reversal_setups = {"SUPPORT_BOUNCE", "EARLY_SUPPORT_RECLAIM", "RESISTANCE_REJECTION", "EARLY_RESISTANCE_REJECTION"}
                    target_delta = 0.55 if signal.setup in reversal_setups else 0.62
                    selected, ranked = score_contracts(candidates, option_quotes, spot, direction, oi, self.config, target_delta)
                    candidate_diagnostics = [{**row, "route": "ATM_ITM1_ITM2"} for row in ranked]
                    if not selected and signal.setup in reversal_setups:
                        fallback = _candidate_strikes(spot, contracts, direction, strike_step, fallback_otm=True)
                        if reference_strikes:
                            fallback = [c for c in fallback if any(abs(c.strike - number(x, 1e9)) <= 2.0 * strike_step for x in reference_strikes)]
                        fallback_keys = [c.instrument_key for c in fallback]
                        fallback_quotes = self.client.quotes(fallback_keys) if fallback_keys else {}
                        fallback_selected, fallback_ranked = score_contracts(fallback, fallback_quotes, spot, direction, oi, self.config, target_delta)
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
                            "status": "TRACKING", "T1_reached": False, "T2_reached": False,
                            "last_checked_candle": current.isoformat(), "event_key": event_key,
                        }
                        prior = state.get("active_signal")
                        if isinstance(prior, dict):
                            hist = state.setdefault("signal_history", [])
                            hist.append(prior); state["signal_history"] = hist[-20:]
                        state["active_signal"] = tracker
                        report["_pending_signal_email"] = {"selected": selected, "signal": signal, "risk": risk, "now": current}
                        report["email_status"] = "PENDING_STATE_SAVE"
                        report["active_signal"] = safe_json(tracker)
            # Append only snapshots that represent a valid chain, and cap memory/state size.
            if chain:
                snaps = state.setdefault("chain_snapshots", [])
                snap = oi["snapshot"]
                if not snaps or str(snaps[-1].get("timestamp")) != str(snap.get("timestamp")):
                    snaps.append(snap)
                state["chain_snapshots"] = [s for s in snaps if isinstance(s, dict) and parse_dt(s.get("timestamp")) and parse_dt(s.get("timestamp")).date() == current.date()][-40:]
            report["strike_grid"] = {"step_points": strike_step, "nearby_available_strikes": [s for s in strikes if abs(s-spot) <= 300]}
            report["risk_disclaimer"] = "Rule-based scenario score is a ranking heuristic, not a calibrated probability or guarantee. Scanner provides signal research only; it places no orders."
            return self._finish(report, state)
        except Exception as exc:
            # The scan boundary is fail-closed: an unforeseen provider/schema error must not create a selection.
            LOG.exception("V86 scan failed safely")
            report.update({"market_state": "DATA_OR_SCAN_ERROR", "scenario": "NO_SELECTION", "direction": "NEUTRAL",
                           "signal_ready": False, "selected_option": None, "confidence_pct": 0.0,
                           "vetoes": [f"SCAN_ERROR:{type(exc).__name__}:{str(exc)[:350]}"]})
            report.pop("_pending_signal_email", None)
            return self._finish(report, state)

    def _signal_notification(self, report: Mapping[str, Any], selected: Mapping[str, Any],
                             signal: Signal, risk: RiskPlan, now: datetime,
                             tracker: Mapping[str, Any]) -> dict[str, Any]:
        event_key = str(tracker.get("event_key", ""))
        subject = f"NIFTY V86 {signal.direction}: {selected['strike']:.0f}{selected['side']}"
        body = (f"V86 market-structure/local-OI signal\nTime (IST): {now.strftime('%Y-%m-%d %H:%M:%S')}\n"
                f"Direction: {signal.direction}\nSetup: {signal.setup}\nStrike: {selected['strike']:.0f} {selected['side']}\n"
                f"Spot at signal: {number(report.get('indicators', {}).get('spot')):.2f}\n"
                f"Confidence heuristic: {signal.confidence_pct:.1f}/100 (not calibrated probability)\n"
                f"T1: {risk.t1}\nT2: {risk.t2 if risk.t2 is not None else 'Unavailable'}\nSL: {risk.sl}\n"
                f"Structural reason: {signal.trigger}\nOption score: {selected['score']}\n"
                "Signal only: no order was placed.")
        return {"notification_key": f"SIGNAL|{event_key}", "kind": "SIGNAL", "event_key": event_key,
                "created_at": now.isoformat(), "subject": subject, "body": body}

    def _event_notification(self, event: Mapping[str, Any]) -> Optional[dict[str, Any]]:
        tracker = event.get("_tracker") if isinstance(event.get("_tracker"), dict) else {}
        if not tracker:
            return None
        event_type = str(event.get("type", "EVENT"))
        timestamp = str(event.get("timestamp", ""))
        event_key = str(tracker.get("event_key", ""))
        key = f"EVENT|{event_key}|{event_type}|{timestamp}"
        subject = f"NIFTY V86 {event_type}: {tracker.get('strike')}{tracker.get('side')}"
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
        has_email_config = bool(self.config.email_sender and self.config.email_password and self.config.email_receiver)
        current_signal_key = ""
        current_event_keys: set[str] = set()
        if has_email_config:
            queue = state.get("pending_email_notifications", [])
            if not isinstance(queue, list):
                queue = []
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
                if send_email(self.config, str(item.get("subject", "NIFTY V86 notification")), str(item.get("body", ""))):
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
            if isinstance(pending_signal, dict):
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


def print_report(report: Mapping[str, Any]) -> None:
    print(json.dumps(safe_json(report), indent=2, ensure_ascii=False, allow_nan=False))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="V86 NIFTY regime-first market-structure and local-OI scanner (signal only)")
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
