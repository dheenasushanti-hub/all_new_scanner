#!/usr/bin/env python3
"""NIFTY 50 Fibonacci, RSI-divergence and option-OI scanner — V84.

Signals follow the user's Market Analysis & Selection spreadsheet:
* Bullish reversal: 50%-61.8% retracement support + confirmed bullish RSI divergence
  + heavy put writing at/below support + call unwinding.
* Bearish reversal: 61.8%/100% retracement resistance + confirmed bearish RSI divergence
  + heavy call writing + put unwinding.
* Bullish breakout: two completed closes above a confirmed swing/Fibonacci ceiling,
  RSI > 60, expanding upward momentum, call short-covering and fresh put writing.
* Bearish breakdown: two completed closes below a confirmed swing/Fibonacci floor,
  RSI < 40, expanding downward momentum, put short-covering and fresh call writing.
* Expiry pin: no strike selection and no signal email.

Signal-only scanner. It does not place orders. Requires UPSTOX_ANALYTICS_TOKEN.
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

VERSION = "V84-FIBONACCI-DIVERGENCE-OI-STRUCTURE"
BASE_URL = "https://api.upstox.com"
IST = ZoneInfo("Asia/Kolkata")
NIFTY_KEY_DEFAULT = "NSE_INDEX|Nifty 50"
MARKET_OPEN = time(9, 15)
ENTRY_OPEN = time(9, 16)
ENTRY_CUTOFF = time(15, 15)
MARKET_CLOSE = time(15, 30)
LOG = logging.getLogger("market_scanner_v84")
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


def round_to_grid(value: float, step: float = 50.0) -> float:
    if not finite(value) or not finite(step) or step <= 0:
        raise ValueError("A finite value and positive grid step are required.")
    return float(math.floor(float(value) / float(step) + 0.5) * float(step))

OI_SPIKE_MIN_PCT = clamp(env_float("OI_SPIKE_MIN_CHANGE_PCT", 0.003), 0.001, 0.02)
FIB_TOUCH_ATR = clamp(env_float("FIB_TOUCH_ATR", 0.25), 0.10, 0.60)
DIVERGENCE_RSI_DELTA = clamp(env_float("DIVERGENCE_RSI_DELTA", 2.0), 1.0, 10.0)


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


@dataclass(frozen=True)
class Config:
    token: str = field(default_factory=lambda: os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip())
    nifty_key: str = field(default_factory=lambda: os.getenv("NIFTY_INSTRUMENT_KEY", NIFTY_KEY_DEFAULT).strip())
    timeout: float = field(default_factory=lambda: clamp(env_float("REQUEST_TIMEOUT", 12.0), 2.0, 30.0))
    retries: int = field(default_factory=lambda: int(clamp(env_int("API_RETRIES", 3), 1, 5)))
    max_quote_age: float = field(default_factory=lambda: clamp(env_float("MAX_QUOTE_AGE_SECONDS", 30.0), 5.0, 90.0))
    max_candle_age: float = field(default_factory=lambda: clamp(env_float("MAX_CANDLE_AGE_SECONDS", 180.0), 60.0, 300.0))
    min_signal_score: float = field(default_factory=lambda: clamp(env_float("MIN_SIGNAL_SCORE", 66.0), 60.0, 85.0))
    min_t1_rr: float = field(default_factory=lambda: clamp(env_float("MIN_T1_REWARD_RISK_RATIO", 1.0), 1.0, 3.0))
    reentry_cooldown_minutes: int = field(default_factory=lambda: int(clamp(env_int("REENTRY_COOLDOWN_MINUTES", 6), 1, 30)))
    max_spread: float = field(default_factory=lambda: clamp(env_float("MAX_SPREAD_RATIO", 0.0025), 0.0005, 0.01))
    strike_step: float = 50.0
    state_file: Path = field(default_factory=lambda: Path(os.getenv("STATE_FILE", "state/market_state_v84.json")))
    audit_dir: Path = field(default_factory=lambda: Path(os.getenv("AUDIT_DIR", "audit_v84")))
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
        if not 60.0 <= self.min_signal_score <= 85.0:
            raise ScannerError("MIN_SIGNAL_SCORE must be between 60 and 85.")
        if not 1.0 <= self.min_t1_rr <= 3.0:
            raise ScannerError("MIN_T1_REWARD_RISK_RATIO must be between 1 and 3.")


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
    """Small V84 state store; safe atomic replace and same-session snapshots."""
    def __init__(self, path: Path):
        self.path = path
        self.data: dict[str, Any] = {}

    def load(self, today: date) -> dict[str, Any]:
        source_path = self.path
        # On the first V84 run, read the sibling V83 state file only as a migration source
        # when no V84 state exists. V83 active signals and email keys are never migrated.
        if not source_path.exists():
            legacy_path = self.path.with_name("market_state_v83.json")
            if legacy_path.exists():
                source_path = legacy_path
        try:
            loaded = json.loads(source_path.read_text(encoding="utf-8")) if source_path.exists() else {}
            if not isinstance(loaded, dict):
                loaded = {}
        except (OSError, json.JSONDecodeError) as exc:
            LOG.warning("State file could not be read; starting safe empty state: %s", exc)
            loaded = {}
        prior_date = parse_date(loaded.get("session_date"))
        schema_ok = loaded.get("schema_version") == 84 and loaded.get("scanner_version") == VERSION
        # A same-session V83 snapshot is structurally compatible for raw OI/premium baselines.
        # Migrate only those snapshots once; never carry V83 signal trackers or email keys into V84.
        legacy_snapshots_ok = False
        if not schema_ok and prior_date == today:
            legacy_version = str(loaded.get("scanner_version", ""))
            if loaded.get("schema_version") == 83 and legacy_version.startswith("V83-"):
                legacy_snapshots_ok = True
        old_snaps = loaded.get("chain_snapshots", []) if isinstance(loaded.get("chain_snapshots", []), list) else []
        snaps = []
        for snap in old_snaps:
            if not isinstance(snap, dict):
                continue
            stamp = parse_dt(snap.get("timestamp"))
            rows = snap.get("rows")
            if (stamp and stamp.date() == today and str(snap.get("expiry", ""))
                    and isinstance(rows, list)
                    and all(isinstance(r, dict) and all(k in r for k in ("strike", "call_oi", "put_oi", "call_ltp", "put_ltp")) for r in rows[:3])):
                snaps.append(snap)
        if prior_date != today:
            loaded = {}
            snaps = []
            schema_ok = False
            legacy_snapshots_ok = False
        snapshots_ok = schema_ok or legacy_snapshots_ok
        if legacy_snapshots_ok and snaps:
            LOG.info("Imported %d same-session raw OI snapshots from V83; prior V83 signals are not migrated.", len(snaps))
        self.data = {
            "schema_version": 84,
            "scanner_version": VERSION,
            "session_date": today.isoformat(),
            "option_expiry": str(loaded.get("option_expiry", "")) if schema_ok else "",
            "chain_snapshots": snaps[-40:] if snapshots_ok else [],
            "active_signal": loaded.get("active_signal") if schema_ok and isinstance(loaded.get("active_signal"), dict) else None,
            "signal_history": loaded.get("signal_history", []) if schema_ok and isinstance(loaded.get("signal_history", []), list) else [],
            "last_email_key": str(loaded.get("last_email_key", "")) if schema_ok else "",
            "emailed_event_keys": loaded.get("emailed_event_keys", []) if schema_ok and isinstance(loaded.get("emailed_event_keys", []), list) else [],
            "emailed_notification_keys": loaded.get("emailed_notification_keys", []) if schema_ok and isinstance(loaded.get("emailed_notification_keys", []), list) else [],
            "pending_email_notifications": loaded.get("pending_email_notifications", []) if schema_ok and isinstance(loaded.get("pending_email_notifications", []), list) else [],
            "last_scan_timestamp": loaded.get("last_scan_timestamp") if schema_ok else None,
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
                     low_minutes: float = 0.5, high_minutes: float = 7.0) -> tuple[Optional[dict[str, Any]], Optional[float]]:
    matches: list[tuple[float, dict[str, Any]]] = []
    for snap in snapshots:
        stamp = parse_dt(snap.get("timestamp"))
        if not stamp or stamp.date() != now.astimezone(IST).date() or str(snap.get("expiry", "")) != expiry:
            continue
        age = (now.astimezone(IST) - stamp).total_seconds() / 60
        if low_minutes <= age <= high_minutes:
            matches.append((age, snap))
    if not matches:
        return None, None
    age, snap = min(matches, key=lambda x: abs(x[0] - 3.0))
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
               expiry: str, now: datetime, strike_step: float) -> dict[str, Any]:
    current = oi_snapshot(chain, expiry, now)
    prior, age = _recent_snapshot(snapshots, now, expiry)
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
                "call_change_oi": (call_oi - call_old) if finite(call_old) else None,
                "put_change_oi": (put_oi - put_old) if finite(put_old) else None,
                "call_change_pct": c_change, "put_change_pct": p_change,
                "call_premium_change_pct": c_premium, "put_premium_change_pct": p_premium,
                "call_flow": classify_oi_flow(c_change, c_premium),
                "put_flow": classify_oi_flow(p_change, p_premium),
                "call_volume": number(row.get("call_volume"), 0), "put_volume": number(row.get("put_volume"), 0),
            })
    tactical_available = calls_base > 0 and puts_base > 0 and age is not None
    call_tactical = calls_delta / calls_base if calls_base > 0 else None
    put_tactical = puts_delta / puts_base if puts_base > 0 else None
    # Identify unusual positive delta-OI spikes as well as established OI walls. This allows
    # a fresh buildup to matter before its total OI becomes one of the largest walls.
    for side in ("CALL", "PUT"):
        delta_key = f"{side.lower()}_change_oi"
        positive_deltas = [number(w.get(delta_key)) for w in wall_items
                           if finite(w.get(delta_key)) and number(w.get(delta_key)) > 0]
        spike_cutoff = max(500.0, float(np.percentile(positive_deltas, 75))) if positive_deltas else float("inf")
        for w in wall_items:
            delta_oi = number(w.get(delta_key))
            w[f"{side.lower()}_oi_spike"] = bool(finite(delta_oi) and delta_oi > 0 and delta_oi >= spike_cutoff)
    # Identify established concentration walls using current OI and delta-OI flow.
    for side in ("CALL", "PUT"):
        oi_key = "call_oi" if side == "CALL" else "put_oi"
        values = sorted(((number(w[oi_key], 0), w) for w in wall_items), key=lambda item: item[0])
        cutoff = values[max(0, int(len(values) * 0.60) - 1)][0] if values else float("inf")
        for w in wall_items:
            oi = number(w[oi_key], 0)
            change = w["call_change_pct"] if side == "CALL" else w["put_change_pct"]
            flow = w["call_flow"] if side == "CALL" else w["put_flow"]
            w[f"{side.lower()}_wall"] = oi >= cutoff and oi > 0
            w[f"{side.lower()}_state"] = "BUILDING" if finite(change) and change >= 0.002 else "WEAKENING" if finite(change) and change <= -0.002 else "STABLE" if finite(change) else "UNKNOWN"
            w[f"{side.lower()}_flow"] = flow
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


def make_structure_levels(frame: pd.DataFrame, indicators: Indicators, oi: Mapping[str, Any], step: float, now: Optional[datetime] = None) -> list[Level]:
    bars = completed_candles(frame, (now or now_ist()).astimezone(IST))
    recent = bars.tail(90)
    tolerance = max(8.0, min(22.0, indicators.atr * 0.22))
    raw: list[tuple[float, str, str, float]] = []
    for val in _pivot_prices(recent, "high", "high"):
        if abs(indicators.spot - val) <= max(500, indicators.atr * 12):
            raw.append((val, "RESISTANCE", "PRICE_PIVOT_HIGH", 0.55))
    for val in _pivot_prices(recent, "low", "low"):
        if abs(indicators.spot - val) <= max(500, indicators.atr * 12):
            raw.append((val, "SUPPORT", "PRICE_PIVOT_LOW", 0.55))
    raw += [(indicators.session_high, "RESISTANCE", "SESSION_HIGH", 0.65),
            (indicators.session_low, "SUPPORT", "SESSION_LOW", 0.65)]
    for w in oi.get("walls", []):
        strike = number(w.get("strike"))
        if not finite(strike) or abs(strike - indicators.spot) > max(500, indicators.atr * 12):
            continue
        call_oi = number(w.get("call_oi"), 0)
        put_oi = number(w.get("put_oi"), 0)
        if w.get("call_wall") and strike >= indicators.spot:
            raw.append((strike, "RESISTANCE", "CALL_OI_WALL", 0.55 + 0.30 * clamp(call_oi / max(1.0, max((number(x.get("call_oi"), 0) for x in oi.get("walls", [])), default=1.0)), 0, 1)))
        if w.get("put_wall") and strike <= indicators.spot:
            raw.append((strike, "SUPPORT", "PUT_OI_WALL", 0.55 + 0.30 * clamp(put_oi / max(1.0, max((number(x.get("put_oi"), 0) for x in oi.get("walls", [])), default=1.0)), 0, 1)))
    levels: list[Level] = []
    used: set[int] = set()
    for i, (price, kind, source, strength) in enumerate(raw):
        if i in used or not finite(price):
            continue
        cluster = [(j, item) for j, item in enumerate(raw) if j not in used and item[1] == kind and abs(item[0] - price) <= tolerance]
        for j, _ in cluster: used.add(j)
        weights = [max(0.05, item[3]) for _, item in cluster]
        level_price = sum(item[0] * weight for (_, item), weight in zip(cluster, weights)) / sum(weights)
        sources = sorted({item[2] for _, item in cluster})
        matching_walls = [w for w in oi.get("walls", []) if abs(number(w.get("strike"), -999999) - level_price) <= max(tolerance, step * .15)]
        w = max(matching_walls, key=lambda x: number(x.get("call_oi" if kind == "RESISTANCE" else "put_oi"), 0), default={})
        change = number(w.get("call_change_pct" if kind == "RESISTANCE" else "put_change_pct"))
        state_key = "call_state" if kind == "RESISTANCE" else "put_state"
        flow_key = "call_flow" if kind == "RESISTANCE" else "put_flow"
        touches = sum(1 for _, x in cluster if "PIVOT" in x[2])
        cluster_strength = clamp(max(weights) + min(0.20, max(0, len(cluster)-1)*0.04), 0.0, 0.98)
        levels.append(Level(float(level_price), kind, "+".join(sources), cluster_strength, max(1, touches),
                            change if finite(change) else None, str(w.get(state_key, "UNKNOWN")), str(w.get(flow_key, "UNKNOWN")),
                            "OI-confirmed" if w else "price-structure"))
    # Do not inject every 50-point strike as a market level; strike spacing is for routing only.
    return sorted(levels, key=lambda x: x.price)


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


def _row_change(row: Mapping[str, Any], side: str) -> float:
    return number(row.get(f"{side}_change_pct"))


def _flow(row: Mapping[str, Any], side: str) -> str:
    return str(row.get(f"{side}_flow", "UNKNOWN")).upper()


def _is_heavy_writing(row: Mapping[str, Any], side: str, min_change: float = OI_SPIKE_MIN_PCT) -> bool:
    has_concentration_or_spike = bool(row.get(f"{side}_wall")) or bool(row.get(f"{side}_oi_spike"))
    return has_concentration_or_spike and _row_change(row, side) >= min_change and _flow(row, side) == "SHORT_BUILDUP_WRITING"


def _is_unwinding(row: Mapping[str, Any], side: str, min_change: float = OI_SPIKE_MIN_PCT) -> bool:
    # Both long liquidation and short covering reduce OI; premium confirms the subtype.
    return _row_change(row, side) <= -min_change and _flow(row, side) in {"SHORT_COVERING", "LONG_UNWINDING"}


def _find_heavy_writing(oi: Mapping[str, Any], side: str, reference_price: float,
                        step: float, strike_side: str) -> Optional[dict[str, Any]]:
    rows = [w for w in oi.get("walls", []) if isinstance(w, dict) and finite(w.get("strike"))]
    ref_strike = math.floor(reference_price / step) * step if strike_side == "AT_OR_BELOW" else math.ceil(reference_price / step) * step
    candidates = []
    for row in rows:
        strike = number(row.get("strike"))
        if strike_side == "AT_OR_BELOW":
            allowed = ref_strike - 2 * step <= strike <= ref_strike + 1e-6
        elif strike_side == "AT_OR_ABOVE":
            allowed = ref_strike - 1e-6 <= strike <= ref_strike + 2 * step
        else:
            allowed = abs(strike - ref_strike) <= 1.5 * step
        if allowed and _is_heavy_writing(row, side):
            candidates.append(row)
    if not candidates:
        return None
    return max(candidates, key=lambda r: (_row_change(r, side), number(r.get(f"{side}_oi"), 0)))


def _find_unwind(oi: Mapping[str, Any], side: str, spot: float, step: float,
                 direction: str) -> Optional[dict[str, Any]]:
    rows = [w for w in oi.get("walls", []) if isinstance(w, dict) and finite(w.get("strike"))]
    atm = round_to_grid(spot, step)
    candidates = []
    for row in rows:
        strike = number(row.get("strike"))
        if abs(strike - atm) > 4 * step or not _is_unwinding(row, side):
            continue
        if side == "call" and direction == "BULLISH" and strike < atm - step:
            continue
        if side == "put" and direction == "BEARISH" and strike > atm + step:
            continue
        candidates.append(row)
    if not candidates:
        return None
    return max(candidates, key=lambda r: (-_row_change(r, side), number(r.get(f"{side}_oi"), 0)))


def _find_short_covering(oi: Mapping[str, Any], side: str, spot: float, step: float,
                         boundary: float) -> Optional[dict[str, Any]]:
    rows = [w for w in oi.get("walls", []) if isinstance(w, dict) and finite(w.get("strike"))]
    candidates = []
    for row in rows:
        strike = number(row.get("strike"))
        if abs(strike - boundary) > 4 * step or _flow(row, side) != "SHORT_COVERING" or _row_change(row, side) > -OI_SPIKE_MIN_PCT:
            continue
        candidates.append(row)
    if not candidates:
        return None
    return max(candidates, key=lambda r: (-_row_change(r, side), number(r.get(f"{side}_oi"), 0)))


def _momentum_expanding(frame: pd.DataFrame, direction: str, now: Optional[datetime] = None) -> bool:
    closes = completed_candles(frame, (now or now_ist()).astimezone(IST))["close"].astype(float)
    if len(closes) < 8 or not all(finite(x) and x > 0 for x in closes.tail(8)):
        return False
    cur3 = closes.iloc[-1] / closes.iloc[-4] - 1.0
    prev3 = closes.iloc[-4] / closes.iloc[-7] - 1.0
    cur1 = closes.iloc[-1] / closes.iloc[-2] - 1.0
    if direction == "BULLISH":
        return cur1 > 0 and cur3 > 0 and cur3 > prev3 + 0.00010
    return cur1 < 0 and cur3 < 0 and cur3 < prev3 - 0.00010


def _recent_touch(frame: pd.DataFrame, level_low: float, level_high: float, side: str,
                  tolerance: float, lookback: int = 8) -> bool:
    bars = frame.tail(lookback)
    if bars.empty:
        return False
    if side == "SUPPORT":
        return bool(((bars["low"] <= level_high + tolerance) & (bars["high"] >= level_low - tolerance)).any())
    return bool(((bars["high"] >= level_low - tolerance) & (bars["low"] <= level_high + tolerance)).any())


def _pin_diagnostics(oi: Mapping[str, Any], fib: Mapping[str, Any], indicators: Indicators,
                     expiry: str, now: datetime, step: float) -> dict[str, Any]:
    try:
        expiry_date = date.fromisoformat(str(expiry)[:10])
        expiry_days = (expiry_date - now.date()).days
    except (TypeError, ValueError):
        expiry_days = 999
    up = fib.get("up_leg") if isinstance(fib.get("up_leg"), dict) else None
    down = fib.get("down_leg") if isinstance(fib.get("down_leg"), dict) else None
    support = up.get("retracements", {}).get("61.8") if up else None
    resistance = down.get("retracements", {}).get("61.8") if down else None
    fib_gap = number(resistance) - number(support) if finite(support) and finite(resistance) else float("inf")
    price_between_levels = bool(finite(support) and finite(resistance)
                                and support <= indicators.spot <= resistance)
    rows = [w for w in oi.get("walls", []) if isinstance(w, dict)]
    atm = round_to_grid(indicators.spot, step)
    matching = next((w for w in rows if abs(number(w.get("strike"), -1e9) - atm) < 0.5), None)
    both_writing = bool(matching and _is_heavy_writing(matching, "call") and _is_heavy_writing(matching, "put"))
    flat_momentum = abs(indicators.momentum_1m) < 0.0012 and abs(indicators.momentum_3m) < 0.0025
    neutral_rsi = finite(indicators.rsi) and 44 <= indicators.rsi <= 56
    pinned = bool(expiry_days <= 1 and 0 <= fib_gap <= max(1.2 * indicators.atr, 50.0)
                  and price_between_levels and both_writing and (flat_momentum or neutral_rsi))
    return {"detected": pinned, "expiry_days": expiry_days, "fib_support_61_8": support,
            "fib_resistance_61_8": resistance, "fib_gap_points": fib_gap if finite(fib_gap) else None,
            "atm_strike": atm, "price_between_fib_levels": price_between_levels,
            "same_strike_call_put_writing": both_writing,
            "flat_momentum": flat_momentum, "neutral_rsi": neutral_rsi,
            "reason": "EXPIRY_PIN_CONFLUENCE" if pinned else "PIN_CONDITIONS_NOT_COMPLETE"}


def score_market_signal(frame: pd.DataFrame, indicators: Indicators, oi: Mapping[str, Any], levels: Sequence[Level],
                        fib: Mapping[str, Any], divergence: Mapping[str, Any], expiry: str,
                        now: datetime, min_score: float, step: float) -> tuple[Signal, dict[str, Any]]:
    """Enforce the spreadsheet's four directional setups; scores rank only qualified setups."""
    spot, atr = indicators.spot, indicators.atr
    bars = completed_candles(frame, now)
    closes = bars["close"].astype(float) if not bars.empty else pd.Series(dtype=float)
    highs = bars["high"].astype(float) if not bars.empty else pd.Series(dtype=float)
    lows = bars["low"].astype(float) if not bars.empty else pd.Series(dtype=float)
    tolerance = max(10.0, min(28.0, atr * FIB_TOUCH_ATR))
    score_by_setup: dict[str, float] = {}
    candidates: list[tuple[str, str, float, float, list[str]]] = []
    diag: dict[str, Any] = {"required_oi_spike_pct": round(OI_SPIKE_MIN_PCT * 100, 3),
                            "fib_touch_tolerance_points": round(tolerance, 2), "setup_checks": {}}
    clock = now.astimezone(IST).time()
    global_blockers: list[str] = []
    if clock < ENTRY_OPEN:
        global_blockers.append("BEFORE_ENTRY_WINDOW")
    if clock >= ENTRY_CUTOFF:
        global_blockers.append("ENTRY_CUTOFF_15_15_MONITOR_ONLY")
    if len(bars) < 35:
        global_blockers.append("INSUFFICIENT_CLOSED_BARS_FOR_FIB_AND_DIVERGENCE")
    if not oi.get("tactical_available"):
        global_blockers.append("INTRADAY_OI_BASELINE_UNAVAILABLE_OR_STALE")
    if not fib.get("available"):
        global_blockers.append("CONFIRMED_FIBONACCI_SWING_UNAVAILABLE")

    pin = _pin_diagnostics(oi, fib, indicators, expiry, now, step)
    diag["expiry_pin"] = pin
    if pin["detected"]:
        sig = Signal("NEUTRAL", "RANGE_BOUND_EXPIRY_PIN", 0.0, 0.0,
                     "Close Fibonacci levels plus same-strike call/put writing and flat momentum near expiry.",
                     None, ("NO_ENTRY_EXPIRY_PIN",), tuple(global_blockers))
        diag.update({"selected_setup": sig.setup, "no_entry": True, "global_blockers": global_blockers})
        return sig, diag

    up = fib.get("up_leg") if isinstance(fib.get("up_leg"), dict) else None
    down = fib.get("down_leg") if isinstance(fib.get("down_leg"), dict) else None
    bull_zone = fib.get("bullish_support_zone") if isinstance(fib.get("bullish_support_zone"), dict) else None
    bear_res = fib.get("bearish_resistance_levels") if isinstance(fib.get("bearish_resistance_levels"), dict) else None
    bull_div = divergence.get("bullish") if isinstance(divergence.get("bullish"), dict) else None
    bear_div = divergence.get("bearish") if isinstance(divergence.get("bearish"), dict) else None
    latest_high = fib.get("latest_swing_high") if isinstance(fib.get("latest_swing_high"), dict) else None
    latest_low = fib.get("latest_swing_low") if isinstance(fib.get("latest_swing_low"), dict) else None

    # 1) Bullish reversal: 50%-61.8% retracement, bullish divergence, put writing and call unwind.
    checks = {"setup": "BULLISH_REVERSAL", "passed": False, "conditions": {}}
    if bull_zone and up and len(bars) >= 8:
        zone_low, zone_high = number(bull_zone.get("zone_low")), number(bull_zone.get("zone_high"))
        touch = _recent_touch(bars.tail(8), zone_low, zone_high, "SUPPORT", tolerance, 8)
        fib_zone = bool(touch and spot >= zone_low - tolerance and spot <= zone_high + max(2 * tolerance, 0.50 * atr))
        price_response = bool(finite(indicators.last_close) and finite(indicators.prev_close)
                              and indicators.last_close >= indicators.prev_close and indicators.last_close >= zone_low - tolerance)
        put_write = _find_heavy_writing(oi, "put", number(bull_zone.get("fib_61_8")), step, "AT_OR_BELOW") if oi.get("tactical_available") else None
        call_unwind = _find_unwind(oi, "call", spot, step, "BULLISH") if oi.get("tactical_available") else None
        conditions = {"pullback_to_fib_50_61_8": fib_zone, "bullish_rsi_divergence": bool(bull_div),
                      "heavy_put_writing_at_below_fib_support": bool(put_write), "call_unwinding": bool(call_unwind),
                      "price_response_from_support": price_response}
        passed = all(conditions.values()) and not global_blockers
        score = (30 if fib_zone else 0) + (25 if bull_div else 0) + (22 if put_write else 0) + (13 if call_unwind else 0) + (10 if price_response else 0)
        evidence = [f"FIB_50_61_8_SUPPORT_ZONE_{zone_low:.2f}_{zone_high:.2f}"] if fib_zone else []
        if bull_div: evidence.append(f"BULLISH_RSI_DIVERGENCE_PRICE_LL_{bull_div['price_low_2']:.2f}_RSI_HL_{bull_div['rsi_low_2']:.1f}")
        if put_write: evidence.append(f"HEAVY_PUT_WRITING_{number(put_write.get('strike')):.0f}_DOI_{_row_change(put_write,'put')*100:.2f}PCT")
        if call_unwind: evidence.append(f"CALL_UNWINDING_{number(call_unwind.get('strike')):.0f}_DOI_{_row_change(call_unwind,'call')*100:.2f}PCT")
        if price_response: evidence.append("CLOSED_CANDLE_RECOVERY_FROM_FIB_SUPPORT")
        checks.update({"passed": passed, "conditions": conditions, "oi_put_write": put_write, "oi_call_unwind": call_unwind})
        diag["setup_checks"]["bullish_reversal"] = checks
        score_by_setup["BULLISH_REVERSAL"] = score
        if passed and score >= min_score:
            candidates.append(("BULLISH", "BULLISH_REVERSAL", score, number(bull_zone.get("fib_61_8")), evidence))
    else:
        diag["setup_checks"]["bullish_reversal"] = {"passed": False, "conditions": {"fib_up_leg_available": bool(up), "bars_available": len(bars) >= 8}}

    # 2) Bearish reversal: a rally into 61.8%/100% resistance, bearish divergence,
    # heavy call writing and put unwinding, with a closed-candle rejection response.
    checks = {"setup": "BEARISH_REVERSAL", "passed": False, "conditions": {}}
    if bear_res and down and len(bars) >= 8:
        r61 = number(bear_res.get("fib_61_8")); r100 = number(bear_res.get("fib_100"))
        touched_618 = _recent_touch(bars.tail(8), r61 - tolerance, r61 + tolerance, "RESISTANCE", tolerance, 8)
        touched_100 = _recent_touch(bars.tail(8), r100 - tolerance, r100 + tolerance, "RESISTANCE", tolerance, 8)
        near_resistance = bool(touched_618 or touched_100)
        reference_level = r61 if touched_618 else r100
        reject = bool(near_resistance and finite(indicators.last_close) and finite(indicators.prev_close)
                      and indicators.last_close < indicators.prev_close
                      and indicators.last_close < reference_level - max(2.0, 0.04 * atr)
                      and spot <= reference_level + tolerance)
        call_write = _find_heavy_writing(oi, "call", reference_level, step, "NEAR") if oi.get("tactical_available") else None
        put_unwind = _find_unwind(oi, "put", spot, step, "BEARISH") if oi.get("tactical_available") else None
        conditions = {"rally_to_fib_61_8_or_100_resistance": near_resistance, "bearish_rsi_divergence": bool(bear_div),
                      "heavy_call_writing_at_resistance": bool(call_write), "put_unwinding": bool(put_unwind),
                      "closed_candle_rejection": reject}
        passed = all(conditions.values()) and not global_blockers
        score = (30 if near_resistance else 0) + (25 if bear_div else 0) + (22 if call_write else 0) + (13 if put_unwind else 0) + (10 if reject else 0)
        evidence = [f"FIB_RESISTANCE_RETEST_{reference_level:.2f}"] if near_resistance else []
        if bear_div: evidence.append(f"BEARISH_RSI_DIVERGENCE_PRICE_HH_{bear_div['price_high_2']:.2f}_RSI_LH_{bear_div['rsi_high_2']:.1f}")
        if call_write: evidence.append(f"HEAVY_CALL_WRITING_{number(call_write.get('strike')):.0f}_DOI_{_row_change(call_write,'call')*100:.2f}PCT")
        if put_unwind: evidence.append(f"PUT_UNWINDING_{number(put_unwind.get('strike')):.0f}_DOI_{_row_change(put_unwind,'put')*100:.2f}PCT")
        if reject: evidence.append("CLOSED_CANDLE_REJECTION_FROM_FIB_RESISTANCE")
        checks.update({"passed": passed, "conditions": conditions, "oi_call_write": call_write, "oi_put_unwind": put_unwind})
        diag["setup_checks"]["bearish_reversal"] = checks
        score_by_setup["BEARISH_REVERSAL"] = score
        if passed and score >= min_score:
            candidates.append(("BEARISH", "BEARISH_REVERSAL", score, reference_level, evidence))
    else:
        diag["setup_checks"]["bearish_reversal"] = {"passed": False, "conditions": {"fib_down_leg_available": bool(down), "bars_available": len(bars) >= 8}}

    # 3) Bullish breakout: clean closes above the latest confirmed swing-high ceiling,
    # RSI > 60, expanding momentum, no bearish divergence, call short-covering + put writing.
    boundary = number(latest_high.get("price")) if latest_high else (number(up.get("high")) if up else float("nan"))
    buf = max(4.0, min(12.0, 0.10 * atr))
    two_closes_above = bool(finite(boundary) and len(closes) >= 2 and closes.iloc[-1] > boundary + buf and closes.iloc[-2] > boundary + buf and spot > boundary + buf)
    expanding_up = _momentum_expanding(frame, "BULLISH", now)
    call_cover = _find_short_covering(oi, "call", spot, step, boundary) if finite(boundary) and oi.get("tactical_available") else None
    put_write_break = _find_heavy_writing(oi, "put", spot, step, "AT_OR_BELOW") if oi.get("tactical_available") else None
    bull_break_conditions = {"clean_break_above_fib_swing_ceiling": two_closes_above,
                             "rsi_above_60": finite(indicators.rsi) and indicators.rsi > 60,
                             "upward_momentum_expanding": expanding_up,
                             "no_bearish_rsi_divergence": not bool(bear_div) and bool(divergence.get("bearish_available")),
                             "call_short_covering": bool(call_cover), "fresh_put_writing": bool(put_write_break)}
    bull_break_score = (28 if two_closes_above else 0) + (18 if finite(indicators.rsi) and indicators.rsi > 60 else 0) + (17 if expanding_up else 0) + (12 if not bear_div and divergence.get("available") else 0) + (13 if call_cover else 0) + (12 if put_write_break else 0)
    bull_break_passed = all(bull_break_conditions.values()) and not global_blockers
    diag["setup_checks"]["bullish_breakout"] = {"passed": bull_break_passed, "conditions": bull_break_conditions,
                                                "boundary": boundary, "buffer": buf, "oi_call_short_covering": call_cover,
                                                "oi_fresh_put_writing": put_write_break}
    score_by_setup["BULLISH_BREAKOUT"] = bull_break_score
    if bull_break_passed and bull_break_score >= min_score:
        candidates.append(("BULLISH", "BULLISH_BREAKOUT", bull_break_score, boundary,
                           [f"TWO_CLOSED_CANDLES_ABOVE_FIB_CEILING_{boundary:.2f}", f"RSI_STRONG_{indicators.rsi:.1f}",
                            "UPWARD_MOMENTUM_EXPANDING", f"CALL_SHORT_COVERING_{number(call_cover.get('strike')):.0f}",
                            f"FRESH_PUT_WRITING_{number(put_write_break.get('strike')):.0f}"]))

    # 4) Bearish breakdown: mirror the bullish breakout gates.
    floor = number(latest_low.get("price")) if latest_low else (number(down.get("low")) if down else float("nan"))
    two_closes_below = bool(finite(floor) and len(closes) >= 2 and closes.iloc[-1] < floor - buf and closes.iloc[-2] < floor - buf and spot < floor - buf)
    expanding_down = _momentum_expanding(frame, "BEARISH", now)
    put_cover = _find_short_covering(oi, "put", spot, step, floor) if finite(floor) and oi.get("tactical_available") else None
    call_write_break = _find_heavy_writing(oi, "call", spot, step, "AT_OR_ABOVE") if oi.get("tactical_available") else None
    bear_break_conditions = {"clean_break_below_fib_swing_floor": two_closes_below,
                             "rsi_below_40": finite(indicators.rsi) and indicators.rsi < 40,
                             "downward_momentum_expanding": expanding_down,
                             "no_bullish_rsi_divergence": not bool(bull_div) and bool(divergence.get("bullish_available")),
                             "put_short_covering": bool(put_cover), "fresh_call_writing": bool(call_write_break)}
    bear_break_score = (28 if two_closes_below else 0) + (18 if finite(indicators.rsi) and indicators.rsi < 40 else 0) + (17 if expanding_down else 0) + (12 if not bull_div and divergence.get("available") else 0) + (13 if put_cover else 0) + (12 if call_write_break else 0)
    bear_break_passed = all(bear_break_conditions.values()) and not global_blockers
    diag["setup_checks"]["bearish_breakdown"] = {"passed": bear_break_passed, "conditions": bear_break_conditions,
                                                 "boundary": floor, "buffer": buf, "oi_put_short_covering": put_cover,
                                                 "oi_fresh_call_writing": call_write_break}
    score_by_setup["BEARISH_BREAKDOWN"] = bear_break_score
    if bear_break_passed and bear_break_score >= min_score:
        candidates.append(("BEARISH", "BEARISH_BREAKDOWN", bear_break_score, floor,
                           [f"TWO_CLOSED_CANDLES_BELOW_FIB_FLOOR_{floor:.2f}", f"RSI_WEAK_{indicators.rsi:.1f}",
                            "DOWNWARD_MOMENTUM_EXPANDING", f"PUT_SHORT_COVERING_{number(put_cover.get('strike')):.0f}",
                            f"FRESH_CALL_WRITING_{number(call_write_break.get('strike')):.0f}"]))

    diag["bull_breakout_score"] = round(bull_break_score, 1)
    diag["bear_breakdown_score"] = round(bear_break_score, 1)
    diag["setup_scores"] = {k: round(v, 1) for k, v in score_by_setup.items()}
    diag["global_blockers"] = global_blockers
    diag["min_score"] = min_score
    if global_blockers:
        sig = Signal("NEUTRAL", "OI_OR_HISTORY_NOT_READY" if "INTRADAY_OI_BASELINE_UNAVAILABLE_OR_STALE" in global_blockers else "INSUFFICIENT_MARKET_EVIDENCE",
                     0.0, 0.0, "; ".join(global_blockers), None, tuple(global_blockers), tuple(global_blockers))
        diag.update({"selected_setup": sig.setup, "no_entry": True})
        return sig, diag
    if not candidates:
        strongest = max(score_by_setup.values(), default=0.0)
        diag.update({"selected_setup": "NO_SPREADSHEET_SETUP_QUALIFIED", "no_entry": True,
                     "unmet_conditions": {name: value.get("conditions", {}) for name, value in diag["setup_checks"].items()}})
        sig = Signal("NEUTRAL", "NO_SPREADSHEET_SETUP_QUALIFIED", round(strongest, 1), 0.0,
                     "No setup satisfied every required price, divergence/momentum and local OI condition.",
                     None, ("NO_ENTRY_REQUIRED_CONFLUENCE_MISSING",), ())
        return sig, diag
    candidates.sort(key=lambda item: item[2], reverse=True)
    if len(candidates) > 1 and candidates[0][0] != candidates[1][0] and candidates[0][2] - candidates[1][2] < 8:
        sig = Signal("NEUTRAL", "CONFLICTING_QUALIFIED_SETUPS", candidates[0][2], 0.0,
                     "Bullish and bearish spreadsheet setups qualified with insufficient score separation.", None,
                     (f"TOP_SETUP_{candidates[0][1]}", f"SECOND_SETUP_{candidates[1][1]}"), ())
        diag.update({"selected_setup": sig.setup, "no_entry": True})
        return sig, diag
    direction, setup, score, level, evidence = candidates[0]
    sig = Signal(direction, setup, round(score, 1), round(clamp(score, 0, 95), 1),
                 "; ".join(evidence[:6]), float(level), tuple(evidence), ())
    diag.update({"selected_setup": setup, "no_entry": False, "qualified_setup_count": len(candidates)})
    return sig, diag


def calculate_risk_plan(signal: Signal, levels: Sequence[Level], indicators: Indicators,
                        min_rr: float, fib: Mapping[str, Any]) -> RiskPlan:
    """Place SL at market-structure invalidation and targets at the next real barrier/Fib extension."""
    if signal.direction not in {"BULLISH", "BEARISH"} or not finite(signal.level):
        return RiskPlan(False, None, None, None, "", "", None, None, None, "No qualified directional structural trigger.")
    direction, setup = signal.direction, signal.setup
    spot, atr = indicators.spot, indicators.atr
    buffer = max(6.0, min(18.0, 0.22 * atr))
    up = fib.get("up_leg") if isinstance(fib.get("up_leg"), dict) else None
    down = fib.get("down_leg") if isinstance(fib.get("down_leg"), dict) else None
    support_levels = [l for l in levels if l.kind == "SUPPORT" and l.price < spot - 0.5]
    resistance_levels = [l for l in levels if l.kind == "RESISTANCE" and l.price > spot + 0.5]
    if direction == "BULLISH":
        anchors: list[tuple[float, str]] = [(l.price, l.source) for l in support_levels]
        if setup == "BULLISH_REVERSAL" and up:
            for name in ("61.8", "78.6"):
                val = number(up.get("retracements", {}).get(name))
                if finite(val) and val < spot - 0.5:
                    anchors.append((val, f"FIB_{name}_SUPPORT"))
            if up.get("low") < spot:
                anchors.append((number(up["low"]), "CONFIRMED_SWING_LOW"))
        if setup == "BULLISH_BREAKOUT" and signal.level < spot:
            anchors.append((signal.level, "BROKEN_FIB_RESISTANCE_RETEST"))
        if not anchors:
            anchors.append((min(indicators.swing_low, spot - atr), "CONFIRMED_SWING_LOW_FALLBACK"))
        anchor, anchor_source = max(anchors, key=lambda x: x[0])
        sl = anchor - buffer
        fib_targets: list[tuple[float, str]] = []
        if up:
            for ext in ("127.2", "161.8"):
                val = number(up.get("extensions", {}).get(ext))
                if finite(val) and val > spot:
                    fib_targets.append((val, f"FIB_{ext}_EXTENSION"))
        raw_targets = [(l.price, l.source) for l in resistance_levels if l.price > spot + max(0.30 * atr, 10.0)] + fib_targets
        raw_targets.sort(key=lambda x: x[0])
    else:
        anchors = [(l.price, l.source) for l in resistance_levels]
        if setup == "BEARISH_REVERSAL" and down and signal.level > spot:
            anchors.append((signal.level, "FIB_RESISTANCE_INVALIDATION"))
            if down.get("high") > spot:
                anchors.append((number(down["high"]), "CONFIRMED_SWING_HIGH"))
        if setup == "BEARISH_BREAKDOWN" and signal.level > spot:
            anchors.append((signal.level, "BROKEN_FIB_SUPPORT_RETEST"))
        if not anchors:
            anchors.append((max(indicators.swing_high, spot + atr), "CONFIRMED_SWING_HIGH_FALLBACK"))
        anchor, anchor_source = min(anchors, key=lambda x: x[0])
        sl = anchor + buffer
        fib_targets = []
        if down:
            for ext in ("127.2", "161.8"):
                val = number(down.get("extensions", {}).get(ext))
                if finite(val) and val < spot:
                    fib_targets.append((val, f"FIB_{ext}_EXTENSION"))
        raw_targets = [(l.price, l.source) for l in support_levels if l.price < spot - max(0.30 * atr, 10.0)] + fib_targets
        raw_targets.sort(key=lambda x: x[0], reverse=True)
    risk = abs(spot - sl)
    if not finite(sl) or sl <= 0 or risk < 5 or risk > max(4.0 * atr, 180.0):
        return RiskPlan(False, None, None, round(sl, 2) if finite(sl) else None,
                        f"{anchor_source}_PLUS_ATR_BUFFER", "", None, round(risk, 2) if finite(risk) else None,
                        None, "Stop is invalid or too close/far relative to underlying volatility.")
    # Preserve the first meaningful opposing barrier; never skip a nearby structural obstacle
    # merely because a farther Fib extension provides a better reward/risk ratio.
    unique_targets: list[tuple[float, str]] = []
    merge_tolerance = max(5.0, 0.12 * atr)
    for price, source in raw_targets:
        if not finite(price) or abs(price - spot) < max(0.30 * atr, 10.0):
            continue
        if not unique_targets or abs(price - unique_targets[-1][0]) > merge_tolerance:
            unique_targets.append((float(price), str(source)))
        elif "FIB_" in source and "FIB_" not in unique_targets[-1][1]:
            unique_targets[-1] = (unique_targets[-1][0], unique_targets[-1][1] + "+" + source)
    if not unique_targets:
        return RiskPlan(False, None, None, round(sl, 2), f"{anchor_source}_PLUS_ATR_BUFFER", "",
                        None, round(risk, 2), None, "No opposing structural level or Fib extension is available for T1.")
    t1, t1_source = unique_targets[0]
    reward = abs(t1 - spot)
    rr = reward / risk if risk > 0 else 0.0
    if (direction == "BULLISH" and t1 <= spot) or (direction == "BEARISH" and t1 >= spot) or rr < min_rr:
        return RiskPlan(False, round(t1, 2), None, round(sl, 2), f"{anchor_source}_PLUS_ATR_BUFFER", t1_source,
                        round(reward, 2), round(risk, 2), round(rr, 2),
                        f"Nearest meaningful T1 fails direction or minimum reward/risk ({rr:.2f} < {min_rr:.2f}); entry rejected.")
    t2 = None
    t2_source = None
    for price, source in unique_targets[1:]:
        if (direction == "BULLISH" and price > t1 + merge_tolerance) or (direction == "BEARISH" and price < t1 - merge_tolerance):
            t2, t2_source = price, source
            break
    target_source = f"T1={t1_source}" + (f"; T2={t2_source}" if t2_source else "; T2_UNAVAILABLE")
    reason = "T1 is the nearest meaningful opposing price/OI/Fibonacci barrier; SL is structural invalidation plus an ATR-scaled buffer."
    if t2 is None:
        reason += " No second distinct confirmed target was available; no synthetic T2 was invented."
    return RiskPlan(True, round(t1, 2), round(t2, 2) if t2 is not None else None, round(sl, 2),
                    f"{anchor_source}_PLUS_ATR_BUFFER", target_source, round(reward, 2), round(risk, 2), round(rr, 2), reason)


def _candidate_strikes(spot: float, contracts: Mapping[tuple[float, str], Contract], direction: str, step: float,
                       setup: str = "") -> list[Contract]:
    """Select only real 50-point-grid strikes in the spreadsheet's directional ATM window."""
    side = "CE" if direction == "BULLISH" else "PE"
    atm = round_to_grid(spot, step)
    if direction == "BULLISH":
        preferred = [atm, atm - step, atm - 2 * step]
        if "BREAKOUT" not in setup:
            preferred.append(atm + step)  # Sheet1's one-strike OTM reversal fallback.
    else:
        preferred = [atm, atm + step, atm + 2 * step]
        if "BREAKDOWN" not in setup:
            preferred.append(atm - step)  # Sheet1's one-strike OTM reversal fallback.
    available: dict[float, Contract] = {}
    for (strike, opt_side), contract in contracts.items():
        if opt_side != side or not contract.instrument_key:
            continue
        # Do not synthesize or accidentally route an irregular strike.
        grid = round(float(strike) / step) * step
        if abs(float(strike) - grid) > 0.5:
            continue
        if float(strike) in preferred:
            available[float(strike)] = contract
    return [available[float(strike)] for strike in preferred if float(strike) in available]


def score_contracts(candidates: Sequence[Contract], quotes: Mapping[str, Quote], spot: float, direction: str,
                    oi: Mapping[str, Any], config: Config, target_delta: float = 0.60,
                    setup: str = "") -> tuple[Optional[dict[str, Any]], list[dict[str, Any]]]:
    """Rank only the spreadsheet's nearby 50-point contracts; hard checks precede ranking."""
    rows: list[dict[str, Any]] = []
    if not candidates:
        return None, rows
    atm = round_to_grid(spot, config.strike_step)
    vol_max = max((max(c.volume, 0.0) for c in candidates), default=0.0)
    oi_rows = [w for w in oi.get("walls", []) if isinstance(w, dict) and finite(w.get("strike"))]
    support_wall = max((w for w in oi_rows if w.get("put_wall") and _is_heavy_writing(w, "put")),
                       key=lambda w: number(w.get("put_change_pct"), -99), default=None)
    resistance_wall = max((w for w in oi_rows if w.get("call_wall") and _is_heavy_writing(w, "call")),
                          key=lambda w: number(w.get("call_change_pct"), -99), default=None)
    for c in candidates:
        q = quotes.get(c.instrument_key)
        reasons: list[str] = []
        warnings: list[str] = []
        ltp = q.ltp if q and finite(q.ltp) and q.ltp > 0 else c.ltp
        bid = q.bid if q and finite(q.bid) else c.bid
        ask = q.ask if q and finite(q.ask) else c.ask
        volume = max(c.volume, q.volume if q else 0.0)
        spread = (ask - bid) / ((ask + bid) / 2.0) if finite(bid) and finite(ask) and 0 < bid <= ask else float("inf")
        delta = c.delta
        abs_delta = abs(delta) if finite(delta) else float("nan")
        delta_score = clamp(1 - abs(abs_delta - target_delta) / 0.35, 0, 1) if finite(abs_delta) else 0.0
        age_ok = bool(q and q.freshness == "FRESH" and finite(q.age_seconds) and -5 <= q.age_seconds <= config.max_quote_age)
        if not age_ok: reasons.append("QUOTE_STALE_OR_UNVERIFIED")
        if not finite(ltp) or ltp <= 0: reasons.append("INVALID_OPTION_PREMIUM")
        if not finite(spread) or spread > config.max_spread: reasons.append("SPREAD_LIMIT_EXCEEDED")
        if volume <= 0: reasons.append("NO_OPTION_VOLUME")
        if not finite(abs_delta) or not 0.40 <= abs_delta <= 0.90: reasons.append("DELTA_OUTSIDE_EXECUTION_RANGE")
        strike_offset = (c.strike - atm) / config.strike_step
        if direction == "BULLISH":
            if strike_offset == 0: role_score = 1.00
            elif strike_offset == -1: role_score = 0.88
            elif strike_offset == -2: role_score = 0.76
            else: role_score = 0.42
        else:
            if strike_offset == 0: role_score = 1.00
            elif strike_offset == 1: role_score = 0.88
            elif strike_offset == 2: role_score = 0.76
            else: role_score = 0.42
        if "BREAKOUT" in setup or "BREAKDOWN" in setup:
            role_score = 1.0 if strike_offset == 0 else max(0.3, role_score - 0.12)
        wall = next((w for w in oi_rows if abs(number(w.get("strike"), -999999) - c.strike) <= 0.5), {})
        own_flow = _flow(wall, "call" if direction == "BULLISH" else "put")
        flow_score = 0.50
        if own_flow == "LONG_BUILDUP_BUYING": flow_score += 0.30
        elif own_flow == "SHORT_COVERING": flow_score += 0.20
        elif own_flow == "SHORT_BUILDUP_WRITING": flow_score -= 0.15
        if direction == "BULLISH" and support_wall:
            wall_dist = abs(c.strike - number(support_wall.get("strike")))
            support_alignment = clamp(1 - wall_dist / (4 * config.strike_step), 0, 1)
        elif direction == "BEARISH" and resistance_wall:
            wall_dist = abs(c.strike - number(resistance_wall.get("strike")))
            support_alignment = clamp(1 - wall_dist / (4 * config.strike_step), 0, 1)
        else:
            support_alignment = 0.25
        volume_score = clamp(volume / vol_max, 0, 1) if vol_max > 0 else 0.0
        spread_score = clamp(1.0 - spread / config.max_spread, 0, 1) if finite(spread) else 0.0
        depth_score = clamp(((q.depth_imbalance if q else 0.0) + 1) / 2, 0, 1)
        liquidity_score = 0.65 * spread_score + 0.25 * volume_score + 0.10 * depth_score
        total = 100 * (0.32 * role_score + 0.24 * delta_score + 0.24 * liquidity_score
                       + 0.12 * clamp(flow_score, 0, 1) + 0.08 * support_alignment)
        eligible = not reasons
        rows.append({
            "instrument_key": c.instrument_key, "trading_symbol": c.symbol, "side": c.side,
            "strike": c.strike, "expiry": c.expiry, "ltp": round(ltp, 2) if finite(ltp) else None,
            "delta": round(delta, 4) if finite(delta) else None, "target_abs_delta": round(target_delta, 3),
            "atm_strike": atm, "strike_offset_from_atm": int(round(strike_offset)),
            "spread_ratio_pct": round(spread * 100, 3) if finite(spread) else None,
            "quote_age_seconds": round(q.age_seconds, 2) if q and finite(q.age_seconds) else None,
            "quote_freshness": q.freshness if q else "UNAVAILABLE", "volume": volume,
            "oi": c.oi, "local_oi_flow": own_flow, "oi_wall_alignment": round(support_alignment, 3),
            "strike_role_score": round(role_score, 3), "score": round(total, 2),
            "execution_eligible": bool(eligible), "warnings": warnings, "vetoes": reasons,
        })
    eligible = [r for r in rows if r["execution_eligible"]]
    eligible.sort(key=lambda r: (-r["score"], abs(r["strike"] - atm), r["spread_ratio_pct"] if r["spread_ratio_pct"] is not None else 999))
    rows.sort(key=lambda r: (-r["score"], abs(r["strike"] - atm)))
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


def can_issue_signal(state: Mapping[str, Any], new_signal: Signal, now: Optional[datetime] = None,
                    cooldown_minutes: int = 6) -> tuple[bool, str]:
    active = state.get("active_signal")
    if not isinstance(active, dict):
        return True, "NO_ACTIVE_SIGNAL"
    status = str(active.get("status", "")).upper()
    active_direction = str(active.get("direction", "")).upper()
    if status in {"TRACKING", "T1_REACHED"}:
        if active_direction == new_signal.direction:
            return False, "SAME_DIRECTION_SIGNAL_ALREADY_TRACKING"
        if status == "T1_REACHED" or active.get("T1_reached"):
            return True, "OPPOSITE_SETUP_ALLOWED_AFTER_T1"
        return False, "ACTIVE_SIGNAL_PROTECTED_UNTIL_T1_OR_STRUCTURAL_STOP"
    # Prevent repeated same-direction entries on the same structure after a terminal event;
    # the opposite direction remains eligible when its own setup/risk gates pass.
    terminal = parse_dt(active.get("terminal_timestamp"))
    reference = (now or now_ist()).astimezone(IST)
    if active_direction == new_signal.direction and terminal and (reference - terminal).total_seconds() < max(1, cooldown_minutes) * 60:
        return False, "SAME_DIRECTION_REENTRY_COOLDOWN"
    return True, "TERMINAL_SIGNAL_OR_OPPOSITE_SETUP"


def audit_append(config: Config, report: Mapping[str, Any]) -> None:
    config.audit_dir.mkdir(parents=True, exist_ok=True)
    local_date = parse_date(report.get("timestamp")) or now_ist().date()
    path = config.audit_dir / f"market_scan_{local_date.isoformat()}_v84.jsonl"
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
                                  "selected_option": None, "vetoes": [], "events": []}
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
            # NIFTY contracts in the supplied specification use a fixed 50-point grid.
            # Never infer a wider interval just because an API response omits some contracts.
            strike_step = 50.0
            index_quote_map = self.client.quotes([self.config.nifty_key])
            index_quote = index_quote_map.get(self.config.nifty_key)
            spot = index_quote.ltp if index_quote and finite(index_quote.ltp) and index_quote.ltp > 0 else float("nan")
            if not finite(spot):
                raise ScannerError("Fresh NIFTY index LTP was not returned; refusing a stale or inferred spot.")
            if not index_quote or index_quote.freshness != "FRESH" or not finite(index_quote.age_seconds) or not (-5 <= index_quote.age_seconds <= self.config.max_quote_age):
                raise ScannerError("NIFTY index quote is stale or its timestamp cannot be verified; refusing to build levels from it.")
            frame_raw = self.client.candles(self.config.nifty_key, 1)
            frame = completed_candles(frame_raw, current)
            if len(frame) < 8:
                raise ScannerError(f"Only {len(frame)} completed NIFTY one-minute candles are available; at least 8 are required.")
            latest_candle_time = frame["timestamp"].iloc[-1].to_pydatetime().astimezone(IST)
            candle_age_seconds = (current - latest_candle_time).total_seconds()
            if candle_age_seconds < -5 or candle_age_seconds > self.config.max_candle_age:
                raise ScannerError(f"Latest completed NIFTY candle is stale or future-dated (age={candle_age_seconds:.1f}s; limit={self.config.max_candle_age:.1f}s).")
            indicators = indicator_set(frame_raw, spot, current)
            snapshots = state.get("chain_snapshots", []) if isinstance(state.get("chain_snapshots", []), list) else []
            oi = analyze_oi(chain, snapshots, spot, expiry, current, strike_step)
            fib = analyze_fibonacci(frame_raw, indicators.atr, current)
            divergence = detect_rsi_divergence(frame_raw, indicators.atr, current)
            levels = make_structure_levels(frame_raw, indicators, oi, strike_step, current)
            signal, signal_diagnostics = score_market_signal(frame_raw, indicators, oi, levels, fib, divergence, expiry, current, self.config.min_signal_score, strike_step)
            risk = calculate_risk_plan(signal, levels, indicators, self.config.min_t1_rr, fib)
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
                "fibonacci_analysis": safe_json(fib), "rsi_divergence": safe_json(divergence),
                "oi_analysis": {k: safe_json(v) for k, v in oi.items() if k != "snapshot"},
                "signal_diagnostics": signal_diagnostics, "risk_plan": safe_json(asdict(risk)),
                "active_signal": safe_json(state.get("active_signal")), "expiry": expiry,
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
                allowed, allow_reason = can_issue_signal(state, signal, current, self.config.reentry_cooldown_minutes)
                report["active_signal_gate"] = {"allowed": allowed, "reason": allow_reason}
                if not allowed:
                    report["vetoes"].append(allow_reason)
                else:
                    candidates = _candidate_strikes(spot, contracts, direction, strike_step, signal.setup)
                    candidate_keys = [c.instrument_key for c in candidates]
                    option_quotes = self.client.quotes(candidate_keys)
                    # Reversal entries favour moderately ITM contracts; momentum entries prioritise ATM.
                    target_delta = 0.58 if "REVERSAL" in signal.setup else 0.52
                    selected, ranked = score_contracts(candidates, option_quotes, spot, direction, oi, self.config, target_delta, signal.setup)
                    report["candidate_diagnostics"] = ranked
                    if not selected:
                        report["vetoes"].append("NO_NEARBY_CONTRACT_PASSED_QUOTE_SPREAD_VOLUME_AND_DELTA_GATES")
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
            report["strategy_specification"] = {
                "source": "Market Analysis & Selection.xlsx",
                "fibonacci_retracements_pct": [38.2, 50.0, 61.8, 78.6],
                "fibonacci_extensions_pct": [127.2, 161.8],
                "bullish_reversal": "Fib 50%-61.8% support + confirmed bullish RSI divergence + heavy put writing + call unwinding",
                "bearish_reversal": "Fib 61.8%/100% resistance + confirmed bearish RSI divergence + heavy call writing + put unwinding",
                "bullish_breakout": "Two completed closes above swing/Fib ceiling + RSI>60 + expanding momentum + call short-covering + fresh put writing; no bearish divergence",
                "bearish_breakdown": "Two completed closes below swing/Fib floor + RSI<40 + expanding momentum + put short-covering + fresh call writing; no bullish divergence",
                "expiry_pin": "No entry and no signal email when same-strike call/put writing and close Fib levels align near expiry",
                "oi_spike_min_change_pct": round(OI_SPIKE_MIN_PCT * 100, 3),
                "state_persistence_required": "Same-session V84 state/snapshots must persist between scheduled runs to classify intraday OI changes.",
            }
            report["risk_disclaimer"] = "Confidence is a rule-based score, not a calibrated probability or guarantee. Fibonacci targets are confluence references, not price forecasts. Scanner provides signal research only; it places no orders."
            return self._finish(report, state)
        except Exception as exc:
            # The scan boundary is fail-closed: an unforeseen provider/schema error must not create a selection.
            LOG.exception("V84 scan failed safely")
            report.update({"market_state": "DATA_OR_SCAN_ERROR", "scenario": "NO_SELECTION", "direction": "NEUTRAL",
                           "signal_ready": False, "selected_option": None, "confidence_pct": 0.0,
                           "vetoes": [f"SCAN_ERROR:{type(exc).__name__}:{str(exc)[:350]}"]})
            report.pop("_pending_signal_email", None)
            return self._finish(report, state)

    def _signal_notification(self, report: Mapping[str, Any], selected: Mapping[str, Any],
                             signal: Signal, risk: RiskPlan, now: datetime,
                             tracker: Mapping[str, Any]) -> dict[str, Any]:
        event_key = str(tracker.get("event_key", ""))
        subject = f"NIFTY V84 {signal.direction}: {selected['strike']:.0f}{selected['side']}"
        body = (f"V84 Fibonacci/divergence/OI signal\nTime (IST): {now.strftime('%Y-%m-%d %H:%M:%S')}\n"
                f"NIFTY Spot Price: {number(report.get('indicators', {}).get('spot')):.2f}\n"
                f"Setup: {signal.setup} ({signal.direction})\nStrike Selected: {selected['strike']:.0f} {selected['side']}\n"
                f"Strike Selected Price: {number(selected.get('ltp')):.2f}\n"
                f"Confidence (heuristic): {signal.confidence_pct:.1f}/100; not a calibrated probability\n"
                f"T1: {risk.t1}\nT2: {risk.t2 if risk.t2 is not None else 'Unavailable: no second structural target'}\nSL: {risk.sl}\n"
                f"Structural reason: {signal.trigger}\nOption score: {selected['score']}\n"
                f"Fibonacci: {json.dumps(safe_json(report.get('fibonacci_analysis', {})), ensure_ascii=False)}\n"
                f"RSI divergence: {json.dumps(safe_json(report.get('rsi_divergence', {})), ensure_ascii=False)}\n"
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
        subject = f"NIFTY V84 {event_type}: {tracker.get('strike')}{tracker.get('side')}"
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
                if send_email(self.config, str(item.get("subject", "NIFTY V84 notification")), str(item.get("body", ""))):
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
    parser = argparse.ArgumentParser(description="V84 NIFTY market-structure and OI-flow scanner (signal only)")
    parser.add_argument("--loop", action="store_true", help="run continuously at SCAN_INTERVAL_SECONDS")
    parser.add_argument("--interval", type=int, default=None, help="override the loop interval in seconds")
    args = parser.parse_args(argv)
    config = Config()
    try:
        config.validate()
    except ScannerError as exc:
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
