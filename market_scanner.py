#!/usr/bin/env python3
"""NIFTY 50 market-structure and option-strike scanner — V83.

V83 is a standalone redesign, not a patch on V82. It identifies price-tested levels,
tracks local option OI and premium changes across this scanner's own snapshots, scores
reversal/breakout setups, routes only liquid nearby 50-point NIFTY option strikes, and
derives underlying T1/T2/SL from observed structure. It never places orders.

Required environment: UPSTOX_ANALYTICS_TOKEN
Optional: NIFTY_INSTRUMENT_KEY, STATE_FILE, AUDIT_DIR, SCAN_INTERVAL_SECONDS,
REQUEST_TIMEOUT, API_RETRIES, MAX_QUOTE_AGE_SECONDS, MAX_CANDLE_AGE_SECONDS, MIN_SIGNAL_SCORE,
MIN_T1_REWARD_RISK_RATIO, REENTRY_COOLDOWN_MINUTES, MAX_SPREAD_RATIO, EMAIL_SENDER, EMAIL_PASSWORD,
EMAIL_RECEIVER, SMTP_HOST, SMTP_PORT, LOG_LEVEL.

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

VERSION = "V83-MARKET-STRUCTURE-OI-FLOW-LEAN"
BASE_URL = "https://api.upstox.com"
IST = ZoneInfo("Asia/Kolkata")
NIFTY_KEY_DEFAULT = "NSE_INDEX|Nifty 50"
MARKET_OPEN = time(9, 15)
ENTRY_OPEN = time(9, 16)
ENTRY_CUTOFF = time(15, 15)
MARKET_CLOSE = time(15, 30)
LOG = logging.getLogger("market_scanner_v83")
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
    state_file: Path = field(default_factory=lambda: Path(os.getenv("STATE_FILE", "state/market_state_v83.json")))
    audit_dir: Path = field(default_factory=lambda: Path(os.getenv("AUDIT_DIR", "audit_v83")))
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
    """Small V83 state store; safe atomic replace and same-session snapshots."""
    def __init__(self, path: Path):
        self.path = path
        self.data: dict[str, Any] = {}

    def load(self, today: date) -> dict[str, Any]:
        try:
            loaded = json.loads(self.path.read_text(encoding="utf-8")) if self.path.exists() else {}
            if not isinstance(loaded, dict):
                loaded = {}
        except (OSError, json.JSONDecodeError) as exc:
            LOG.warning("State file could not be read; starting safe empty state: %s", exc)
            loaded = {}
        prior_date = parse_date(loaded.get("session_date"))
        schema_ok = loaded.get("schema_version") == 83 and loaded.get("scanner_version") == VERSION
        # Only import V83 snapshots with the expected schema. Legacy signal trackers and
        # email dedupe state are deliberately not migrated across scanner versions.
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
        self.data = {
            "schema_version": 83,
            "scanner_version": VERSION,
            "session_date": today.isoformat(),
            "option_expiry": str(loaded.get("option_expiry", "")) if schema_ok else "",
            "chain_snapshots": snaps[-40:] if schema_ok else [],
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
                "call_change_pct": c_change, "put_change_pct": p_change,
                "call_premium_change_pct": c_premium, "put_premium_change_pct": p_premium,
                "call_flow": classify_oi_flow(c_change, c_premium),
                "put_flow": classify_oi_flow(p_change, p_premium),
                "call_volume": number(row.get("call_volume"), 0), "put_volume": number(row.get("put_volume"), 0),
            })
    tactical_available = calls_base > 0 and puts_base > 0 and age is not None
    call_tactical = calls_delta / calls_base if calls_base > 0 else None
    put_tactical = puts_delta / puts_base if puts_base > 0 else None
    # Identify walls by concentration around nearby strikes, not by raw OI alone.
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
    crossed_resistances = [l for l in levels if l.kind == "RESISTANCE" and l.price < spot]
    crossed_supports = [l for l in levels if l.kind == "SUPPORT" and l.price > spot]
    crossed_resistance = max(crossed_resistances, key=lambda l: l.price, default=None)
    crossed_support = min(crossed_supports, key=lambda l: l.price, default=None)
    if crossed_resistance and len(closes) >= 2 and float(closes.iloc[-1]) > crossed_resistance.price + buf and float(closes.iloc[-2]) > crossed_resistance.price + buf:
        bull_struct = max(bull_struct, 52)
        bull_ev += [f"TWO_CLOSE_BREAKOUT_{crossed_resistance.price:.2f}"]
        setup_bull, level_bull = "CONFIRMED_BREAKOUT", crossed_resistance.price
    if crossed_support and len(closes) >= 2 and float(closes.iloc[-1]) < crossed_support.price - buf and float(closes.iloc[-2]) < crossed_support.price - buf:
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


def calculate_risk_plan(signal: Signal, levels: Sequence[Level], indicators: Indicators, min_rr: float) -> RiskPlan:
    if signal.direction not in {"BULLISH", "BEARISH"} or not signal.level:
        return RiskPlan(False, None, None, None, "", "", None, None, None, "No directional structural trigger.")
    direction = signal.direction
    spot, atr = indicators.spot, indicators.atr
    meaningful_buffer = max(8.0, 0.20 * atr)
    supports = sorted([l for l in levels if l.kind == "SUPPORT" and l.price < spot - meaningful_buffer], key=lambda x: x.price, reverse=True)
    resistances = sorted([l for l in levels if l.kind == "RESISTANCE" and l.price > spot + meaningful_buffer], key=lambda x: x.price)
    buffer = max(5.0, min(20.0, atr * 0.30))
    if direction == "BULLISH":
        # A reclaimed/broken resistance becomes a support candidate; a support-bounce level
        # remains the primary invalidation boundary. This prevents a generic distant stop.
        protect_candidates: list[tuple[float, str]] = [(l.price, l.source) for l in supports]
        if signal.level < spot - 0.5:
            protect_candidates.append((signal.level, "SIGNAL_TRIGGER_LEVEL"))
        protect_price, protect_source = max(protect_candidates, key=lambda x: x[0]) if protect_candidates else (min(indicators.swing_low, spot-atr), "SWING_LOW_FALLBACK")
        sl = protect_price - buffer
        raw_targets = [l for l in resistances if l.price > spot + max(0.45*atr, 12.0)]
        targets = raw_targets
        target_source_base = "OPPOSING_PRICE_STRUCTURE_OR_CALL_OI_WALL"
    else:
        # A broken support becomes resistance for the invalidation stop.
        protect_candidates = [(l.price, l.source) for l in resistances]
        if signal.level > spot + 0.5:
            protect_candidates.append((signal.level, "SIGNAL_TRIGGER_LEVEL"))
        protect_price, protect_source = min(protect_candidates, key=lambda x: x[0]) if protect_candidates else (max(indicators.swing_high, spot+atr), "SWING_HIGH_FALLBACK")
        sl = protect_price + buffer
        raw_targets = [l for l in supports if l.price < spot - max(0.45*atr, 12.0)]
        targets = raw_targets
        target_source_base = "OPPOSING_PRICE_STRUCTURE_OR_PUT_OI_WALL"
    risk = abs(spot - sl)
    if not finite(sl) or sl <= 0 or risk < 4 or risk > max(4*atr, 150):
        return RiskPlan(False, None, None, round(sl, 2) if finite(sl) else None, "STRUCTURAL_INVALIDATION", "", None, round(risk, 2) if finite(risk) else None, None, "Stop is invalid or structurally too distant.")
    viable = []
    for level in targets:
        reward = abs(level.price - spot)
        rr = reward / risk if risk > 0 else 0
        # Ignore micro pivots; require a target that can reasonably pay the structural risk.
        if reward >= max(0.45*atr, 12.0) and rr >= min_rr:
            viable.append((level, reward, rr))
    if not viable:
        return RiskPlan(False, None, None, round(sl, 2), "STRUCTURAL_INVALIDATION", target_source_base, None, round(risk, 2), None,
                        "No observed opposing structural level meets minimum reward/risk; refusing an arbitrary grid/ATR target.")
    viable.sort(key=lambda x: x[0].price if direction == "BULLISH" else -x[0].price)
    first = viable[0]
    second = viable[1] if len(viable) > 1 else None
    return RiskPlan(True, round(first[0].price, 2), round(second[0].price, 2) if second else None, round(sl, 2),
                    f"{protect_source}_PLUS_ATR_BUFFER", target_source_base,
                    round(first[1], 2), round(risk, 2), round(first[2], 2),
                    "Structural levels pass the configured reward/risk floor." + (" T2 available." if second else " T2 unavailable; T1 remains structural."))


def _candidate_strikes(spot: float, contracts: Mapping[tuple[float, str], Contract], direction: str, step: float) -> list[Contract]:
    """Compare a five-contract local window; never invent strikes missing from the chain."""
    side = "CE" if direction == "BULLISH" else "PE"
    available = [c for (strike, opt_side), c in contracts.items()
                 if opt_side == side and abs(float(strike) - spot) <= 3.0 * step]
    # Distance establishes a local window, but contract scoring—not an ITM-only shortcut—
    # chooses among ATM, slightly OTM, and ITM candidates.
    available.sort(key=lambda c: (abs(spot - c.strike), c.strike))
    picked: list[Contract] = []
    seen: set[float] = set()
    for c in available:
        if c.strike in seen or not c.instrument_key:
            continue
        seen.add(c.strike)
        picked.append(c)
        if len(picked) == 5:
            break
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
    path = config.audit_dir / f"market_scan_{local_date.isoformat()}_v83.jsonl"
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
            if len(frame) < 8:
                raise ScannerError(f"Only {len(frame)} completed NIFTY one-minute candles are available; at least 8 are required.")
            latest_candle_time = frame["timestamp"].iloc[-1].to_pydatetime().astimezone(IST)
            candle_age_seconds = (current - latest_candle_time).total_seconds()
            if candle_age_seconds < -5 or candle_age_seconds > self.config.max_candle_age:
                raise ScannerError(f"Latest completed NIFTY candle is stale or future-dated (age={candle_age_seconds:.1f}s; limit={self.config.max_candle_age:.1f}s).")
            indicators = indicator_set(frame_raw, spot, current)
            snapshots = state.get("chain_snapshots", []) if isinstance(state.get("chain_snapshots", []), list) else []
            oi = analyze_oi(chain, snapshots, spot, expiry, current, strike_step)
            levels = make_structure_levels(frame_raw, indicators, oi, strike_step, current)
            signal, signal_diagnostics = score_market_signal(frame_raw, indicators, oi, levels, current, self.config.min_signal_score, strike_step)
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
                    candidates = _candidate_strikes(spot, contracts, direction, strike_step)
                    candidate_keys = [c.instrument_key for c in candidates]
                    option_quotes = self.client.quotes(candidate_keys)
                    # Use a near-ATM delta preference for early reversals; confirmed bounce/breakout
                    # structures prefer a higher-delta contract that tracks the underlying more directly.
                    target_delta = 0.55 if signal.setup in {"EARLY_RESISTANCE_REJECTION", "EARLY_SUPPORT_RECLAIM"} else 0.62
                    selected, ranked = score_contracts(candidates, option_quotes, spot, direction, oi, self.config, target_delta)
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
            report["risk_disclaimer"] = "Rule-based scenario score is a ranking heuristic, not a calibrated probability or guarantee. Scanner provides signal research only; it places no orders."
            return self._finish(report, state)
        except Exception as exc:
            # The scan boundary is fail-closed: an unforeseen provider/schema error must not create a selection.
            LOG.exception("V83 scan failed safely")
            report.update({"market_state": "DATA_OR_SCAN_ERROR", "scenario": "NO_SELECTION", "direction": "NEUTRAL",
                           "signal_ready": False, "selected_option": None, "confidence_pct": 0.0,
                           "vetoes": [f"SCAN_ERROR:{type(exc).__name__}:{str(exc)[:350]}"]})
            report.pop("_pending_signal_email", None)
            return self._finish(report, state)

    def _signal_notification(self, report: Mapping[str, Any], selected: Mapping[str, Any],
                             signal: Signal, risk: RiskPlan, now: datetime,
                             tracker: Mapping[str, Any]) -> dict[str, Any]:
        event_key = str(tracker.get("event_key", ""))
        subject = f"NIFTY V83 {signal.direction}: {selected['strike']:.0f}{selected['side']}"
        body = (f"V83 market-structure signal\nTime (IST): {now.strftime('%Y-%m-%d %H:%M:%S')}\n"
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
        subject = f"NIFTY V83 {event_type}: {tracker.get('strike')}{tracker.get('side')}"
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
                if send_email(self.config, str(item.get("subject", "NIFTY V83 notification")), str(item.get("body", ""))):
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
    parser = argparse.ArgumentParser(description="V83 NIFTY market-structure and OI-flow scanner (signal only)")
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
