#!/usr/bin/env python3
"""NIFTY 50 Predictive Market Scanner & Strike Router — V59.

Clean, modular redesign of the supplied V52–V58 scanner lineage. This version has
one market-scenario engine, one strike router, one structural risk engine, one state
store, and one reporting path; it does not place, modify, or cancel orders.

Core behavior
-------------
* Uses the NIFTY index as the price-action source and V3 minute candles for early
  intraday structure. Historical 1-minute candles seed ATR/ADX so the scanner need
  not wait for five completed 3-minute bars.
* Uses Upstox V2 option-chain/contract APIs plus V3 live quotes and candles.
* Gives valid tactical OI velocity (1m first, then 3m/5m/15m) priority over session
  aggregate bias. It never invents tactical velocity when no historical snapshot exists.
* Finds weakening/building OI walls; can report a predictive pre-breakout watch before
  spot crosses a wall. An entry still requires fresh quote, premium-VWAP, spread, delta,
  score, directional regime, wall/target geometry, and timing gates.
* Implements morning Gap & Go, Gamma Squeeze / Pre-Breakout Compression, Exhaustion
  Reversal, Continuation, and a hard Sideways/Pinning veto.
* Restricts normal option candidates to ATM, ITM1, ITM2; permits one-step OTM only for
  a confirmed high-momentum afternoon squeeze. Option quality score is exactly
  40% flow + 30% premium-VWAP lift + 30% tactical COI acceleration.
* Derives index targets/stops from intact OI walls and 1-minute price-action pivots.
  A weakening opposing wall is skipped for T1. After T1, a virtual recommendation
  tracker ratchets its stop to current structural support/resistance; this is not a
  representation of an actual user position.
* Uses an atomic JSON store with trading-date resets and no sticky directional latch.
* Uses three separate layers: predictive detection, candidate ranking, and trade readiness.
  A blocked contract is still shown as a ranked candidate with reasons; it is never labeled
  executable unless every hard gate passes.
* Treats the 0.650 score as the default configurable research threshold; changes below 0.650
  emit a warning and should only be used after historical calibration.
* T2 is optional: a valid T1 and structural stop are sufficient for readiness; missing T2 is
  reported as unavailable rather than blocking a valid structural setup.
* Outputs a structured JSON scan report on each invocation / minute loop.

Run:
    python market_scanner_v59.py
    python market_scanner_v59.py --loop

Required environment:
    UPSTOX_ANALYTICS_TOKEN

Optional environment:
    NIFTY_INSTRUMENT_KEY, STATE_FILE, REQUEST_TIMEOUT, API_RETRIES,
    MIN_SCORE (default 0.650; calibratable for research), MIN_DIRECTIONAL_DELTA (0.55),
    MIN_EXHAUSTION_DELTA (0.75), MAX_QUOTE_AGE_SECONDS, MAX_SPREAD_RATIO, RISK_FREE_RATE,
    FALLBACK_IV, EMAIL_SENDER, EMAIL_PASSWORD, EMAIL_RECEIVER, SMTP_HOST, SMTP_PORT.

API sources checked during design (official Upstox docs):
    /v2/option/contract, /v2/option/chain, /v2/market/status/:exchange,
    /v2/instruments/search, /v3/market-quote/quotes,
    /v3/historical-candle/intraday/:instrument_key/minutes/:interval,
    /v3/historical-candle/:instrument_key/minutes/:interval/:to_date/:from_date.

Important measurement limitation: the option-chain endpoint returns OI snapshots, not a
continuous OI time series. Intraday COI velocity is therefore computed from this scanner's
own timestamped snapshots. For 09:16 velocity availability, schedule the first scan at
09:15. If a process starts later with no same-session baseline, V59 reports COI as
unavailable/session-proxy and will not describe the proxy as tactical velocity.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import logging
import math
import os
import smtplib
import ssl
import sys
import tempfile
import time as time_module
import traceback
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

# =============================================================================
# Constants and configuration
# =============================================================================

IST = ZoneInfo("Asia/Kolkata")
BASE_URL = "https://api.upstox.com"
SCANNER_VERSION = "2026-10-15-V59-PRODUCTION-STATE-MIGRATION-EXACT-QUOTE-MAPPING"
MARKET_START = time(9, 15)
ENTRY_START = time(9, 16)
MORNING_END = time(10, 30)
MIDDAY_END = time(13, 30)
ENTRY_CUTOFF = time(15, 15)
MARKET_END = time(15, 30)
DEFAULT_NIFTY_KEY = "NSE_INDEX|Nifty 50"
DEFAULT_STATE_PATH = Path(__file__).resolve().parent / "state" / "market_state.json"

LOGGER = logging.getLogger("nifty_v59")
logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO").upper(),
                    format="%(asctime)s | %(levelname)s | %(message)s",
                    stream=sys.stderr)


class ScannerError(RuntimeError):
    """Expected data-quality, API, or signal-validation failure."""


@dataclass(frozen=True)
class Config:
    token: str = field(default_factory=lambda: os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip())
    nifty_key: str = field(default_factory=lambda: os.getenv("NIFTY_INSTRUMENT_KEY", DEFAULT_NIFTY_KEY).strip())
    timeout_seconds: float = field(default_factory=lambda: max(2.0, _env_float("REQUEST_TIMEOUT", 12.0)))
    retries: int = field(default_factory=lambda: max(1, min(5, _env_int("API_RETRIES", 3))))
    max_quote_age_seconds: float = field(default_factory=lambda: min(30.0, max(5.0, _env_float("MAX_QUOTE_AGE_SECONDS", 30.0))))
    max_spread_ratio: float = field(default_factory=lambda: min(0.001, max(0.0001, _env_float("MAX_SPREAD_RATIO", 0.001))))
    min_score: float = field(default_factory=lambda: min(1.0, max(0.0, _env_float("MIN_SCORE", 0.650))))
    min_directional_delta: float = field(default_factory=lambda: min(1.0, max(0.0, _env_float("MIN_DIRECTIONAL_DELTA", 0.55))))
    min_exhaustion_delta: float = field(default_factory=lambda: min(1.0, max(0.0, _env_float("MIN_EXHAUSTION_DELTA", 0.75))))
    strike_stickiness_tolerance: float = field(default_factory=lambda: min(0.20, max(0.0, _env_float("STRIKE_STICKINESS_SCORE_TOLERANCE", 0.05))))
    atr_period: int = field(default_factory=lambda: max(3, _env_int("ATR_PERIOD", 14)))
    adx_period: int = field(default_factory=lambda: max(3, _env_int("ADX_PERIOD", 14)))
    rsi_period: int = field(default_factory=lambda: max(3, _env_int("RSI_PERIOD", 14)))
    oi_velocity_trigger: float = field(default_factory=lambda: max(0.0002, _env_float("OI_VELOCITY_TRIGGER", 0.0015)))
    compression_atr_multiple: float = field(default_factory=lambda: max(0.25, _env_float("COMPRESSION_ATR_MULTIPLE", 1.25)))
    wall_proximity_atr: float = field(default_factory=lambda: max(0.10, _env_float("WALL_PROXIMITY_ATR", 0.55)))
    gap_threshold_pct: float = field(default_factory=lambda: max(0.001, _env_float("GAP_THRESHOLD_PCT", 0.0025)))
    pcr_spike_pct: float = field(default_factory=lambda: max(0.005, _env_float("PCR_SPIKE_PCT", 0.03)))
    risk_free_rate: float = field(default_factory=lambda: _env_float("RISK_FREE_RATE", 0.065))
    fallback_iv: float = field(default_factory=lambda: min(2.0, max(0.05, _env_float("FALLBACK_IV", 0.18))))
    state_file: Path = field(default_factory=lambda: _resolve_state_path(os.getenv("STATE_FILE", "")))
    email_sender: str = field(default_factory=lambda: os.getenv("EMAIL_SENDER", "").strip())
    email_password: str = field(default_factory=lambda: os.getenv("EMAIL_PASSWORD", "").strip())
    email_receiver: str = field(default_factory=lambda: os.getenv("EMAIL_RECEIVER", "").strip())
    smtp_host: str = field(default_factory=lambda: os.getenv("SMTP_HOST", "smtp.gmail.com").strip())
    smtp_port: int = field(default_factory=lambda: max(1, _env_int("SMTP_PORT", 465)))
    email_watch_alerts: bool = field(default_factory=lambda: _env_bool("EMAIL_WATCH_ALERTS", True))
    watch_alert_min_confidence: float = field(default_factory=lambda: min(100.0, max(0.0, _env_float("WATCH_ALERT_MIN_CONFIDENCE", 55.0))))
    watch_alert_cooldown_minutes: int = field(default_factory=lambda: min(120, max(1, _env_int("WATCH_ALERT_COOLDOWN_MINUTES", 10))))
    monitor_quote_alert_cooldown_minutes: int = field(default_factory=lambda: min(120, max(1, _env_int("MONITOR_QUOTE_ALERT_COOLDOWN_MINUTES", 10))))
    max_active_trackers: int = field(default_factory=lambda: min(12, max(1, _env_int("MAX_ACTIVE_RECOMMENDATION_TRACKERS", 5))))
    reentry_cooldown_minutes: int = field(default_factory=lambda: min(60, max(1, _env_int("REENTRY_COOLDOWN_MINUTES", 6))))

    def validate(self, require_token: bool = True) -> None:
        if require_token and not self.token:
            raise ScannerError("UPSTOX_ANALYTICS_TOKEN is missing. Set it in the environment.")
        if not self.nifty_key:
            raise ScannerError("NIFTY_INSTRUMENT_KEY cannot be empty.")
        if not (0.0 <= self.min_score <= 1.0):
            raise ScannerError("MIN_SCORE must be between 0.0 and 1.0.")
        if self.min_score < 0.650:
            LOGGER.warning("MIN_SCORE=%.3f is below the default 0.650; use only after historical calibration.", self.min_score)
        if not (0.0 <= self.min_directional_delta <= 1.0 and 0.0 <= self.min_exhaustion_delta <= 1.0):
            raise ScannerError("Configured delta thresholds must be between 0.0 and 1.0.")
        if self.min_directional_delta < 0.55 or self.min_exhaustion_delta < 0.75:
            LOGGER.warning("Delta floor is below the requested default; use only for historical calibration and risk analysis.")
        if not (0.0 <= self.strike_stickiness_tolerance <= 0.20):
            raise ScannerError("STRIKE_STICKINESS_SCORE_TOLERANCE must be between 0 and 0.20.")


def _env_float(key: str, default: float) -> float:
    try:
        value = float(os.getenv(key, str(default)))
        return value if math.isfinite(value) else default
    except (ValueError, TypeError):
        return default


def _env_int(key: str, default: int) -> int:
    try:
        return int(os.getenv(key, str(default)))
    except (ValueError, TypeError):
        return default


def _env_bool(key: str, default: bool) -> bool:
    raw = os.getenv(key)
    if raw is None:
        return default
    return raw.strip().lower() in {"1", "true", "yes", "on", "enabled"}


def _resolve_state_path(raw: str) -> Path:
    if not str(raw or "").strip():
        return DEFAULT_STATE_PATH
    path = Path(raw).expanduser()
    return path if path.is_absolute() else (Path.cwd() / path).resolve()


def now_ist() -> datetime:
    return datetime.now(IST)


def safe_float(value: Any, default: float = float("nan")) -> float:
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


def clamp(value: float, low: float = 0.0, high: float = 1.0) -> float:
    if not finite(value):
        return low
    return max(low, min(high, float(value)))


def parse_date(value: Any) -> Optional[date]:
    try:
        return datetime.strptime(str(value)[:10], "%Y-%m-%d").date()
    except (ValueError, TypeError):
        return None


def parse_timestamp(value: Any) -> Optional[datetime]:
    """Parse Upstox ISO timestamps or epoch values into timezone-aware IST."""
    if value is None or str(value).strip() == "":
        return None
    try:
        numeric = safe_float(value, float("nan"))
        if math.isfinite(numeric) and numeric > 1_000_000_000:
            if numeric >= 100_000_000_000_000_000:
                unit = "ns"
            elif numeric >= 100_000_000_000_000:
                unit = "us"
            elif numeric >= 100_000_000_000:
                unit = "ms"
            else:
                unit = "s"
            parsed = pd.to_datetime(numeric, unit=unit, utc=True, errors="coerce")
            if pd.isna(parsed):
                return None
            return parsed.to_pydatetime().astimezone(IST)
        parsed = pd.Timestamp(value)
        if pd.isna(parsed):
            return None
        if parsed.tzinfo is None:
            parsed = parsed.tz_localize(IST)
        else:
            parsed = parsed.tz_convert(IST)
        return parsed.to_pydatetime()
    except (ValueError, TypeError, OverflowError):
        return None


def json_safe(value: Any) -> Any:
    """Recursively convert pandas/numpy/datetime/non-finite values to JSON-safe values."""
    if value is None or isinstance(value, (str, bool, int)):
        return value
    if isinstance(value, float):
        return value if math.isfinite(value) else None
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        f = float(value)
        return f if math.isfinite(f) else None
    if isinstance(value, (np.bool_,)):
        return bool(value)
    if isinstance(value, (datetime, date, pd.Timestamp)):
        return value.isoformat()
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, pd.Series):
        return [json_safe(x) for x in value.tolist()]
    if isinstance(value, pd.DataFrame):
        return [json_safe(x) for x in value.to_dict(orient="records")]
    if hasattr(value, "item") and callable(value.item):
        try:
            return json_safe(value.item())
        except Exception:
            pass
    if isinstance(value, Mapping):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [json_safe(x) for x in value]
    if hasattr(value, "__dataclass_fields__"):
        return json_safe(asdict(value))
    return str(value)


def ist_iso(dt: datetime) -> str:
    aware = dt if dt.tzinfo else dt.replace(tzinfo=IST)
    return aware.astimezone(IST).isoformat()


def market_time_allowed(dt: datetime) -> tuple[bool, str]:
    """Gate scanning by session, while allowing 09:15 baseline and post-cutoff monitoring.

    09:15 must be processed to create the first option-OI snapshot for the 09:16
    tactical window. After 15:15, the scanner continues observing/maintaining virtual
    risk state, but a separate execution veto blocks all new directional recommendations.
    """
    local = dt.astimezone(IST) if dt.tzinfo else dt.replace(tzinfo=IST)
    if local.weekday() >= 5:
        return False, "WEEKEND"
    if local.time() < MARKET_START:
        return False, "BEFORE_NSE_MARKET_OPEN"
    if local.time() >= MARKET_END:
        return False, "OUTSIDE_NSE_MARKET_HOURS"
    if local.time() < ENTRY_START:
        return True, "BASELINE_WARMUP_09_15_NO_ENTRY"
    if local.time() >= ENTRY_CUTOFF:
        return True, "POST_15_15_MONITOR_ONLY_NO_NEW_ENTRIES"
    return True, "ENTRY_WINDOW_OPEN"


# =============================================================================
# Typed data structures
# =============================================================================

@dataclass(frozen=True)
class LiveQuote:
    instrument_key: str
    symbol: str
    ltp: float
    bid: float
    ask: float
    bid_qty: float
    ask_qty: float
    volume: float
    oi: float
    previous_oi: float
    previous_close: float
    timestamp: Optional[str]
    last_trade_time: Optional[str]
    freshness: str
    age_seconds: Optional[float]
    last_trade_age_seconds: Optional[float]
    raw: dict[str, Any] = field(default_factory=dict, repr=False)

    @property
    def mid(self) -> float:
        if finite(self.bid) and finite(self.ask) and self.bid > 0 and self.ask >= self.bid:
            return (self.bid + self.ask) / 2.0
        return float("nan")

    @property
    def spread_ratio(self) -> float:
        mid = self.mid
        if not finite(mid) or mid <= 0:
            return float("inf")
        return (self.ask - self.bid) / mid

    @property
    def depth_imbalance(self) -> float:
        denom = max(0.0, self.bid_qty) + max(0.0, self.ask_qty)
        if denom <= 0:
            return 0.0
        return clamp((self.bid_qty - self.ask_qty) / denom, -1.0, 1.0)


@dataclass(frozen=True)
class OptionContract:
    instrument_key: str
    trading_symbol: str
    option_type: str
    strike: float
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
    theta: float
    iv: float
    delta_source: str
    spread_ratio: float
    premium_vwap: float
    flow_score: float
    vwap_lift_score: float
    coi_score: float
    total_score: float
    call_coi_pct: float
    put_coi_pct: float
    tactical_source: str
    quote_freshness: str
    quote_age_seconds: Optional[float]
    premium_return_pct: float
    volume_ratio: float
    pin_disqualified: bool
    vetoes: tuple[str, ...] = ()
    score_basis: str = "FULL_40_30_30"
    score_components_available: tuple[str, ...] = ()


@dataclass(frozen=True)
class StructuralWall:
    strike: float
    side: str  # CALL resistance / PUT support
    oi: float
    change_pct: Optional[float]
    state: str  # BUILDING / WEAKENING / STABLE / UNKNOWN
    source: str
    distance: float


@dataclass(frozen=True)
class IndicatorSet:
    spot: float
    vwap: float
    vwap_slope: float
    stddev: float
    upper_1sd: float
    lower_1sd: float
    upper_2sd: float
    lower_2sd: float
    atr: float
    adx: float
    plus_di: float
    minus_di: float
    rsi: float
    momentum_3m_pct: float
    recent_range: float
    prior_range: float
    compressed: bool
    swing_low: float
    swing_high: float
    previous_close: float
    session_open: float
    candles_count: int
    indicators_seeded: bool
    volume_source: str


@dataclass
class OIAnalysis:
    rows: dict[float, dict[str, Any]]
    call_total: float
    put_total: float
    pcr: float
    pcr_previous: Optional[float]
    pcr_spiking: bool
    call_coi_pct: float
    put_coi_pct: float
    session_call_coi_pct: float
    session_put_coi_pct: float
    tactical_source: str
    tactical_available: bool
    tactical_age_minutes: Optional[float]
    pin_market_veto: bool
    pin_strikes: list[float]
    both_sides_building: bool
    call_unwind_dominates: bool
    put_unwind_dominates: bool
    walls_resistance: list[StructuralWall]
    walls_support: list[StructuralWall]
    baseline_quality: str
    reasons: list[str]
    session_baseline_source: str = "UNAVAILABLE"
    call_coi_acceleration_pct: float = float("nan")
    put_coi_acceleration_pct: float = float("nan")
    acceleration_available: bool = False


@dataclass(frozen=True)
class Scenario:
    state: str
    direction: str
    confidence: float
    trigger_reason: str
    wall_level: Optional[float]
    wall_state: str
    executable_candidate: bool
    hard_veto: Optional[str]
    features: dict[str, Any]


@dataclass(frozen=True)
class RiskPlan:
    valid: bool
    target_1: Optional[float]
    target_2: Optional[float]
    stop_loss: Optional[float]
    stop_source: str
    target_1_source: str
    target_2_source: str
    skipped_weak_walls: tuple[float, ...]
    reason: str


def _infer_state_session_date(state: Mapping[str, Any]) -> str:
    """Infer the stored session date across V52–V58 state formats without guessing."""
    for key in ("session_date", "state_session_date"):
        parsed = parse_date(state.get(key))
        if parsed:
            return parsed.isoformat()
    timestamp_fields = ("last_scan_timestamp", "last_signal_timestamp")
    for key in timestamp_fields:
        stamp = parse_timestamp(state.get(key))
        if stamp:
            return stamp.astimezone(IST).date().isoformat()
    for key in ("market_snapshot", "option_oi_snapshot", "session_oi_baseline"):
        raw = state.get(key)
        stamp = parse_timestamp(raw.get("timestamp")) if isinstance(raw, dict) else None
        if stamp:
            return stamp.astimezone(IST).date().isoformat()
    candidates: list[datetime] = []
    for key in ("chain_snapshots", "option_oi_history", "option_oi_history_snapshots", "market_history"):
        rows = state.get(key)
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            stamp = parse_timestamp(row.get("timestamp"))
            if stamp:
                candidates.append(stamp.astimezone(IST))
    return max(candidates).date().isoformat() if candidates else ""


def _normalize_legacy_chain_snapshot(raw: Any) -> Optional[dict[str, Any]]:
    """Normalize supported historical OI snapshot layouts to the V59 chain schema."""
    if not isinstance(raw, dict):
        return None
    stamp = parse_timestamp(raw.get("timestamp"))
    if stamp is None:
        return None
    by_strike: dict[float, dict[str, Any]] = {}

    def add(strike_value: Any, side: str, oi_value: Any) -> None:
        strike = safe_float(strike_value)
        oi = safe_float(oi_value)
        side_norm = str(side).strip().upper()
        if not finite(strike) or strike <= 0 or not finite(oi) or oi < 0 or side_norm not in {"CE", "PE", "CALL", "PUT"}:
            return
        row = by_strike.setdefault(strike, {"strike": strike, "call_oi": 0.0, "put_oi": 0.0})
        row["call_oi" if side_norm in {"CE", "CALL"} else "put_oi"] = oi

    rows = raw.get("rows")
    if isinstance(rows, list):
        for item in rows:
            if not isinstance(item, dict):
                continue
            strike = item.get("strike")
            if finite(strike):
                by_strike[float(strike)] = {
                    "strike": float(strike),
                    "call_oi": max(0.0, safe_float(item.get("call_oi"), 0.0)),
                    "put_oi": max(0.0, safe_float(item.get("put_oi"), 0.0)),
                }

    # V52 stored OI by logical contract/instrument and in a strikes map.
    for map_key in ("oi_by_contract", "oi_by_instrument"):
        mapping = raw.get(map_key)
        if not isinstance(mapping, dict):
            continue
        for key, item in mapping.items():
            if not isinstance(item, dict):
                continue
            side = item.get("side", "")
            key_upper = str(key).upper()
            if not side:
                if key_upper.endswith("|CE") or key_upper.endswith(":CE"):
                    side = "CE"
                elif key_upper.endswith("|PE") or key_upper.endswith(":PE"):
                    side = "PE"
            add(item.get("strike"), str(side), item.get("oi"))

    legacy_strikes = raw.get("strikes")
    if isinstance(legacy_strikes, dict):
        for strike, item in legacy_strikes.items():
            if not isinstance(item, dict):
                continue
            add(strike, "CE", item.get("call_oi"))
            add(strike, "PE", item.get("put_oi"))

    if not by_strike:
        return None
    normalized_rows = [by_strike[k] for k in sorted(by_strike)]
    call_total = sum(safe_float(row.get("call_oi"), 0.0) for row in normalized_rows)
    put_total = sum(safe_float(row.get("put_oi"), 0.0) for row in normalized_rows)
    pcr = safe_float(raw.get("pcr"), put_total / call_total if call_total > 0 else float("nan"))
    return {
        "timestamp": ist_iso(stamp),
        "expiry": str(raw.get("expiry", ""))[:10],
        "pcr": pcr,
        "rows": normalized_rows,
    }


def _migrate_intraday_state(state: dict[str, Any], today: date) -> None:
    """Consolidate legacy same-session OI snapshots and tracker fields in-place."""
    today_iso = today.isoformat()
    active_expiry = str(state.get("option_expiry", ""))[:10]
    collected: dict[str, dict[str, Any]] = {}
    for key in ("chain_snapshots", "option_oi_history", "option_oi_history_snapshots", "option_oi_snapshot"):
        raw_rows = state.get(key)
        if not isinstance(raw_rows, list):
            continue
        for raw in raw_rows:
            item = _normalize_legacy_chain_snapshot(raw)
            if item is None or str(item.get("timestamp", ""))[:10] != today_iso:
                continue
            expiry = str(item.get("expiry", ""))[:10]
            if active_expiry and expiry != active_expiry:
                continue
            # Multiple legacy stores sometimes contain the same minute; prefer the
            # canonical V59 snapshot when it was present first, but keep valid rows.
            minute_key = str(item["timestamp"])[:16]
            collected.setdefault(minute_key, item)
    snapshots = sorted(collected.values(), key=lambda item: str(item.get("timestamp", "")))
    state["chain_snapshots"] = snapshots[-120:]

    baseline = _normalize_legacy_chain_snapshot(state.get("session_oi_baseline"))
    if baseline is not None and str(baseline.get("timestamp", ""))[:10] == today_iso:
        if not active_expiry or str(baseline.get("expiry", ""))[:10] == active_expiry:
            state["session_oi_baseline"] = baseline
        else:
            baseline = None
            state["session_oi_baseline"] = None
    else:
        state["session_oi_baseline"] = None
        baseline = None
    if state.get("session_oi_baseline") is None and snapshots:
        earliest = snapshots[0]
        earliest_ts = parse_timestamp(earliest.get("timestamp"))
        state["session_oi_baseline"] = earliest
        state["session_oi_baseline_source"] = (
            "MIGRATED_09_15_BASELINE" if earliest_ts and earliest_ts.astimezone(IST).time() == time(9, 15)
            else "MIGRATED_FIRST_AVAILABLE_SNAPSHOT_NOT_CONFIRMED_OPEN"
        )
    if state.get("session_oi_baseline") is not None and str(state.get("session_oi_baseline_source", "UNAVAILABLE")).upper() in {"", "UNAVAILABLE", "NONE"}:
        state["session_oi_baseline_source"] = "MIGRATED_EXISTING_SAME_SESSION_BASELINE"
    else:
        state.setdefault("session_oi_baseline_source", "UNAVAILABLE")
    state["schema_version"] = 59
    state["scanner_version"] = SCANNER_VERSION
    state["session_date"] = today_iso
    # Remove legacy directional latches so V59 always classifies live structure afresh.
    for key in ("persistent_direction", "continuation_phase", "continuation_count", "continuation_last_bar"):
        state.pop(key, None)


@dataclass
class StateStore:
    path: Path
    state: dict[str, Any] = field(default_factory=dict)

    def load(self, today: date) -> dict[str, Any]:
        """Load/upgrade scanner state, preserving alert outbox across session resets.

        On corrupt JSON the unreadable file is copied to a timestamped diagnostic backup;
        the scanner fails closed for signals if required baselines cannot be recovered.
        """
        try:
            if self.path.exists():
                with self.path.open("r", encoding="utf-8") as handle:
                    data = json.load(handle)
                self.state = data if isinstance(data, dict) else {}
        except (OSError, json.JSONDecodeError, TypeError, ValueError) as exc:
            LOGGER.error("STATE LOAD FAILURE; preserving corrupt file and starting safely: %s", exc)
            try:
                if self.path.exists():
                    backup = self.path.with_name(f"{self.path.name}.corrupt-{now_ist().strftime('%Y%m%dT%H%M%S')}")
                    backup.write_bytes(self.path.read_bytes())
                    LOGGER.error("CORRUPT STATE BACKUP: %s", backup)
            except OSError as backup_exc:
                LOGGER.error("Unable to back up corrupt state file: %s", backup_exc)
            self.state = {}

        stored_date = _infer_state_session_date(self.state)
        today_iso = today.isoformat()
        if stored_date != today_iso:
            if stored_date:
                LOGGER.info("SESSION RESET: state_date=%s current_date=%s; clearing intraday OI/direction state.", stored_date, today_iso)
            # Unsent notifications must survive a date boundary; market/virtual trackers must not.
            old_outbox = [dict(x) for x in self.state.get("alert_outbox", [])
                          if isinstance(x, dict) and str(x.get("status", "PENDING")).upper() == "PENDING"] if isinstance(self.state.get("alert_outbox"), list) else []
            old_dedupe = self.state.get("alert_dedupe", {}) if isinstance(self.state.get("alert_dedupe"), dict) else {}
            self.state = {
                "schema_version": 59,
                "scanner_version": SCANNER_VERSION,
                "session_date": today_iso,
                "chain_snapshots": [],
                "session_oi_baseline": None,
                "session_oi_baseline_source": "UNAVAILABLE",
                "futures_snapshots": [],
                "market_history": [],
                "historical_seed": {},
                "option_expiry": "",
                "nifty_future": {},
                "recommendation_tracker": None,
                "recommendation_trackers": [],
                "last_email_fingerprint": "",
                "last_signal_fingerprint": "",
                "last_signal_timestamp": "",
                "alert_outbox": old_outbox[-200:],
                "alert_dedupe": old_dedupe,
            }
        else:
            # Preserve current-session history across version upgrades; normalize older
            # snapshot formats rather than throwing away valid tactical COI baselines.
            _migrate_intraday_state(self.state, today)
            self.state.setdefault("futures_snapshots", [])
            self.state.setdefault("market_history", [])
            self.state.setdefault("historical_seed", {})
            self.state.setdefault("recommendation_tracker", None)
            self.state.setdefault("recommendation_trackers", [])
            self.state.setdefault("alert_outbox", [])
            self.state.setdefault("alert_dedupe", {})

        # Migrate the pre-V59 singular tracker into the canonical tracker list.
        trackers_raw = self.state.get("recommendation_trackers")
        trackers = [dict(item) for item in trackers_raw if isinstance(item, dict)] if isinstance(trackers_raw, list) else []
        primary = self.state.get("recommendation_tracker")
        if not trackers and isinstance(primary, dict):
            trackers = [dict(primary)]
        elif isinstance(primary, dict):
            primary_fp = str(primary.get("signal_fingerprint", ""))
            if primary_fp:
                found = next((item for item in trackers if str(item.get("signal_fingerprint", "")) == primary_fp), None)
                if found is not None:
                    # Keep the singular legacy view canonical for backward compatibility.
                    found.update(primary)
                    primary = found
                else:
                    trackers.append(dict(primary))
                    primary = trackers[-1]
        trackers = trackers[-60:]
        self.state["recommendation_trackers"] = trackers
        if trackers:
            latest = next((item for item in reversed(trackers)
                           if str(item.get("signal_fingerprint", "")) == str(self.state.get("last_signal_fingerprint", ""))), trackers[-1])
            self.state["recommendation_tracker"] = latest
        else:
            self.state["recommendation_tracker"] = None

        if not isinstance(self.state.get("alert_outbox"), list):
            self.state["alert_outbox"] = []
        if not isinstance(self.state.get("alert_dedupe"), dict):
            self.state["alert_dedupe"] = {}
        # Remove obsolete direction latches. Every decision is recomputed from current structure.
        self.state.pop("persistent_direction", None)
        self.state.pop("continuation_phase", None)
        return self.state

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        payload = json.dumps(json_safe(self.state), indent=2, ensure_ascii=False, allow_nan=False)
        fd, temp_path = tempfile.mkstemp(prefix=self.path.name + ".", suffix=".tmp", dir=str(self.path.parent))
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                handle.write(payload)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp_path, self.path)
        except Exception:
            try:
                os.unlink(temp_path)
            except OSError:
                pass
            raise

    def recent_chain_snapshots(self, now: datetime, keep_minutes: int = 20) -> list[dict[str, Any]]:
        raw = self.state.get("chain_snapshots", [])
        if not isinstance(raw, list):
            raw = []
        cutoff = now - timedelta(minutes=keep_minutes)
        valid: list[dict[str, Any]] = []
        for row in raw:
            if not isinstance(row, dict):
                continue
            ts = parse_timestamp(row.get("timestamp"))
            if ts and ts.date() == now.date() and cutoff <= ts <= now + timedelta(seconds=5):
                valid.append(row)
        valid.sort(key=lambda r: str(r.get("timestamp", "")))
        self.state["chain_snapshots"] = valid[-32:]
        return valid

    def append_chain_snapshot(self, snapshot: dict[str, Any], now: datetime) -> None:
        samples = self.recent_chain_snapshots(now)
        key = str(snapshot.get("timestamp", ""))[:16]
        samples = [x for x in samples if str(x.get("timestamp", ""))[:16] != key]
        samples.append(snapshot)
        samples.sort(key=lambda r: str(r.get("timestamp", "")))
        cutoff = now - timedelta(minutes=20)
        samples = [x for x in samples if (parse_timestamp(x.get("timestamp")) or datetime.min.replace(tzinfo=IST)) >= cutoff]
        self.state["chain_snapshots"] = samples[-32:]


# =============================================================================
# Upstox API and normalization
# =============================================================================

def _is_exact_nifty_future_row(row: Mapping[str, Any]) -> bool:
    """Reject BANKNIFTY/FINNIFTY/MIDCPNIFTY when search query is simply NIFTY."""
    instrument_type = str(row.get("instrument_type", "")).strip().upper()
    if instrument_type != "FUT":
        return False
    underlying = str(row.get("underlying_symbol", "")).strip().upper()
    symbol_tokens = str(row.get("trading_symbol", "")).strip().upper().split()
    if underlying:
        return underlying in {"NIFTY", "NIFTY 50"}
    return len(symbol_tokens) >= 2 and symbol_tokens[0] == "NIFTY" and symbol_tokens[1] == "FUT"


def _is_exact_nifty_future_symbol(symbol: str) -> bool:
    """Validate a cached NIFTY future using its canonical trading-symbol prefix."""
    tokens = str(symbol or "").strip().upper().split()
    return len(tokens) >= 2 and tokens[0] == "NIFTY" and tokens[1] == "FUT"


class UpstoxClient:
    def __init__(self, config: Config, session: Optional[requests.Session] = None) -> None:
        self.config = config
        self.session = session or requests.Session()
        self.session.headers.update({"Accept": "application/json", "Content-Type": "application/json"})

    def get(self, path: str, params: Optional[dict[str, Any]] = None) -> dict[str, Any]:
        self.config.validate(require_token=True)
        url = path if path.startswith("http") else BASE_URL + path
        last_error = "Unknown API error"
        for attempt in range(1, self.config.retries + 1):
            try:
                response = self.session.get(
                    url, params=params,
                    headers={"Authorization": f"Bearer {self.config.token}", "Accept": "application/json"},
                    timeout=(min(5.0, self.config.timeout_seconds), self.config.timeout_seconds),
                )
            except requests.RequestException as exc:
                last_error = f"network/timeout error: {exc}"
                if attempt < self.config.retries:
                    time_module.sleep(min(0.5 * (2 ** (attempt - 1)), 3.0))
                    continue
                raise ScannerError(f"Upstox request failed for {url}: {last_error}") from exc
            if response.status_code == 200:
                try:
                    payload = response.json()
                except ValueError as exc:
                    raise ScannerError(f"Upstox returned invalid JSON for {url}") from exc
                if not isinstance(payload, dict):
                    raise ScannerError(f"Unexpected Upstox response shape for {url}")
                if str(payload.get("status", "success")).lower() == "error":
                    raise ScannerError(f"Upstox API error at {url}: {json.dumps(payload)[:1000]}")
                return payload
            last_error = f"HTTP {response.status_code}: {str(response.text)[:1000]}"
            retryable = response.status_code in {429, 500, 502, 503, 504}
            if retryable and attempt < self.config.retries:
                retry_after = safe_float(response.headers.get("Retry-After"), float("nan"))
                delay = retry_after if math.isfinite(retry_after) else min(0.75 * (2 ** (attempt - 1)), 4.0)
                time_module.sleep(max(0.1, min(delay, 8.0)))
                continue
            raise ScannerError(f"Upstox request failed for {url}: {last_error}")
        raise ScannerError(f"Upstox request failed for {url}: {last_error}")

    def market_status(self) -> str:
        payload = self.get("/v2/market/status/NSE")
        data = payload.get("data", {})
        value = str(data.get("status", "UNKNOWN")).upper() if isinstance(data, dict) else "UNKNOWN"
        return "OPEN" if value in {"NORMAL_OPEN", "OPEN"} else "CLOSED" if value in {"NORMAL_CLOSE", "CLOSED"} else value

    def quotes(self, keys: Sequence[str]) -> dict[str, LiveQuote]:
        unique = list(dict.fromkeys(k for k in keys if str(k).strip()))
        if not unique:
            return {}
        if len(unique) > 500:
            raise ScannerError("Upstox V3 Full Market Quotes accepts at most 500 instrument keys per request.")
        payload = self.get("/v3/market-quote/quotes", {"instrument_key": ",".join(unique)})
        raw = payload.get("data", {})
        if not isinstance(raw, dict):
            raise ScannerError("Upstox full-market-quote data is not an object.")
        result: dict[str, LiveQuote] = {}
        for key in unique:
            row = _lookup_quote(raw, key)
            if not isinstance(row, dict):
                continue
            result[key] = _normalise_quote(key, row, self.config.max_quote_age_seconds)
        return result

    def candles(self, instrument_key: str, interval: int = 1, historical: bool = False,
                from_date: Optional[date] = None, to_date: Optional[date] = None) -> pd.DataFrame:
        encoded = urllib.parse.quote(instrument_key, safe="")
        if historical:
            if from_date is None or to_date is None:
                raise ValueError("from_date and to_date are required for historical candles")
            path = f"/v3/historical-candle/{encoded}/minutes/{int(interval)}/{to_date.isoformat()}/{from_date.isoformat()}"
        else:
            path = f"/v3/historical-candle/intraday/{encoded}/minutes/{int(interval)}"
        payload = self.get(path)
        data = payload.get("data", {})
        candle_rows = data.get("candles", []) if isinstance(data, dict) else []
        frame = parse_candles(candle_rows)
        if frame.empty:
            return frame
        current = now_ist()
        local_time = frame["timestamp"].dt.tz_convert(IST)
        if not historical:
            frame = frame.loc[local_time.dt.date == current.date()].copy()
        else:
            frame = frame.loc[local_time.dt.date <= (to_date or current.date())].copy()
        return (frame.sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True))

    def option_expiry(self, state: dict[str, Any], today: date) -> str:
        cached = parse_date(state.get("option_expiry", ""))
        if cached and cached >= today:
            return cached.isoformat()
        payload = self.get("/v2/option/contract", {"instrument_key": self.config.nifty_key})
        rows = payload.get("data", [])
        if not isinstance(rows, list):
            raise ScannerError("Option-contract endpoint returned an invalid data array.")
        expiries = sorted({d for row in rows if isinstance(row, dict)
                           and (d := parse_date(row.get("expiry"))) is not None and d >= today})
        if not expiries:
            raise ScannerError("No active NIFTY option expiry found.")
        state["option_expiry"] = expiries[0].isoformat()
        return expiries[0].isoformat()

    def option_chain(self, expiry: str) -> list[dict[str, Any]]:
        payload = self.get("/v2/option/chain", {"instrument_key": self.config.nifty_key, "expiry_date": expiry})
        rows = payload.get("data", [])
        if not isinstance(rows, list) or not rows:
            raise ScannerError(f"NIFTY option chain is empty for expiry {expiry}.")
        filtered = [r for r in rows if isinstance(r, dict) and str(r.get("expiry", expiry))[:10] == expiry[:10]]
        return filtered or [r for r in rows if isinstance(r, dict)]

    def nearest_future(self, state: dict[str, Any], today: date) -> Optional[dict[str, str]]:
        cached = state.get("nifty_future")
        if isinstance(cached, dict):
            expiry = parse_date(cached.get("expiry"))
            key = str(cached.get("instrument_key", ""))
            symbol = str(cached.get("trading_symbol", ""))
            if key and symbol and expiry and expiry >= today and _is_exact_nifty_future_symbol(symbol):
                return {"instrument_key": key, "trading_symbol": symbol, "expiry": expiry.isoformat()}
        rows: list[dict[str, Any]] = []
        for expiry_filter in ("current_month", "next_month"):
            payload = self.get("/v2/instruments/search", {
                "query": "NIFTY", "exchanges": "NSE", "segments": "FO",
                "instrument_types": "FUT", "expiry": expiry_filter,
                "page_number": 1, "records": 30,
            })
            data = payload.get("data", [])
            if isinstance(data, list):
                rows.extend(x for x in data if isinstance(x, dict))
        valid = []
        for row in rows:
            expiry = parse_date(row.get("expiry"))
            key = str(row.get("instrument_key", "")).strip()
            symbol = str(row.get("trading_symbol", "")).strip()
            if key and symbol and expiry and expiry >= today and _is_exact_nifty_future_row(row):
                valid.append((expiry, row))
        if not valid:
            LOGGER.warning("NIFTY futures instrument not found; continuing without futures confirmation.")
            return None
        valid.sort(key=lambda pair: pair[0])
        expiry, selected = valid[0]
        future = {"instrument_key": str(selected["instrument_key"]),
                  "trading_symbol": str(selected["trading_symbol"]), "expiry": expiry.isoformat()}
        state["nifty_future"] = future
        return future


def _lookup_quote(raw: Mapping[str, Any], key: str) -> Optional[dict[str, Any]]:
    for candidate in (key, key.replace("|", ":", 1)):
        value = raw.get(candidate)
        if isinstance(value, dict):
            return value
    for value in raw.values():
        if isinstance(value, dict) and str(value.get("instrument_token", "")).replace(":", "|") == key:
            return value
    # Never map a lone response row to an unrelated requested key. In a batched
    # quote request, Upstox may omit instruments with no current quote; a singleton
    # fallback would silently copy one option's LTP/depth into other contracts.
    return None


def _normalise_quote(key: str, raw: dict[str, Any], max_age: float) -> LiveQuote:
    depth = raw.get("depth") if isinstance(raw.get("depth"), dict) else {}
    ohlc = raw.get("ohlc") if isinstance(raw.get("ohlc"), dict) else {}
    buys = depth.get("buy", []) if isinstance(depth.get("buy", []), list) else []
    sells = depth.get("sell", []) if isinstance(depth.get("sell", []), list) else []
    first_buy = buys[0] if buys and isinstance(buys[0], dict) else {}
    first_sell = sells[0] if sells and isinstance(sells[0], dict) else {}
    bid = safe_float(first_buy.get("price"), float("nan"))
    ask = safe_float(first_sell.get("price"), float("nan"))
    # Exchange quote timestamp denotes snapshot generation; last_trade_time is kept
    # separately because a quiet contract may have old last trade but fresh depth.
    ts_raw = raw.get("timestamp")
    trade_raw = raw.get("last_trade_time")
    now = now_ist()
    ts = parse_timestamp(ts_raw)
    trade_ts = parse_timestamp(trade_raw)
    if ts:
        age = (now - ts).total_seconds()
        freshness = "FRESH" if -5.0 <= age <= max_age else "STALE" if age > max_age else "FUTURE_TIMESTAMP"
    elif trade_ts:
        age = (now - trade_ts).total_seconds()
        freshness = "FRESH" if -5.0 <= age <= max_age else "STALE" if age > max_age else "FUTURE_TIMESTAMP"
    else:
        age, freshness = None, "UNVERIFIED"
    trade_age = (now - trade_ts).total_seconds() if trade_ts else None
    # `dict.get(key, default)` does not use the default when the key exists but is
    # explicitly null. Fall back to the documented V3 OHLC volume in that case.
    quote_volume = safe_float(raw.get("volume"), float("nan"))
    if not finite(quote_volume):
        quote_volume = safe_float(ohlc.get("volume"), 0.0)
    return LiveQuote(
        instrument_key=key,
        symbol=str(raw.get("symbol", raw.get("trading_symbol", key))),
        ltp=safe_float(raw.get("last_price", raw.get("ltp"))),
        bid=bid, ask=ask,
        bid_qty=sum(max(0.0, safe_float(x.get("quantity"), 0.0)) for x in buys if isinstance(x, dict)),
        ask_qty=sum(max(0.0, safe_float(x.get("quantity"), 0.0)) for x in sells if isinstance(x, dict)),
        volume=max(0.0, quote_volume),
        oi=max(0.0, safe_float(raw.get("oi"), 0.0)),
        previous_oi=safe_float(raw.get("previous_oi", raw.get("prev_oi")), float("nan")),
        previous_close=safe_float(raw.get("prev_close_price"), safe_float(ohlc.get("close"), float("nan"))),
        timestamp=ts.isoformat() if ts else (str(ts_raw) if ts_raw else None),
        last_trade_time=trade_ts.isoformat() if trade_ts else (str(trade_raw) if trade_raw else None),
        freshness=freshness, age_seconds=age, last_trade_age_seconds=trade_age, raw=raw,
    )


def parse_candles(rows: Any) -> pd.DataFrame:
    """Normalize Upstox [timestamp, open, high, low, close, volume, oi?] rows."""
    parsed: list[dict[str, Any]] = []
    if not isinstance(rows, list):
        return pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
    for row in rows:
        if not isinstance(row, (list, tuple)) or len(row) < 6:
            continue
        try:
            ts = pd.to_datetime(row[0], utc=True, errors="coerce")
            vals = [safe_float(row[i], float("nan")) for i in range(1, 6)]
            if pd.isna(ts) or not all(math.isfinite(v) for v in vals[:4]):
                continue
            parsed.append({"timestamp": ts, "open": vals[0], "high": vals[1], "low": vals[2],
                           "close": vals[3], "volume": max(0.0, vals[4]),
                           "oi": safe_float(row[6], float("nan")) if len(row) > 6 else float("nan")})
        except (TypeError, ValueError, OverflowError):
            continue
    frame = pd.DataFrame(parsed)
    if frame.empty:
        return pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
    return frame.sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)


# =============================================================================
# Mathematical indicators (Wilder ATR/ADX/RSI, VWAP and delta)
# =============================================================================

def calculate_atr(frame: pd.DataFrame, period: int = 14) -> pd.Series:
    """Wilder ATR. Overnight gap is excluded at session boundaries."""
    if frame is None or frame.empty:
        return pd.Series(dtype=float)
    work = frame.copy()
    high = pd.to_numeric(work["high"], errors="coerce")
    low = pd.to_numeric(work["low"], errors="coerce")
    close = pd.to_numeric(work["close"], errors="coerce")
    prev_close = close.shift(1)
    if "timestamp" in work:
        dates = pd.to_datetime(work["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
        prev_close = prev_close.mask(dates.ne(dates.shift(1)), pd.to_numeric(work["open"], errors="coerce"))
    tr = pd.concat([(high - low), (high - prev_close).abs(), (low - prev_close).abs()], axis=1).max(axis=1)
    n = max(2, int(period))
    return tr.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()


def calculate_vwap(frame: pd.DataFrame) -> pd.Series:
    """Session VWAP, weighted by supplied volume; input must use index prices."""
    if frame is None or frame.empty:
        return pd.Series(dtype=float)
    work = frame.copy()
    typical = (pd.to_numeric(work["high"], errors="coerce") + pd.to_numeric(work["low"], errors="coerce") + pd.to_numeric(work["close"], errors="coerce")) / 3.0
    volume = pd.to_numeric(work["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    dates = pd.to_datetime(work["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
    cumulative_volume = volume.groupby(dates).cumsum()
    cumulative_pv = (typical * volume).groupby(dates).cumsum()
    vwap = cumulative_pv / cumulative_volume.replace(0.0, np.nan)
    # A no-volume index feed cannot define a true volume VWAP. Keep it NaN rather
    # than quietly substituting a price mean and presenting that as VWAP.
    return vwap


def calculate_vwap_bands(frame: pd.DataFrame) -> tuple[float, float, float, float, float]:
    """Return session VWAP, weighted sigma, +/-1 sigma and +/-2 sigma levels."""
    if frame is None or frame.empty:
        return (float("nan"),) * 5
    work = frame.copy()
    typical = (pd.to_numeric(work["high"], errors="coerce") + pd.to_numeric(work["low"], errors="coerce") + pd.to_numeric(work["close"], errors="coerce")) / 3.0
    volume = pd.to_numeric(work["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    dates = pd.to_datetime(work["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
    cv = volume.groupby(dates).cumsum()
    cpv = (typical * volume).groupby(dates).cumsum()
    cp2v = (typical.pow(2) * volume).groupby(dates).cumsum()
    vwap_series = cpv / cv.replace(0.0, np.nan)
    var = (cp2v / cv.replace(0.0, np.nan)) - vwap_series.pow(2)
    std = np.sqrt(var.clip(lower=0.0))
    if not vwap_series.notna().any():
        return (float("nan"),) * 5
    vwap = safe_float(vwap_series.iloc[-1])
    sigma = safe_float(std.iloc[-1])
    if not finite(vwap) or not finite(sigma):
        return (float("nan"),) * 5
    return vwap, sigma, vwap + sigma, vwap - sigma, vwap + 2 * sigma


def calculate_adx(frame: pd.DataFrame, period: int = 14) -> tuple[pd.Series, pd.Series, pd.Series]:
    """Standard Wilder +DI, -DI, ADX with full warm-up windows."""
    if frame is None or frame.empty:
        empty = pd.Series(dtype=float)
        return empty, empty, empty
    high = pd.to_numeric(frame["high"], errors="coerce")
    low = pd.to_numeric(frame["low"], errors="coerce")
    close = pd.to_numeric(frame["close"], errors="coerce")
    prev_high, prev_low, prev_close = high.shift(1), low.shift(1), close.shift(1)
    if "timestamp" in frame:
        dates = pd.to_datetime(frame["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
        new_session = dates.ne(dates.shift(1))
        prev_high = prev_high.mask(new_session, high)
        prev_low = prev_low.mask(new_session, low)
        prev_close = prev_close.mask(new_session, close)
    up = high - prev_high
    down = prev_low - low
    valid = up.notna() & down.notna()
    plus_dm = pd.Series(np.where((up > down) & (up > 0), up, 0.0), index=frame.index, dtype=float).where(valid)
    minus_dm = pd.Series(np.where((down > up) & (down > 0), down, 0.0), index=frame.index, dtype=float).where(valid)
    tr = pd.concat([(high - low), (high - prev_close).abs(), (low - prev_close).abs()], axis=1).max(axis=1)
    n = max(2, int(period))
    atr = tr.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    plus_s = plus_dm.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    minus_s = minus_dm.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    plus_di = 100.0 * plus_s / atr.replace(0.0, np.nan)
    minus_di = 100.0 * minus_s / atr.replace(0.0, np.nan)
    denom = (plus_di + minus_di).replace(0.0, np.nan)
    dx = (100.0 * (plus_di - minus_di).abs() / denom).clip(0.0, 100.0)
    adx = dx.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean().clip(0.0, 100.0)
    return adx, plus_di, minus_di


def calculate_rsi(close: pd.Series, period: int = 14, session_dates: Optional[pd.Series] = None) -> pd.Series:
    values = pd.to_numeric(close, errors="coerce")
    delta = values.diff()
    if session_dates is not None:
        dates = pd.Series(session_dates, index=values.index)
        delta = delta.mask(dates.ne(dates.shift(1)))
    gain, loss = delta.clip(lower=0.0), -delta.clip(upper=0.0)
    n = max(2, int(period))
    avg_gain = gain.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    avg_loss = loss.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    rs = avg_gain / avg_loss.replace(0.0, np.nan)
    rsi = 100.0 - 100.0 / (1.0 + rs)
    rsi = rsi.where(avg_loss > 0.0, 100.0)
    both_flat = (avg_gain == 0.0) & (avg_loss == 0.0)
    return rsi.where(~both_flat, 50.0).clip(0.0, 100.0)


def normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def black_scholes_delta(spot: float, strike: float, years: float, iv: float,
                        rate: float, option_type: str) -> float:
    """European Black-Scholes delta approximation; returns signed put delta."""
    if not all(finite(v) for v in (spot, strike, years, iv, rate)) or spot <= 0 or strike <= 0 or years <= 0 or iv <= 0:
        return float("nan")
    root_t = math.sqrt(years)
    d1 = (math.log(spot / strike) + (rate + 0.5 * iv * iv) * years) / (iv * root_t)
    call_delta = normal_cdf(d1)
    return call_delta if str(option_type).upper() in {"CE", "CALL"} else call_delta - 1.0


def option_years_to_expiry(expiry: str, now: datetime) -> float:
    exp_date = parse_date(expiry)
    if exp_date is None:
        return 1.0 / (365.0 * 24.0 * 60.0)
    expiry_dt = datetime.combine(exp_date, time(15, 30), tzinfo=IST)
    seconds = max(60.0, (expiry_dt - (now.astimezone(IST) if now.tzinfo else now.replace(tzinfo=IST))).total_seconds())
    return seconds / (365.0 * 24.0 * 3600.0)


def parse_option_side(row: dict[str, Any], option_type: str) -> dict[str, Any]:
    block_key = "call_options" if option_type == "CE" else "put_options"
    block = row.get(block_key) if isinstance(row.get(block_key), dict) else {}
    market = block.get("market_data") if isinstance(block.get("market_data"), dict) else {}
    greeks = block.get("option_greeks") if isinstance(block.get("option_greeks"), dict) else {}
    return {
        "instrument_key": str(block.get("instrument_key", "")),
        "ltp": safe_float(market.get("ltp")),
        "close_price": safe_float(market.get("close_price")),
        "oi": max(0.0, safe_float(market.get("oi"), 0.0)),
        "prev_oi": max(0.0, safe_float(market.get("prev_oi"), float("nan"))),
        "volume": max(0.0, safe_float(market.get("volume"), 0.0)),
        "bid": safe_float(market.get("bid_price")),
        "ask": safe_float(market.get("ask_price")),
        "bid_qty": max(0.0, safe_float(market.get("bid_qty"), 0.0)),
        "ask_qty": max(0.0, safe_float(market.get("ask_qty"), 0.0)),
        "delta": safe_float(greeks.get("delta")),
        "theta": safe_float(greeks.get("theta")),
        "iv": safe_float(greeks.get("iv")),
    }


# =============================================================================
# Historical/candle preparation and indicators
# =============================================================================

def merge_index_with_futures_volume(index_frame: pd.DataFrame, futures_frame: pd.DataFrame) -> tuple[pd.DataFrame, str]:
    """Keep NIFTY index OHLC; use futures volume only if index volume is unavailable/zero."""
    if index_frame.empty:
        return index_frame, "UNAVAILABLE"
    out = index_frame.copy()
    out["volume"] = pd.to_numeric(out["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    if out["volume"].sum() > 0:
        return out, "NIFTY_INDEX_CANDLE_VOLUME"
    if not futures_frame.empty and "volume" in futures_frame:
        fut = futures_frame[["timestamp", "volume"]].copy()
        fut["volume"] = pd.to_numeric(fut["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
        out = out.drop(columns=["volume"]).merge(fut, on="timestamp", how="left")
        out["volume"] = pd.to_numeric(out["volume"], errors="coerce").fillna(0.0)
        if out["volume"].sum() > 0:
            return out, "NIFTY_FUTURES_VOLUME_PROXY_INDEX_PRICE"
    return out, "NO_VALID_VOLUME"


def _combine_history_and_session(history: pd.DataFrame, session: pd.DataFrame) -> pd.DataFrame:
    columns = ["timestamp", "open", "high", "low", "close", "volume", "oi"]
    parts = []
    for frame in (history, session):
        if frame is not None and not frame.empty:
            part = frame.copy()
            for col in columns:
                if col not in part:
                    part[col] = np.nan
            parts.append(part[columns])
    if not parts:
        return pd.DataFrame(columns=columns)
    merged = pd.concat(parts, ignore_index=True, sort=False)
    merged["timestamp"] = pd.to_datetime(merged["timestamp"], utc=True, errors="coerce")
    for col in columns[1:]:
        merged[col] = pd.to_numeric(merged[col], errors="coerce")
    return merged.dropna(subset=["timestamp", "open", "high", "low", "close"]).sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)


def build_indicators(
    now: datetime,
    spot: float,
    index_session: pd.DataFrame,
    futures_session: pd.DataFrame,
    historical_seed: pd.DataFrame,
    config: Config,
    previous_close: float = float("nan"),
) -> IndicatorSet:
    if index_session.empty:
        raise ScannerError("NIFTY index 1-minute candle feed is empty; no structure can be calculated.")
    session, volume_source = merge_index_with_futures_volume(index_session, futures_session)
    combined = _combine_history_and_session(historical_seed, session)
    if combined.empty:
        raise ScannerError("Insufficient valid index candles to calculate indicators.")
    atr_series = calculate_atr(combined, config.atr_period)
    adx_series, plus_series, minus_series = calculate_adx(combined, config.adx_period)
    rsi_series = calculate_rsi(combined["close"], config.rsi_period,
                              session_dates=pd.to_datetime(combined["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date)
    current_day = now.astimezone(IST).date() if now.tzinfo else now.replace(tzinfo=IST).date()
    combined_dates = pd.to_datetime(combined["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
    today_mask = combined_dates.eq(current_day)
    session_indicators = combined.loc[today_mask].copy().reset_index(drop=True)
    if session_indicators.empty:
        raise ScannerError("Historical seed has no current-session bars and live index candles were not usable.")
    vwap, sigma, upper1, lower1, upper2 = calculate_vwap_bands(session_indicators)
    lower2 = vwap - 2 * sigma if finite(vwap) and finite(sigma) else float("nan")
    # vwap slope measured across the last ~3 current-session points.
    vwap_series = calculate_vwap(session_indicators)
    vwap_slope = float("nan")
    if vwap_series.notna().sum() >= 2:
        valid_v = vwap_series.dropna()
        vwap_slope = float(valid_v.iloc[-1] - valid_v.iloc[max(0, len(valid_v) - 4)])
    last_idx = len(combined) - 1
    atr = safe_float(atr_series.iloc[last_idx]) if len(atr_series) else float("nan")
    adx = safe_float(adx_series.iloc[last_idx]) if len(adx_series) else float("nan")
    plus_di = safe_float(plus_series.iloc[last_idx]) if len(plus_series) else float("nan")
    minus_di = safe_float(minus_series.iloc[last_idx]) if len(minus_series) else float("nan")
    rsi = safe_float(rsi_series.iloc[last_idx]) if len(rsi_series) else float("nan")
    recent = session_indicators.tail(3)
    prior = session_indicators.iloc[max(0, len(session_indicators) - 6):max(0, len(session_indicators) - 3)]
    recent_range = safe_float(recent["high"].max() - recent["low"].min()) if not recent.empty else float("nan")
    prior_range = safe_float(prior["high"].max() - prior["low"].min()) if not prior.empty else float("nan")
    range_limit = max(config.compression_atr_multiple * atr * math.sqrt(max(1, len(recent))), 0.20 * _estimate_strike_step_from_price(spot)) if finite(atr) else float("nan")
    compressed = bool(finite(recent_range) and finite(range_limit) and recent_range <= range_limit and
                      (not finite(prior_range) or prior_range <= 0 or recent_range <= prior_range * 0.80 or recent_range <= range_limit * 0.70))
    close_series = pd.to_numeric(session_indicators["close"], errors="coerce")
    momentum = float("nan")
    if len(close_series) >= 2:
        back = close_series.iloc[max(0, len(close_series) - 4)]
        if finite(back) and back != 0:
            momentum = (safe_float(close_series.iloc[-1]) / float(back)) - 1.0
    swing_look = session_indicators.tail(5)
    swing_low = safe_float(swing_look["low"].min()) if not swing_look.empty else float("nan")
    swing_high = safe_float(swing_look["high"].max()) if not swing_look.empty else float("nan")
    session_open = safe_float(session_indicators["open"].iloc[0]) if not session_indicators.empty else float("nan")
    return IndicatorSet(
        spot=spot, vwap=vwap, vwap_slope=vwap_slope, stddev=sigma,
        upper_1sd=upper1, lower_1sd=lower1, upper_2sd=upper2, lower_2sd=lower2,
        atr=atr, adx=adx, plus_di=plus_di, minus_di=minus_di, rsi=rsi,
        momentum_3m_pct=momentum, recent_range=recent_range, prior_range=prior_range,
        compressed=compressed, swing_low=swing_low, swing_high=swing_high,
        previous_close=previous_close, session_open=session_open,
        candles_count=len(session_indicators), indicators_seeded=(finite(adx) and finite(atr)),
        volume_source=volume_source,
    )


def _estimate_strike_step_from_price(spot: float) -> float:
    # Only a compression-normalization fallback; actual option strike step is inferred from chain.
    if spot >= 30000:
        return 100.0
    return 50.0


def load_historical_seed(client: UpstoxClient, state: dict[str, Any], key: str, now: datetime) -> pd.DataFrame:
    today = now.astimezone(IST).date()
    cache = state.get("historical_seed")
    if isinstance(cache, dict) and cache.get("date") == today.isoformat() and cache.get("instrument_key") == key:
        try:
            rows = cache.get("candles", [])
            return parse_candles(rows)
        except Exception as exc:
            LOGGER.warning("HISTORICAL SEED CACHE INVALID; refetching: %s", exc)
    to_date = today - timedelta(days=1)
    from_date = today - timedelta(days=10)
    try:
        frame = client.candles(key, interval=1, historical=True, from_date=from_date, to_date=to_date)
        rows_out = []
        for row in frame.to_dict(orient="records"):
            ts = parse_timestamp(row.get("timestamp"))
            if ts:
                rows_out.append([ts.isoformat(), row.get("open"), row.get("high"), row.get("low"), row.get("close"), row.get("volume", 0), row.get("oi")])
        state["historical_seed"] = {"date": today.isoformat(), "instrument_key": key, "candles": rows_out[-4000:]}
        LOGGER.info("HISTORICAL INDICATOR SEED: loaded %d prior-session 1m bars.", len(frame))
        return frame
    except Exception as exc:
        LOGGER.warning("HISTORICAL INDICATOR SEED unavailable; early ATR/ADX may remain UNKNOWN: %s", exc)
        state["historical_seed"] = {"date": today.isoformat(), "instrument_key": key, "candles": []}
        return pd.DataFrame()


# =============================================================================
# Multi-horizon option OI, structural walls, and predictive scenarios
# =============================================================================

def chain_rows_by_strike(chain: Sequence[dict[str, Any]]) -> dict[float, dict[str, Any]]:
    output: dict[float, dict[str, Any]] = {}
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"))
        if not finite(strike) or strike <= 0:
            continue
        output[float(strike)] = row
    return output


def infer_strike_step(strikes: Sequence[float], fallback: float = 50.0) -> float:
    clean = sorted({float(s) for s in strikes if finite(s) and float(s) > 0})
    diffs = [b - a for a, b in zip(clean, clean[1:]) if b > a]
    diffs = [d for d in diffs if d >= 1.0]
    return float(np.median(diffs)) if diffs else fallback


def nearest_strike(spot: float, strikes: Sequence[float]) -> float:
    clean = [float(s) for s in strikes if finite(s)]
    if not clean:
        raise ScannerError("Cannot find ATM: option chain has no strike prices.")
    return min(clean, key=lambda s: (abs(s - spot), s))


def _snapshot_map(snapshot: dict[str, Any]) -> dict[float, dict[str, Any]]:
    output: dict[float, dict[str, Any]] = {}
    rows = snapshot.get("rows", [])
    if isinstance(rows, list):
        for row in rows:
            if isinstance(row, dict) and finite(row.get("strike")):
                output[float(row["strike"])] = row
    return output


def _find_snapshot_baseline(snapshots: Sequence[dict[str, Any]], now: datetime,
                            target_minutes: float) -> Optional[tuple[dict[str, Any], float]]:
    # Accept windows broad enough for one missed scheduled scan but never use prior dates.
    # The source label reflects a realistic baseline age. A delayed 2-minute poll
    # must not be described as a one-minute COI measurement.
    ranges = {1.0: (0.45, 1.60), 2.0: (1.40, 3.20), 3.0: (2.20, 4.80),
              5.0: (3.80, 7.50), 15.0: (10.0, 18.5)}
    low, high = ranges[target_minutes]
    matches = []
    for snap in snapshots:
        ts = parse_timestamp(snap.get("timestamp"))
        if not ts or ts.date() != now.astimezone(IST).date():
            continue
        age = (now - ts).total_seconds() / 60.0
        if low <= age <= high:
            matches.append((abs(age - target_minutes), snap, age))
    if not matches:
        return None
    matches.sort(key=lambda v: v[0])
    _, snap, age = matches[0]
    return snap, age


def _pct_change(current: float, baseline: float) -> float:
    if not finite(current) or not finite(baseline) or baseline <= 0:
        return float("nan")
    return (current - baseline) / baseline


def _oi_change_for_side(current_rows: dict[float, dict[str, Any]], baseline: Optional[dict[str, Any]], side_key: str,
                        prev_key: str = "") -> tuple[float, dict[float, float]]:
    if baseline is None:
        return float("nan"), {}
    base_rows = _snapshot_map(baseline)
    changes: dict[float, float] = {}
    numerator = 0.0
    denominator = 0.0
    for strike, row in current_rows.items():
        current = safe_float(row.get(side_key), float("nan"))
        oldrow = base_rows.get(strike, {})
        old = safe_float(oldrow.get(side_key), float("nan"))
        if finite(current) and finite(old) and old > 0:
            changes[strike] = (current - old) / old
            numerator += current - old
            denominator += old
    return (numerator / denominator if denominator > 0 else float("nan")), changes


def classify_wall_state(change_pct: float, threshold: float, available: bool = True) -> str:
    if not available or not finite(change_pct):
        return "UNKNOWN"
    if change_pct <= -threshold:
        return "WEAKENING"
    if change_pct >= threshold:
        return "BUILDING"
    return "STABLE"


def _wall_candidates(rows: dict[float, dict[str, Any]], changes: dict[float, float], spot: float,
                     side: str, step: float, threshold: float) -> list[StructuralWall]:
    side = side.upper()
    oi_key = "call_oi" if side == "CALL" else "put_oi"
    valid = [(k, safe_float(r.get(oi_key), 0.0)) for k, r in rows.items()
             if (k > spot + 0.01 if side == "CALL" else k < spot - 0.01)]
    if not valid:
        return []
    # Inspect the full chain for predictive wall routing: a weak nearby wall must
    # not hide the next intact wall merely because it sits >200 index points away.
    # Materiality/local-peak filtering, rather than a rigid price-distance cut, removes noise.
    focus = valid
    max_oi = max((oi for _, oi in focus), default=0.0)
    if max_oi <= 0:
        return []
    sorted_strikes = sorted(rows)
    walls: list[StructuralWall] = []
    for strike, oi in focus:
        if oi < 0.20 * max_oi:
            continue
        idx = sorted_strikes.index(strike) if strike in rows else -1
        before = safe_float(rows.get(sorted_strikes[idx - 1], {}).get(oi_key), -1.0) if idx > 0 else -1.0
        after = safe_float(rows.get(sorted_strikes[idx + 1], {}).get(oi_key), -1.0) if 0 <= idx < len(sorted_strikes) - 1 else -1.0
        local_peak = oi >= before and oi >= after
        if not local_peak and oi < 0.55 * max_oi:
            continue
        change = changes.get(strike, float("nan"))
        state = classify_wall_state(change, threshold, finite(change))
        walls.append(StructuralWall(strike=strike, side=side, oi=oi,
                                    change_pct=change if finite(change) else None,
                                    state=state, source="TACTICAL_OI_SNAPSHOT" if finite(change) else "OI_CONCENTRATION_ONLY",
                                    distance=abs(strike - spot)))
    # Ensure a wall is available if the local-peak filter eliminated all levels.
    if not walls:
        k, oi = max(focus, key=lambda pair: pair[1])
        change = changes.get(k, float("nan"))
        walls.append(StructuralWall(k, side, oi, change if finite(change) else None,
                                    classify_wall_state(change, threshold, finite(change)),
                                    "TACTICAL_OI_SNAPSHOT" if finite(change) else "OI_CONCENTRATION_ONLY", abs(k - spot)))
    return sorted(walls, key=lambda wall: wall.strike if side == "CALL" else -wall.strike)


def analyze_option_oi(chain: Sequence[dict[str, Any]], prior_snapshots: Sequence[dict[str, Any]],
                      now: datetime, spot: float, config: Config,
                      session_baseline: Optional[dict[str, Any]] = None,
                      session_baseline_source: str = "UNAVAILABLE") -> OIAnalysis:
    chain_map = chain_rows_by_strike(chain)
    if not chain_map:
        raise ScannerError("Option chain has no valid strikes.")
    current: dict[float, dict[str, Any]] = {}
    call_total = put_total = 0.0
    for strike, row in chain_map.items():
        call = parse_option_side(row, "CE")
        put = parse_option_side(row, "PE")
        current[strike] = {"strike": strike, "call_oi": call["oi"], "put_oi": put["oi"],
                           "call_prev_oi": call["prev_oi"], "put_prev_oi": put["prev_oi"]}
        call_total += call["oi"]
        put_total += put["oi"]
    pcr = put_total / call_total if call_total > 0 else float("nan")
    snapshots = sorted([s for s in prior_snapshots if isinstance(s, dict)], key=lambda x: str(x.get("timestamp", "")))
    b1 = _find_snapshot_baseline(snapshots, now, 1.0)
    b2 = _find_snapshot_baseline(snapshots, now, 2.0)
    b3 = _find_snapshot_baseline(snapshots, now, 3.0)
    b5 = _find_snapshot_baseline(snapshots, now, 5.0)
    b15 = _find_snapshot_baseline(snapshots, now, 15.0)
    selected_baseline = None
    selected_age = None
    selected_source = "UNAVAILABLE"
    for label, baseline in (("1M", b1), ("2M", b2), ("3M", b3), ("5M", b5), ("15M", b15)):
        if baseline:
            selected_baseline, selected_age = baseline
            selected_source = label
            break
    call_pct, call_changes = _oi_change_for_side(current, selected_baseline, "call_oi")
    put_pct, put_changes = _oi_change_for_side(current, selected_baseline, "put_oi")
    call_acceleration = put_acceleration = float("nan")
    acceleration_available = False
    # Acceleration is the change in the one-minute OI percentage velocity versus
    # the preceding one-minute interval. It becomes measurable after 09:16 when
    # there are 09:15, 09:16 and current snapshots; before that the velocity score
    # is used without a cold-start penalty.
    one_minute_spacing = bool(b1 is not None and b2 is not None and abs((b2[1] - b1[1]) - 1.0) <= 0.45)
    if selected_source == "1M" and b2 is not None and b1 is not None and one_minute_spacing:
        previous_call_velocity, _ = _oi_change_for_side(_snapshot_map(b1[0]), b2[0], "call_oi")
        previous_put_velocity, _ = _oi_change_for_side(_snapshot_map(b1[0]), b2[0], "put_oi")
        if finite(previous_call_velocity) and finite(previous_put_velocity) and finite(call_pct) and finite(put_pct):
            call_acceleration = call_pct - previous_call_velocity
            put_acceleration = put_pct - previous_put_velocity
            acceleration_available = True
    session_call = session_put = float("nan")
    baseline_quality = "TACTICAL" if selected_baseline else "NO_SAME_SESSION_BASELINE"
    # Session COI must use a separately persisted session-opening/first-observation
    # snapshot. The tactical ring is intentionally pruned after 20 minutes and must
    # never be mislabeled as a session baseline.
    session_base = session_baseline if isinstance(session_baseline, dict) else None
    session_base_ts = parse_timestamp(session_base.get("timestamp")) if session_base else None
    if (session_base_ts is None or session_base_ts.date() != now.astimezone(IST).date()
            or session_base_ts > now + timedelta(seconds=5)):
        session_base = None
    actual_session_source = session_baseline_source if session_base else "UNAVAILABLE"
    if session_base is not None:
        session_call, _ = _oi_change_for_side(current, session_base, "call_oi")
        session_put, _ = _oi_change_for_side(current, session_base, "put_oi")
    if not finite(call_pct) or not finite(put_pct):
        # Upstox prev_oi is useful context but not equivalent to a same-session velocity window.
        # Keep this explicitly labelled so the predictor cannot confuse it with 1m/3m COI.
        call_num = call_den = put_num = put_den = 0.0
        for r in current.values():
            c, cp = safe_float(r.get("call_oi")), safe_float(r.get("call_prev_oi"))
            p, pp = safe_float(r.get("put_oi")), safe_float(r.get("put_prev_oi"))
            if finite(c) and finite(cp) and cp > 0:
                call_num += c - cp; call_den += cp
            if finite(p) and finite(pp) and pp > 0:
                put_num += p - pp; put_den += pp
        if not finite(session_call) and call_den > 0:
            session_call = call_num / call_den
        if not finite(session_put) and put_den > 0:
            session_put = put_num / put_den
    tactical_available = bool(selected_baseline and finite(call_pct) and finite(put_pct))
    if not tactical_available:
        selected_source = "UNAVAILABLE"
        if snapshots:
            baseline_quality = "NO_VALID_TACTICAL_WINDOW"
    elif len(snapshots) == 1:
        baseline_quality = "FIRST_SESSION_SNAPSHOT_WITH_VALID_TACTICAL_BASELINE"
    else:
        baseline_quality = "VALID_SAME_SESSION_TACTICAL_BASELINE"
    # Pin guard is exact per strike: both legs must independently increase >10% over the 5m baseline.
    pin_strikes: list[float] = []
    if b5:
        _, c5_changes = _oi_change_for_side(current, b5[0], "call_oi")
        _, p5_changes = _oi_change_for_side(current, b5[0], "put_oi")
        for strike in current:
            if finite(c5_changes.get(strike)) and finite(p5_changes.get(strike)) and c5_changes[strike] > 0.10 and p5_changes[strike] > 0.10:
                pin_strikes.append(strike)
    # ADX is added by the scenario engine; this is the structural dual-side build diagnostic.
    both_sides_building = bool(finite(call_pct) and finite(put_pct) and
                               call_pct >= config.oi_velocity_trigger and put_pct >= config.oi_velocity_trigger)
    prev_pcr = safe_float(snapshots[-1].get("pcr")) if snapshots else float("nan")
    pcr_spiking = bool(finite(pcr) and finite(prev_pcr) and prev_pcr > 0 and pcr >= prev_pcr * (1.0 + config.pcr_spike_pct))
    call_dominates = bool(finite(call_pct) and call_pct < 0 and
                          (not finite(put_pct) or abs(call_pct) > abs(min(put_pct, 0.0))))
    put_dominates = bool(finite(put_pct) and put_pct < 0 and
                         (not finite(call_pct) or abs(put_pct) > abs(min(call_pct, 0.0))))
    resistance = _wall_candidates(current, call_changes, spot, "CALL", infer_strike_step(list(current)), config.oi_velocity_trigger)
    support = _wall_candidates(current, put_changes, spot, "PUT", infer_strike_step(list(current)), config.oi_velocity_trigger)
    reasons = []
    reasons.append(f"PCR={pcr:.3f}" if finite(pcr) else "PCR=UNAVAILABLE")
    reasons.append(f"tactical_COI={selected_source}" if tactical_available else "tactical_COI=UNAVAILABLE; session proxy not relabelled as velocity")
    if acceleration_available:
        reasons.append(f"COI_acceleration_call={call_acceleration*100:+.3f}% put={put_acceleration*100:+.3f}%")
    else:
        reasons.append("COI acceleration unavailable; tactical velocity retained without a cold-start score penalty")
    if pin_strikes:
        reasons.append("5m pin disqualification at " + ",".join(f"{x:.0f}" for x in sorted(pin_strikes)))
    if both_sides_building:
        reasons.append("aggregate Call and Put OI both building tactically")
    return OIAnalysis(
        rows=current, call_total=call_total, put_total=put_total, pcr=pcr,
        pcr_previous=prev_pcr if finite(prev_pcr) else None, pcr_spiking=pcr_spiking,
        call_coi_pct=call_pct, put_coi_pct=put_pct,
        session_call_coi_pct=session_call, session_put_coi_pct=session_put,
        tactical_source=selected_source, tactical_available=tactical_available,
        tactical_age_minutes=selected_age, pin_market_veto=bool(pin_strikes), pin_strikes=sorted(pin_strikes),
        both_sides_building=both_sides_building, call_unwind_dominates=call_dominates,
        put_unwind_dominates=put_dominates, walls_resistance=resistance, walls_support=support,
        baseline_quality=baseline_quality, reasons=reasons,
        session_baseline_source=actual_session_source,
        call_coi_acceleration_pct=call_acceleration,
        put_coi_acceleration_pct=put_acceleration,
        acceleration_available=acceleration_available,
    )


def make_chain_snapshot(chain: Sequence[dict[str, Any]], oi: OIAnalysis, now: datetime, expiry: str) -> dict[str, Any]:
    rows = []
    chain_map = chain_rows_by_strike(chain)
    for strike in sorted(chain_map):
        row = oi.rows.get(strike, {})
        raw = chain_map[strike]
        call = parse_option_side(raw, "CE")
        put = parse_option_side(raw, "PE")
        rows.append({"strike": strike, "call_oi": row.get("call_oi", call["oi"]), "put_oi": row.get("put_oi", put["oi"])})
    return {"timestamp": ist_iso(now), "expiry": expiry, "pcr": oi.pcr, "rows": rows}


def _nearest_wall(walls: Sequence[StructuralWall], spot: float, direction: str,
                  intact_only: bool = False) -> Optional[StructuralWall]:
    direction = direction.upper()
    candidates = []
    for wall in walls:
        if direction == "BULLISH" and wall.strike <= spot:
            continue
        if direction == "BEARISH" and wall.strike >= spot:
            continue
        if intact_only and wall.state not in {"BUILDING", "STABLE"}:
            continue
        candidates.append(wall)
    if not candidates:
        return None
    return min(candidates, key=lambda w: abs(w.strike - spot))


def _build_oi_wall_context(oi: OIAnalysis, indicators: IndicatorSet) -> tuple[Optional[StructuralWall], Optional[StructuralWall]]:
    return (_nearest_wall(oi.walls_resistance, indicators.spot, "BULLISH"),
            _nearest_wall(oi.walls_support, indicators.spot, "BEARISH"))


def detect_scenario(now: datetime, indicators: IndicatorSet, oi: OIAnalysis,
                    future_regime: str, config: Config) -> Scenario:
    """Single authoritative scenario hierarchy. No prior direction latch is consulted."""
    t = now.astimezone(IST).time() if now.tzinfo else now.replace(tzinfo=IST).time()
    spot, vwap, atr = indicators.spot, indicators.vwap, indicators.atr
    call_pct, put_pct = oi.call_coi_pct, oi.put_coi_pct
    c_session, p_session = oi.session_call_coi_pct, oi.session_put_coi_pct
    trigger = config.oi_velocity_trigger
    above_vwap = finite(vwap) and spot > vwap
    below_vwap = finite(vwap) and spot < vwap
    support_wall = _nearest_wall(oi.walls_support, spot, "BEARISH")
    resistance_wall = _nearest_wall(oi.walls_resistance, spot, "BULLISH")
    proximity = max(config.wall_proximity_atr * atr, 0.75 * infer_strike_step(list(oi.rows))) if finite(atr) else 0.75 * infer_strike_step(list(oi.rows))
    near_res = bool(resistance_wall and resistance_wall.distance <= proximity)
    near_sup = bool(support_wall and support_wall.distance <= proximity)
    tactical_valid = oi.tactical_available and finite(call_pct) and finite(put_pct)
    bullish_coi = tactical_valid and call_pct <= -trigger and put_pct >= -0.25 * trigger
    bearish_coi = tactical_valid and put_pct <= -trigger and call_pct >= -0.25 * trigger
    bullish_gap_coi = tactical_valid and call_pct <= -trigger and put_pct >= 0.25 * trigger
    bearish_gap_coi = tactical_valid and put_pct <= -trigger and call_pct >= 0.25 * trigger
    # If session and tactical flows conflict, only tactical determines direction. Session is diagnostic.
    if tactical_valid and finite(c_session) and finite(p_session):
        session_bullish = c_session <= -trigger and p_session >= 0
        session_bearish = p_session <= -trigger and c_session >= 0
        if (session_bearish and bullish_coi) or (session_bullish and bearish_coi):
            flow_note = f"tactical {oi.tactical_source} COI overrides contradictory session baseline"
        else:
            flow_note = f"tactical COI source={oi.tactical_source}"
    else:
        flow_note = "tactical COI unavailable"
    # Any per-strike 5m dual-side surge disqualifies affected contracts; a strict ADX/chop veto is global.
    if finite(indicators.adx) and indicators.adx < 20.0 and oi.both_sides_building:
        return Scenario("SIDEWAYS_CHOP", "NEUTRAL", 0.0,
                        f"Strict sideways veto: ADX={indicators.adx:.1f}<20 and aggregate Call/Put OI both building; no directional entries.",
                        None, "", False, "SIDEWAYS_ADX_DUAL_SIDE_OI_BUILD", {"adx": indicators.adx, "both_sides_building": True})
    if oi.pin_market_veto:
        # A simultaneous >10% 5m build at the same strike is treated as market-level pin risk only when several strikes pin;
        # isolated strikes remain disqualified in the candidate router.
        if len(oi.pin_strikes) >= 2:
            return Scenario("SIDEWAYS_PIN_RISK", "NEUTRAL", 0.0,
                            f"Pin-risk veto: Call and Put OI each rose >10% over five minutes at {len(oi.pin_strikes)} strikes.",
                            None, "", False, "MARKET_PIN_RISK", {"pin_strikes": oi.pin_strikes})

    # Stage 1 must be able to publish an early *watch* independently of Stage 3 readiness.
    # Missing tactical COI is never fabricated: the scenario is directional but explicitly
    # non-executable until real timestamped OI observations exist.
    if not tactical_valid:
        positive_momentum = finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct > 0
        negative_momentum = finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct < 0
        if indicators.compressed and near_res and above_vwap and positive_momentum and resistance_wall:
            confidence = min(62.0, 42.0 + (8.0 if finite(indicators.vwap_slope) and indicators.vwap_slope > 0 else 0.0)
                             + (6.0 if resistance_wall.state == "WEAKENING" else 0.0))
            return Scenario("PREDICTIVE_BULLISH_WATCH_COI_UNAVAILABLE", "BULLISH", confidence,
                            f"Early bullish watch: NIFTY compressed {resistance_wall.distance:.1f} points below Call-OI wall {resistance_wall.strike:.0f}; spot above VWAP. Tactical COI is unavailable, so wall weakening is unconfirmed; watch only, not trade-ready.",
                            resistance_wall.strike, resistance_wall.state, False, None,
                            {"compressed": True, "tactical_coi_available": False, "wall_weakening_confirmed": resistance_wall.state == "WEAKENING"})
        if indicators.compressed and near_sup and below_vwap and negative_momentum and support_wall:
            confidence = min(62.0, 42.0 + (8.0 if finite(indicators.vwap_slope) and indicators.vwap_slope < 0 else 0.0)
                             + (6.0 if support_wall.state == "WEAKENING" else 0.0))
            return Scenario("PREDICTIVE_BEARISH_WATCH_COI_UNAVAILABLE", "BEARISH", confidence,
                            f"Early bearish watch: NIFTY compressed {support_wall.distance:.1f} points above Put-OI wall {support_wall.strike:.0f}; spot below VWAP. Tactical COI is unavailable, so support weakening is unconfirmed; watch only, not trade-ready.",
                            support_wall.strike, support_wall.state, False, None,
                            {"compressed": True, "tactical_coi_available": False, "wall_weakening_confirmed": support_wall.state == "WEAKENING"})

    # Exhaustion reversal is counter-trend and needs directional loss-of-support/resistance evidence.
    overextended_up = finite(indicators.upper_2sd) and spot > indicators.upper_2sd
    overextended_down = finite(indicators.lower_2sd) and spot < indicators.lower_2sd
    if finite(indicators.adx) and indicators.adx > 40 and overextended_up and tactical_valid:
        support_unwind = put_pct <= -trigger
        bearish_price_turn = (finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct < 0) or (finite(indicators.rsi) and indicators.rsi >= 70)
        if support_unwind and bearish_price_turn:
            confidence = min(95.0, 56.0 + min(20.0, indicators.adx - 40) + min(12.0, abs(put_pct) / trigger * 4.0))
            return Scenario("EXHAUSTION_REVERSAL", "BEARISH", confidence,
                            f"Exhaustion reversal: NIFTY {spot:.2f} above +2σ VWAP band; ADX={indicators.adx:.1f}; Put/support OI unwinding {put_pct*100:+.2f}% tactically with downside momentum. {flow_note}.",
                            support_wall.strike if support_wall else None, support_wall.state if support_wall else "UNKNOWN", True, None,
                            {"adx": indicators.adx, "rsi": indicators.rsi, "sigma_side": "+2", "put_coi_pct": put_pct})
    if finite(indicators.adx) and indicators.adx > 40 and overextended_down and tactical_valid:
        resistance_unwind = call_pct <= -trigger
        bullish_price_turn = (finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct > 0) or (finite(indicators.rsi) and indicators.rsi <= 30)
        if resistance_unwind and bullish_price_turn:
            confidence = min(95.0, 56.0 + min(20.0, indicators.adx - 40) + min(12.0, abs(call_pct) / trigger * 4.0))
            return Scenario("EXHAUSTION_REVERSAL", "BULLISH", confidence,
                            f"Exhaustion reversal: NIFTY {spot:.2f} below -2σ VWAP band; ADX={indicators.adx:.1f}; Call/resistance OI unwinding {call_pct*100:+.2f}% tactically with upside momentum. {flow_note}.",
                            resistance_wall.strike if resistance_wall else None, resistance_wall.state if resistance_wall else "UNKNOWN", True, None,
                            {"adx": indicators.adx, "rsi": indicators.rsi, "sigma_side": "-2", "call_coi_pct": call_pct})

    # Morning gap-and-go: one-minute index data, VWAP alignment, call/put OI flow.
    gap_pct = ((indicators.session_open / indicators.previous_close) - 1.0) if finite(indicators.session_open) and finite(indicators.previous_close) and indicators.previous_close > 0 else float("nan")
    if t < MORNING_END and finite(gap_pct) and gap_pct >= config.gap_threshold_pct and above_vwap and bullish_gap_coi:
        confidence = min(96.0, 65.0 + min(12.0, abs(gap_pct) * 1000) + min(12.0, abs(call_pct) / trigger * 3.0))
        wall = resistance_wall
        return Scenario("MORNING_GAP_GO", "BULLISH", confidence,
                        f"Morning Gap & Go: gap +{gap_pct*100:.2f}%, spot above VWAP, Call OI unwinding {call_pct*100:+.2f}% and Put OI {put_pct*100:+.2f}% ({flow_note}).",
                        wall.strike if wall else None, wall.state if wall else "UNKNOWN", True, None,
                        {"gap_pct": gap_pct, "call_coi_pct": call_pct, "put_coi_pct": put_pct})
    if t < MORNING_END and finite(gap_pct) and gap_pct <= -config.gap_threshold_pct and below_vwap and bearish_gap_coi:
        confidence = min(96.0, 65.0 + min(12.0, abs(gap_pct) * 1000) + min(12.0, abs(put_pct) / trigger * 3.0))
        wall = support_wall
        return Scenario("MORNING_GAP_GO", "BEARISH", confidence,
                        f"Morning Gap & Go down: gap {gap_pct*100:.2f}%, spot below VWAP, Put OI unwinding {put_pct*100:+.2f}% and Call OI {call_pct*100:+.2f}% ({flow_note}).",
                        wall.strike if wall else None, wall.state if wall else "UNKNOWN", True, None,
                        {"gap_pct": gap_pct, "call_coi_pct": call_pct, "put_coi_pct": put_pct})

    # Gamma squeeze gets priority over a generic compression watch when PCR expansion
    # and dominant Call-OI unwinding are simultaneously present.
    if t >= MORNING_END and t < ENTRY_CUTOFF and indicators.compressed and near_res and oi.pcr_spiking and oi.call_unwind_dominates and bullish_coi and above_vwap:
        confidence = min(97.0, 68.0 + min(10.0, abs(call_pct) / trigger * 2.5) + min(8.0, max(0.0, oi.pcr - 1.0) * 10.0))
        return Scenario("GAMMA_SQUEEZE", "BULLISH", confidence,
                        f"Gamma squeeze setup: compression near {resistance_wall.strike:.0f} Call wall, PCR rose {config.pcr_spike_pct*100:.1f}%+ from its last sampled value and Call OI unwinding ({call_pct*100:+.2f}%) dominates Put unwinding ({put_pct*100:+.2f}%). {flow_note}.",
                        resistance_wall.strike, resistance_wall.state, True, None,
                        {"pcr": oi.pcr, "pcr_previous": oi.pcr_previous, "call_coi_pct": call_pct, "put_coi_pct": put_pct})


    # Predictive pre-breakout: price compresses just below a weakening resistance/support; no candle close beyond wall required.
    if indicators.compressed and near_res and resistance_wall and resistance_wall.state == "WEAKENING" and bullish_coi and above_vwap:
        confidence = min(97.0, 66.0 + min(12.0, abs(call_pct) / trigger * 3.0) + (8.0 if oi.pcr_spiking else 0.0))
        return Scenario("PREDICTIVE_BULLISH_BREAKOUT", "BULLISH", confidence,
                        f"NIFTY compressing {resistance_wall.distance:.1f} points below {resistance_wall.strike:.0f} Call-OI resistance; defending Call OI unwinding {call_pct*100:+.2f}% over {oi.tactical_source}; spot is still below wall. {flow_note}.",
                        resistance_wall.strike, resistance_wall.state, True, None,
                        {"compressed": True, "call_coi_pct": call_pct, "put_coi_pct": put_pct, "pcr_spiking": oi.pcr_spiking})
    if indicators.compressed and near_sup and support_wall and support_wall.state == "WEAKENING" and bearish_coi and below_vwap:
        confidence = min(97.0, 66.0 + min(12.0, abs(put_pct) / trigger * 3.0))
        return Scenario("PREDICTIVE_BEARISH_BREAKDOWN", "BEARISH", confidence,
                        f"NIFTY compressing {support_wall.distance:.1f} points above {support_wall.strike:.0f} Put-OI support; defending Put OI unwinding {put_pct*100:+.2f}% over {oi.tactical_source}; spot is still above wall. {flow_note}.",
                        support_wall.strike, support_wall.state, True, None,
                        {"compressed": True, "call_coi_pct": call_pct, "put_coi_pct": put_pct})

    # Low-PCR / rising-Call-OI imbalance from the prior scanner requirements. OI alone
    # cannot identify whether the new Call OI is buying or writing, so the Strike Router
    # additionally requires strong call-premium/order-book flow before allowing entry.
    if (tactical_valid and finite(oi.pcr) and oi.pcr <= 1.0 and call_pct >= trigger
            and above_vwap and finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct > 0
            and future_regime.upper() != "STRONG_SHORT_BUILDUP"):
        confidence = min(86.0, 59.0 + min(12.0, oi.call_total / max(oi.put_total, 1.0))
                         + min(10.0, call_pct / trigger * 2.0))
        return Scenario("PCR_LOW_CALL_OI_IMBALANCE", "BULLISH", confidence,
                        f"Low-PCR Call OI expansion: PCR={oi.pcr:.3f} (<=1.0), Call OI building {call_pct*100:+.2f}% while spot is above VWAP and 1m momentum is positive. Because OI alone cannot distinguish call buying from writing, execution additionally requires strong Call premium/order-book flow. {flow_note}.",
                        resistance_wall.strike if resistance_wall else None, resistance_wall.state if resistance_wall else "UNKNOWN", True, None,
                        {"pcr": oi.pcr, "call_coi_pct": call_pct, "put_coi_pct": put_pct,
                         "requires_option_flow_confirmation": True, "futures_regime": future_regime})

    # A directional continuation is allowed before a completed 3m candle, but must align with VWAP and tactical OI.
    future = future_regime.upper()
    if above_vwap and bullish_coi and finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct > 0 and future != "STRONG_SHORT_BUILDUP":
        confidence = min(91.0, 55.0 + min(15.0, abs(call_pct) / trigger * 2.5) + min(10.0, indicators.momentum_3m_pct * 25000))
        return Scenario("BULLISH_CONTINUATION", "BULLISH", confidence,
                        f"Bullish continuation: spot above NIFTY VWAP, positive 1m momentum, Call OI {call_pct*100:+.2f}% and Put OI {put_pct*100:+.2f}% over {oi.tactical_source}; futures={future}. {flow_note}.",
                        resistance_wall.strike if resistance_wall else None, resistance_wall.state if resistance_wall else "UNKNOWN", True, None,
                        {"call_coi_pct": call_pct, "put_coi_pct": put_pct, "futures_regime": future})
    if below_vwap and bearish_coi and finite(indicators.momentum_3m_pct) and indicators.momentum_3m_pct < 0 and future != "STRONG_LONG_BUILDUP":
        confidence = min(91.0, 55.0 + min(15.0, abs(put_pct) / trigger * 2.5) + min(10.0, abs(indicators.momentum_3m_pct) * 25000))
        return Scenario("BEARISH_CONTINUATION", "BEARISH", confidence,
                        f"Bearish continuation: spot below NIFTY VWAP, negative 1m momentum, Put OI {put_pct*100:+.2f}% and Call OI {call_pct*100:+.2f}% over {oi.tactical_source}; futures={future}. {flow_note}.",
                        support_wall.strike if support_wall else None, support_wall.state if support_wall else "UNKNOWN", True, None,
                        {"call_coi_pct": call_pct, "put_coi_pct": put_pct, "futures_regime": future})

    return Scenario("WATCH_NO_CONFIRMED_SETUP", "NEUTRAL", 0.0,
                    f"No qualifying predictive scenario. VWAP alignment, compression/wall condition, tactical COI, PCR, or futures context is insufficient. {flow_note}.",
                    None, "", False, None,
                    {"above_vwap": above_vwap, "below_vwap": below_vwap, "compressed": indicators.compressed,
                     "call_coi_pct": call_pct, "put_coi_pct": put_pct, "pcr_spiking": oi.pcr_spiking})


def futures_regime_from_snapshots(quote: Optional[LiveQuote], state: dict[str, Any], now: datetime) -> tuple[str, dict[str, Any]]:
    if quote is None or not finite(quote.ltp) or quote.ltp <= 0 or quote.freshness != "FRESH":
        return "UNKNOWN", {"reason": "fresh futures quote unavailable"}
    rows = state.get("futures_snapshots", []) if isinstance(state.get("futures_snapshots"), list) else []
    selected = None
    age_m = None
    for row in reversed(rows):
        ts = parse_timestamp(row.get("timestamp")) if isinstance(row, dict) else None
        if ts and ts.date() == now.astimezone(IST).date():
            age = (now - ts).total_seconds() / 60.0
            if 1.0 <= age <= 5.5:
                selected, age_m = row, age
                break
    if selected is None:
        # previous_oi/prev_close is a session-context proxy only and is not labelled a tactical regime.
        return "UNKNOWN", {"reason": "no same-session 1-5m futures baseline", "session_proxy_available": finite(quote.previous_oi) and quote.previous_oi > 0}
    old_price = safe_float(selected.get("ltp"))
    old_oi = safe_float(selected.get("oi"))
    price_pct = (quote.ltp - old_price) / old_price if finite(old_price) and old_price > 0 else float("nan")
    oi_pct = _pct_change(quote.oi, old_oi)
    if not finite(price_pct) or not finite(oi_pct):
        return "UNKNOWN", {"reason": "invalid futures price/OI baseline", "baseline_age_minutes": age_m}
    min_price_move = 0.00025
    min_oi_move = 0.0010
    if price_pct >= min_price_move and oi_pct >= min_oi_move:
        regime = "STRONG_LONG_BUILDUP" if price_pct >= 0.0005 and oi_pct >= 0.002 else "LONG_BUILDUP"
    elif price_pct <= -min_price_move and oi_pct >= min_oi_move:
        regime = "STRONG_SHORT_BUILDUP" if price_pct <= -0.0005 and oi_pct >= 0.002 else "SHORT_BUILDUP"
    elif price_pct >= min_price_move and oi_pct <= -min_oi_move:
        regime = "SHORT_COVERING"
    elif price_pct <= -min_price_move and oi_pct <= -min_oi_move:
        regime = "LONG_UNWINDING"
    else:
        regime = "NEUTRAL"
    return regime, {"price_change_pct": price_pct, "oi_change_pct": oi_pct, "baseline_age_minutes": age_m, "source": "SAME_SESSION_QUOTE_SNAPSHOTS"}


def append_futures_snapshot(state: dict[str, Any], quote: Optional[LiveQuote], now: datetime) -> None:
    if quote is None or quote.freshness != "FRESH" or not finite(quote.ltp):
        return
    samples = state.get("futures_snapshots", []) if isinstance(state.get("futures_snapshots"), list) else []
    minute_key = ist_iso(now)[:16]
    samples = [s for s in samples if isinstance(s, dict) and str(s.get("timestamp", ""))[:16] != minute_key]
    samples.append({"timestamp": ist_iso(now), "instrument_key": quote.instrument_key, "ltp": quote.ltp, "oi": quote.oi})
    cutoff = now - timedelta(minutes=20)
    samples = [s for s in samples if (parse_timestamp(s.get("timestamp")) or datetime.min.replace(tzinfo=IST)) >= cutoff]
    state["futures_snapshots"] = samples[-32:]


# =============================================================================
# Strike quality, premium VWAP, targets and stops
# =============================================================================

def allowed_strikes(spot: float, strikes: Sequence[float], direction: str, now: datetime,
                    scenario: Scenario, indicators: IndicatorSet) -> tuple[float, list[tuple[float, str]]]:
    atm = nearest_strike(spot, strikes)
    step = infer_strike_step(strikes)
    direction = direction.upper()
    if direction == "BULLISH":
        permitted = [(atm, "ATM"), (atm - step, "ITM1"), (atm - 2 * step, "ITM2")]
        otm = atm + step
    else:
        permitted = [(atm, "ATM"), (atm + step, "ITM1"), (atm + 2 * step, "ITM2")]
        otm = atm - step
    available = {round(float(s), 2) for s in strikes}
    permitted = [(float(s), label) for s, label in permitted if round(float(s), 2) in available]
    t = now.astimezone(IST).time() if now.tzinfo else now.replace(tzinfo=IST).time()
    confirmed_afternoon_squeeze = (
        t >= MIDDAY_END and t < ENTRY_CUTOFF and scenario.state == "GAMMA_SQUEEZE"
        and scenario.confidence >= 80.0 and finite(indicators.adx) and indicators.adx >= 25.0
        and finite(indicators.momentum_3m_pct) and abs(indicators.momentum_3m_pct) >= 0.00075
    )
    if confirmed_afternoon_squeeze and round(otm, 2) in available:
        permitted.append((float(otm), "OTM1_CONFIRMED_AFTERNOON_SQUEEZE"))
    return atm, permitted


def _session_premium_vwap(frame: pd.DataFrame, now: datetime) -> float:
    if frame is None or frame.empty or "volume" not in frame:
        return float("nan")
    local_dates = pd.to_datetime(frame["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
    today = now.astimezone(IST).date() if now.tzinfo else now.replace(tzinfo=IST).date()
    work = frame.loc[local_dates == today].copy()
    if work.empty:
        return float("nan")
    volume = pd.to_numeric(work["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    price = (pd.to_numeric(work["high"], errors="coerce") + pd.to_numeric(work["low"], errors="coerce") + pd.to_numeric(work["close"], errors="coerce")) / 3.0
    total = float(volume.sum())
    if total <= 0:
        return float("nan")
    return float((price * volume).sum() / total)


def _option_candle_flow(frame: pd.DataFrame, ltp: float, direction: str, depth_imbalance: float) -> tuple[float, float, float]:
    """Return [0,1] flow-quality, latest premium return, recent/median volume ratio."""
    if frame is None or frame.empty or "close" not in frame.columns or "volume" not in frame.columns:
        return float("nan"), float("nan"), float("nan")
    close = pd.to_numeric(frame["close"], errors="coerce").dropna()
    volumes = pd.to_numeric(frame["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    ret = float("nan")
    if len(close) >= 2 and close.iloc[-2] > 0:
        ret = (ltp / float(close.iloc[-2])) - 1.0
    if len(close) < 2 or not finite(ret):
        return float("nan"), ret, float("nan")
    # This is a long-option quality score; positive premium movement is favorable for CE and PE alike.
    aligned_ret = ret
    momentum_score = clamp(0.5 + (aligned_ret / 0.004) * 0.5) if finite(aligned_ret) else 0.5
    depth_score = clamp(0.5 + 0.5 * depth_imbalance)
    if len(volumes) >= 3:
        current_vol = float(volumes.iloc[-1])
        baseline = float(volumes.iloc[-min(8, len(volumes) - 1):-1].median()) if len(volumes) > 1 else 0.0
        vol_ratio = current_vol / baseline if baseline > 0 else (1.0 if current_vol > 0 else 0.0)
    else:
        vol_ratio = 1.0 if float(volumes.sum()) > 0 else 0.0
    volume_score = clamp(vol_ratio / 2.0)
    return clamp(0.50 * momentum_score + 0.30 * depth_score + 0.20 * volume_score), ret, vol_ratio


def _coi_score(direction: str, oi: OIAnalysis, config: Config, scenario_state: str = "") -> float:
    """Normalize tactical COI velocity; blend measured acceleration when available.

    If acceleration is unavailable during the first tactical interval, its component
    is not treated as zero and does not penalize the entry score. The 30% component
    uses velocity until an actual second velocity observation makes acceleration measurable.
    """
    if not oi.tactical_available or not finite(oi.call_coi_pct) or not finite(oi.put_coi_pct):
        return float("nan")
    trig = max(config.oi_velocity_trigger, 0.0001)
    if direction == "BULLISH" and scenario_state == "PCR_LOW_CALL_OI_IMBALANCE" and finite(oi.pcr) and oi.pcr <= 1.0:
        velocity_score = clamp(0.70 * clamp(oi.call_coi_pct / (2.0 * trig))
                               + 0.30 * clamp(oi.put_coi_pct / (2.0 * trig)))
        if not oi.acceleration_available:
            return velocity_score
        accel_score = clamp(0.70 * clamp(0.5 + oi.call_coi_acceleration_pct / (2.0 * trig))
                            + 0.30 * clamp(0.5 + oi.put_coi_acceleration_pct / (2.0 * trig)))
    elif direction == "BULLISH":
        velocity_score = clamp(0.65 * clamp((-oi.call_coi_pct) / (2.0 * trig))
                               + 0.35 * clamp(oi.put_coi_pct / (2.0 * trig)))
        if not oi.acceleration_available:
            return velocity_score
        accel_score = clamp(0.65 * clamp(0.5 - oi.call_coi_acceleration_pct / (2.0 * trig))
                            + 0.35 * clamp(0.5 + oi.put_coi_acceleration_pct / (2.0 * trig)))
    else:
        velocity_score = clamp(0.65 * clamp((-oi.put_coi_pct) / (2.0 * trig))
                               + 0.35 * clamp(oi.call_coi_pct / (2.0 * trig)))
        if not oi.acceleration_available:
            return velocity_score
        accel_score = clamp(0.65 * clamp(0.5 - oi.put_coi_acceleration_pct / (2.0 * trig))
                            + 0.35 * clamp(0.5 + oi.call_coi_acceleration_pct / (2.0 * trig)))
    return clamp(0.70 * velocity_score + 0.30 * accel_score)


def _candidate_from_data(
    *, row: dict[str, Any], strike: float, option_type: str, expiry: str,
    quote: LiveQuote, candle_frame: pd.DataFrame,
    oi: OIAnalysis, direction: str, now: datetime, indicators: IndicatorSet,
    config: Config, moneyness: str, pin_disqualified: bool, exhaustion: bool = False,
    scenario_state: str = "",
) -> OptionContract:
    side = parse_option_side(row, option_type)
    # Never silently fall back to the untimestamped chain LTP when the dedicated
    # live quote is missing: a fresh depth snapshot without a valid LTP is not executable.
    ltp = quote.ltp
    iv_raw = side["iv"]
    iv = iv_raw / 100.0 if finite(iv_raw) and iv_raw > 2.0 else iv_raw
    delta_api = side["delta"]
    if finite(delta_api) and abs(delta_api) <= 1.0:
        delta, delta_source = delta_api, "UPSTOX_GREEKS"
    else:
        iv_model = iv if finite(iv) and iv > 0 else config.fallback_iv
        delta = black_scholes_delta(indicators.spot, strike, option_years_to_expiry(expiry, now), iv_model,
                                    config.risk_free_rate, option_type)
        delta_source = "BLACK_SCHOLES_APPROX_IV" if finite(iv) and iv > 0 else "BLACK_SCHOLES_APPROX_FALLBACK_IV"
    premium_vwap = _session_premium_vwap(candle_frame, now)
    flow_score, premium_return, volume_ratio = _option_candle_flow(candle_frame, ltp, direction, quote.depth_imbalance)
    lift_ratio = (ltp / premium_vwap - 1.0) if finite(ltp) and finite(premium_vwap) and premium_vwap > 0 else float("nan")
    vwap_score = clamp(lift_ratio / 0.003) if finite(lift_ratio) else float("nan")
    coi_score = _coi_score(direction, oi, config, scenario_state=scenario_state)
    weighted_components = [(0.40, flow_score, "FLOW"), (0.30, vwap_score, "PREMIUM_VWAP"), (0.30, coi_score, "TACTICAL_COI")]
    available_components = [(weight, value, label) for weight, value, label in weighted_components if finite(value)]
    total_weight = sum(weight for weight, _, _ in available_components)
    total = (sum(weight * value for weight, value, _ in available_components) / total_weight
             if total_weight > 0 else float("nan"))
    score_basis = "FULL_40_30_30" if len(available_components) == 3 else "PROVISIONAL_" + "_".join(label for _, _, label in available_components)
    vetoes: list[str] = []
    if quote.freshness != "FRESH":
        vetoes.append(f"QUOTE_{quote.freshness}")
    if not finite(ltp) or ltp <= 0:
        vetoes.append("LIVE_OPTION_LTP_UNAVAILABLE_OR_NONPOSITIVE")
    if not finite(quote.bid) or not finite(quote.ask) or quote.bid <= 0 or quote.ask < quote.bid:
        vetoes.append("INVALID_BID_ASK")
    if not finite(quote.spread_ratio) or quote.spread_ratio > config.max_spread_ratio:
        vetoes.append(f"SPREAD>{config.max_spread_ratio*100:.3f}%")
    if not finite(premium_vwap) or premium_vwap <= 0:
        vetoes.append("OPTION_PREMIUM_VWAP_UNAVAILABLE")
    elif not finite(ltp) or ltp <= premium_vwap:
        vetoes.append("OPTION_LTP_NOT_ABOVE_OWN_1M_VWAP")
    delta_floor = config.min_exhaustion_delta if exhaustion else config.min_directional_delta
    if not finite(delta) or abs(delta) < delta_floor:
        vetoes.append(f"DELTA<{delta_floor:.2f}")
    if pin_disqualified:
        vetoes.append("PIN_DISQUALIFICATION_CALL_AND_PUT_OI_BOTH_UP_GT10PCT_5M")
    if not finite(flow_score):
        vetoes.append("OPTION_FLOW_SCORE_UNAVAILABLE_REQUIRES_MORE_1M_CANDLES")
    if not finite(vwap_score):
        vetoes.append("PREMIUM_VWAP_LIFT_SCORE_UNAVAILABLE")
    if scenario_state == "PCR_LOW_CALL_OI_IMBALANCE" and direction == "BULLISH" and (not finite(flow_score) or flow_score < 0.65):
        vetoes.append("LOW_PCR_SETUP_REQUIRES_STRONG_OPTION_FLOW_SCORE>=0.650")
    if not oi.tactical_available or not finite(coi_score):
        vetoes.append("TACTICAL_COI_BASELINE_UNAVAILABLE")
    elif finite(total) and total < config.min_score:
        vetoes.append(f"SCORE<{config.min_score:.3f}")
    return OptionContract(
        instrument_key=quote.instrument_key,
        trading_symbol=quote.symbol,
        option_type=option_type,
        strike=strike,
        expiry=expiry,
        ltp=ltp,
        oi=side["oi"], prev_oi=side["prev_oi"], volume=quote.volume if finite(quote.volume) else side["volume"],
        bid=quote.bid, ask=quote.ask, bid_qty=quote.bid_qty, ask_qty=quote.ask_qty,
        delta=delta, theta=side["theta"], iv=iv, delta_source=delta_source,
        spread_ratio=quote.spread_ratio, premium_vwap=premium_vwap,
        flow_score=flow_score, vwap_lift_score=vwap_score, coi_score=coi_score, total_score=total,
        call_coi_pct=oi.call_coi_pct, put_coi_pct=oi.put_coi_pct, tactical_source=oi.tactical_source,
        quote_freshness=quote.freshness, quote_age_seconds=quote.age_seconds,
        premium_return_pct=premium_return * 100.0 if finite(premium_return) else float("nan"),
        volume_ratio=volume_ratio, pin_disqualified=pin_disqualified, vetoes=tuple(vetoes),
        score_basis=score_basis, score_components_available=tuple(label for _, _, label in available_components),
    )


def select_option_contract(
    chain: Sequence[dict[str, Any]], spot: float, scenario: Scenario, now: datetime,
    indicators: IndicatorSet, oi: OIAnalysis, quotes: Mapping[str, LiveQuote],
    option_candles: Mapping[str, pd.DataFrame], expiry: str, config: Config,
    preferred_instrument_key: Optional[str] = None,
) -> tuple[Optional[OptionContract], list[dict[str, Any]]]:
    """Stage 2: rank candidate contracts; do not hide a useful candidate because it fails readiness.

    A passing contract is preferred. If no contract passes all execution gates, return the
    best observable contract for diagnostics only. Stage 3 independently applies its vetoes.
    """
    if scenario.direction not in {"BULLISH", "BEARISH"}:
        return None, []
    chain_map = chain_rows_by_strike(chain)
    strikes = sorted(chain_map)
    atm, permitted = allowed_strikes(spot, strikes, scenario.direction, now, scenario, indicators)
    option_type = "CE" if scenario.direction == "BULLISH" else "PE"
    pin_set = set(oi.pin_strikes)
    candidates: list[OptionContract] = []
    diagnostics: list[dict[str, Any]] = []
    for strike, moneyness in permitted:
        raw_row = chain_map.get(round(strike, 2)) or chain_map.get(strike)
        if not isinstance(raw_row, dict):
            diagnostics.append({"strike": strike, "moneyness": moneyness, "option_type": option_type,
                                "vetoes": ["STRIKE_NOT_IN_LIVE_CHAIN"], "execution_eligible": False})
            continue
        side = parse_option_side(raw_row, option_type)
        key = side["instrument_key"]
        quote = quotes.get(key)
        if not key or quote is None:
            diagnostics.append({"strike": strike, "moneyness": moneyness, "option_type": option_type,
                                "vetoes": ["LIVE_QUOTE_UNAVAILABLE"], "execution_eligible": False})
            continue
        candidate = _candidate_from_data(
            row=raw_row, strike=strike, option_type=option_type, expiry=expiry, quote=quote,
            candle_frame=option_candles.get(key, pd.DataFrame()), oi=oi, direction=scenario.direction,
            now=now, indicators=indicators, config=config, moneyness=moneyness,
            pin_disqualified=(strike in pin_set), exhaustion="EXHAUSTION" in scenario.state,
            scenario_state=scenario.state,
        )
        candidates.append(candidate)
        diagnostics.append({
            "strike": strike, "moneyness": moneyness, "option_type": option_type,
            "instrument_key": key, "score": candidate.total_score, "score_basis": candidate.score_basis,
            "score_components_available": list(candidate.score_components_available),
            "flow_score": candidate.flow_score, "vwap_lift_score": candidate.vwap_lift_score,
            "coi_score": candidate.coi_score, "vetoes": list(candidate.vetoes),
            "execution_eligible": not candidate.vetoes,
            "premium_vwap": candidate.premium_vwap, "ltp": candidate.ltp,
            "delta": candidate.delta, "spread_ratio": candidate.spread_ratio,
            "quote_freshness": candidate.quote_freshness,
        })

    if not candidates:
        return None, diagnostics
    passing = [candidate for candidate in candidates if not candidate.vetoes]
    pool = passing if passing else candidates
    # A full 40/30/30 score is more comparable than a provisional, renormalized score.
    pool.sort(key=lambda c: (0 if c.score_basis == "FULL_40_30_30" else 1,
                             -(c.total_score if finite(c.total_score) else -1.0),
                             0 if c.strike == atm else 1, c.strike))
    selected = pool[0]
    # Stickiness is allowed only among truly execution-eligible candidates.
    if passing and preferred_instrument_key:
        preferred = next((c for c in passing if c.instrument_key == preferred_instrument_key), None)
        if preferred and finite(preferred.total_score) and finite(selected.total_score) and \
                preferred.total_score >= selected.total_score - config.strike_stickiness_tolerance:
            selected = preferred
    for diagnostic in diagnostics:
        diagnostic["best_candidate_for_review"] = bool(
            diagnostic.get("instrument_key") == selected.instrument_key
            and diagnostic.get("strike") == selected.strike
        )
        diagnostic["selected_for_execution"] = bool(
            not selected.vetoes and diagnostic.get("instrument_key") == selected.instrument_key
            and diagnostic.get("strike") == selected.strike
        )
    return selected, diagnostics


def route_targets_and_stop(scenario: Scenario, spot: float, indicators: IndicatorSet,
                           oi: OIAnalysis, config: Config) -> RiskPlan:
    """Route T1/T2 to intact opposing OI walls; use real price-action swings as fallback."""
    if scenario.direction not in {"BULLISH", "BEARISH"}:
        return RiskPlan(False, None, None, None, "", "", "", (), "No directional scenario.")
    atr = indicators.atr
    if not finite(atr) or atr <= 0:
        return RiskPlan(False, None, None, None, "", "", "", (), "ATR unavailable; cannot apply required 0.10 ATR stop buffer.")
    bullish = scenario.direction == "BULLISH"
    target_walls = oi.walls_resistance if bullish else oi.walls_support
    stop_walls = oi.walls_support if bullish else oi.walls_resistance
    candidates = sorted([w for w in target_walls if (w.strike > spot if bullish else w.strike < spot)],
                        key=lambda w: w.strike if bullish else -w.strike)
    skipped: list[float] = []
    intact: list[StructuralWall] = []
    for wall in candidates:
        if wall.state == "WEAKENING":
            skipped.append(wall.strike)
            continue
        if wall.state in {"BUILDING", "STABLE"}:
            intact.append(wall)
    t1, t2 = None, None
    t1_source = t2_source = ""
    min_distance = max(0.20 * atr, 1.0)
    if intact:
        valid_intact = [w for w in intact if abs(w.strike - spot) >= min_distance]
        if valid_intact:
            t1 = valid_intact[0].strike
            t1_source = f"INTACT_{valid_intact[0].side}_OI_WALL_{valid_intact[0].state}"
            for wall in valid_intact[1:]:
                if (wall.strike > t1 if bullish else wall.strike < t1):
                    t2 = wall.strike
                    t2_source = f"NEXT_INTACT_{wall.side}_OI_WALL_{wall.state}"
                    break
    # If T1 has no intact OI wall, use a real same-session price swing, never a synthetic target.
    swing_target = indicators.swing_high if bullish else indicators.swing_low
    if t1 is None and finite(swing_target) and (swing_target > spot + min_distance if bullish else swing_target < spot - min_distance):
        t1 = swing_target
        t1_source = "CURRENT_SESSION_1M_SWING_EXTREME"
    if t1 is not None and t2 is None:
        # T2 may be a real price swing beyond T1 if no second intact OI wall exists.
        swing2 = indicators.swing_high if bullish else indicators.swing_low
        if finite(swing2) and (swing2 > t1 + min_distance if bullish else swing2 < t1 - min_distance):
            t2 = swing2
            t2_source = "CURRENT_SESSION_1M_SWING_BEYOND_T1"
    # SL uses the nearer valid 1m pivot or local same-side OI wall, then offsets 0.10 ATR.
    local_pivot = indicators.swing_low if bullish else indicators.swing_high
    structural = None
    stop_candidates = [w for w in stop_walls if (w.strike < spot if bullish else w.strike > spot)
                       and w.state in {"BUILDING", "STABLE"}]
    if stop_candidates:
        structural = max(stop_candidates, key=lambda w: w.strike) if bullish else min(stop_candidates, key=lambda w: w.strike)
    support_levels = []
    if finite(local_pivot) and (local_pivot < spot if bullish else local_pivot > spot):
        support_levels.append(local_pivot)
    if structural and (structural.strike < spot if bullish else structural.strike > spot):
        support_levels.append(structural.strike)
    if not support_levels:
        return RiskPlan(False, t1, t2, None, "", t1_source, t2_source, tuple(skipped), "No valid 1-minute pivot or intact structural wall for stop placement.")
    base = max(support_levels) if bullish else min(support_levels)
    stop = base - 0.10 * atr if bullish else base + 0.10 * atr
    stop_source = ("NEAREST_1M_PIVOT_OR_INTACT_PUT_SUPPORT_MINUS_0.10_ATR" if bullish
                   else "NEAREST_1M_PIVOT_OR_INTACT_CALL_RESISTANCE_PLUS_0.10_ATR")
    t1_ok = t1 is not None and (t1 > spot if bullish else t1 < spot)
    t2_ok = t2 is None or (t1 is not None and (t2 > t1 if bullish else t2 < t1))
    stop_ok = stop is not None and (stop < spot if bullish else stop > spot)
    if not (t1_ok and t2_ok and stop_ok):
        missing = []
        if t1 is None: missing.append("T1 unavailable")
        elif not t1_ok: missing.append("T1 on wrong side of spot")
        if t2 is not None and not t2_ok: missing.append("T2 order invalid")
        if stop is None: missing.append("stop unavailable")
        elif not stop_ok: missing.append("stop on wrong side of spot")
        return RiskPlan(False, t1, t2, stop, stop_source, t1_source, t2_source, tuple(skipped), "; ".join(missing) or "Invalid target/stop geometry.")
    target_detail = "T1 and ATR-buffered stop valid; T2 available." if t2 is not None else "T1 and ATR-buffered stop valid; T2 unavailable and intentionally left unset."
    return RiskPlan(True, float(t1), float(t2) if t2 is not None else None, float(stop), stop_source, t1_source, t2_source,
                    tuple(skipped), f"Valid OI/price-action target and ATR-buffered stop geometry. {target_detail}")


def update_recommendation_tracker(
    state: dict[str, Any], spot: float, indicators: IndicatorSet,
    oi: OIAnalysis, now: datetime,
    option_quotes: Optional[Mapping[str, LiveQuote]] = None,
    *, quote_alert_cooldown_minutes: int = 10,
) -> dict[str, Any]:
    """Monitor every active virtual recommendation using NIFTY levels and its live option quote.

    The tracker is explicitly hypothetical: it never represents an exchange position.
    Level events are edge-triggered so each T1/T2/stop event can create one alert only.
    """
    raw = state.get("recommendation_trackers")
    trackers = [dict(x) for x in raw if isinstance(x, dict)] if isinstance(raw, list) else []
    legacy = state.get("recommendation_tracker")
    if not trackers and isinstance(legacy, dict):
        trackers = [dict(legacy)]
    # If the singular compatibility view has newer fields, merge it into the matching entry.
    if isinstance(legacy, dict):
        legacy_fp = str(legacy.get("signal_fingerprint", ""))
        if legacy_fp:
            for item in trackers:
                if str(item.get("signal_fingerprint", "")) == legacy_fp:
                    item.update(legacy)
                    break
    quotes = option_quotes or {}
    events: list[dict[str, Any]] = []
    monitor_rows: list[dict[str, Any]] = []
    terminal = {
        "VIRTUAL_STOP_LOSS_REACHED", "VIRTUAL_TRAILING_STOP_REACHED", "VIRTUAL_T2_REACHED",
        "INVALIDATED_STATE", "VIRTUAL_SESSION_ENDED", "VIRTUAL_MONITOR_CAP_REACHED",
    }

    for tracker in trackers:
        status = str(tracker.get("status", "")).upper()
        if status != "TRACKING":
            continue
        direction = str(tracker.get("direction", "")).upper()
        instrument_key = str(tracker.get("instrument_key", ""))
        quote = quotes.get(instrument_key) if instrument_key else None
        prior_quote_status = str(tracker.get("last_option_quote_status", "UNKNOWN")).upper()
        quote_status = quote.freshness if quote is not None else "UNAVAILABLE"
        option_ltp: Optional[float] = None
        if quote is not None and finite(quote.ltp) and quote.ltp > 0:
            option_ltp = float(quote.ltp)
            tracker["last_option_ltp_observed"] = option_ltp
            tracker["last_option_quote_status"] = quote_status
            tracker["last_option_quote_timestamp"] = quote.timestamp or quote.last_trade_time
            entry_ltp = safe_float(tracker.get("entry_reference_ltp"))
            if finite(entry_ltp) and entry_ltp > 0:
                tracker["option_ltp_change_pct_from_signal"] = (option_ltp / entry_ltp - 1.0) * 100.0
        else:
            tracker["last_option_quote_status"] = quote_status
        tracker["last_nifty_spot"] = float(spot) if finite(spot) else tracker.get("last_nifty_spot")
        tracker["last_monitored_at"] = ist_iso(now)

        # Quote freshness is reported independently from index-level event monitoring.
        # A missing/stale option quote cannot create a price exit, but it must be visible.
        if quote is None or quote.freshness != "FRESH" or option_ltp is None:
            prior_warning = parse_timestamp(tracker.get("last_quote_warning_at"))
            cooldown_elapsed = prior_warning is None or (now - prior_warning).total_seconds() >= max(1, quote_alert_cooldown_minutes) * 60
            if cooldown_elapsed:
                events.append({
                    "event_type": "SELECTED_OPTION_QUOTE_UNAVAILABLE",
                    "event_at": ist_iso(now), "tracker_fingerprint": tracker.get("signal_fingerprint", ""),
                    "direction": direction, "scenario": tracker.get("scenario", ""),
                    "instrument_key": instrument_key, "trading_symbol": tracker.get("trading_symbol", ""),
                    "option_type": tracker.get("option_type", ""), "strike": tracker.get("strike"),
                    "spot": spot, "option_ltp": option_ltp, "option_quote_status": quote_status,
                    "option_quote_age_seconds": quote.age_seconds if quote is not None else None,
                    "T1": tracker.get("target_1"), "T2": tracker.get("target_2"),
                    "SL": tracker.get("stop_loss"), "trailing_SL": tracker.get("trailing_stop", tracker.get("stop_loss")),
                    "message": "The recommendation remains monitored against NIFTY index levels, but the selected option quote is not fresh/available.",
                })
                tracker["last_quote_warning_at"] = ist_iso(now)
        else:
            if prior_quote_status in {"STALE", "UNAVAILABLE", "ERROR", "MISSING"}:
                tracker["quote_recovered_at"] = ist_iso(now)
                events.append({
                    "event_type": "SELECTED_OPTION_QUOTE_RECOVERED",
                    "event_at": ist_iso(now), "tracker_fingerprint": tracker.get("signal_fingerprint", ""),
                    "direction": direction, "scenario": tracker.get("scenario", ""),
                    "instrument_key": instrument_key, "trading_symbol": tracker.get("trading_symbol", ""),
                    "option_type": tracker.get("option_type", ""), "strike": tracker.get("strike"),
                    "spot": spot, "option_ltp": option_ltp, "option_quote_status": quote_status,
                    "option_quote_age_seconds": quote.age_seconds if quote is not None else None,
                    "T1": tracker.get("target_1"), "T2": tracker.get("target_2"),
                    "SL": tracker.get("stop_loss"), "trailing_SL": tracker.get("trailing_stop", tracker.get("stop_loss")),
                    "message": "The selected option quote has become fresh again; virtual monitoring continues.",
                })

        t1 = safe_float(tracker.get("target_1"))
        t2 = safe_float(tracker.get("target_2"))
        stored_stop = safe_float(tracker.get("trailing_stop", tracker.get("stop_loss")))
        if direction not in {"BULLISH", "BEARISH"} or not finite(t1) or not finite(stored_stop):
            tracker["status"] = "INVALIDATED_STATE"
            tracker["completed_at"] = ist_iso(now)
            events.append({
                "event_type": "TRACKER_STATE_INVALIDATED", "event_at": ist_iso(now),
                "tracker_fingerprint": tracker.get("signal_fingerprint", ""),
                "direction": direction, "instrument_key": instrument_key, "trading_symbol": tracker.get("trading_symbol", ""),
                "option_type": tracker.get("option_type", ""), "strike": tracker.get("strike"), "spot": spot,
                "option_ltp": option_ltp, "option_quote_status": quote_status,
                "T1": tracker.get("target_1"), "T2": tracker.get("target_2"), "SL": tracker.get("stop_loss"),
                "trailing_SL": tracker.get("trailing_stop"),
                "message": "Persisted target/stop/direction data failed validation; this recommendation will no longer be monitored.",
            })
            continue

        was_t1_hit = bool(tracker.get("target_1_hit", False))
        spot_t1_cross = (direction == "BULLISH" and spot >= t1) or (direction == "BEARISH" and spot <= t1)
        t1_newly_hit = not was_t1_hit and spot_t1_cross
        if t1_newly_hit:
            tracker["target_1_hit"] = True
            tracker["target_1_hit_at"] = ist_iso(now)

        old_stop = stored_stop
        stop = old_stop
        trailing_changed = False
        if bool(tracker.get("target_1_hit", False)) and finite(indicators.atr) and indicators.atr > 0:
            wall_rows = oi.walls_support if direction == "BULLISH" else oi.walls_resistance
            side_walls = [w for w in wall_rows if w.state in {"BUILDING", "STABLE"}
                          and (w.strike < spot if direction == "BULLISH" else w.strike > spot)]
            if side_walls:
                wall = max(side_walls, key=lambda w: w.strike) if direction == "BULLISH" else min(side_walls, key=lambda w: w.strike)
                new_stop = wall.strike - 0.10 * indicators.atr if direction == "BULLISH" else wall.strike + 0.10 * indicators.atr
                ratcheted = max(stop, new_stop) if direction == "BULLISH" else min(stop, new_stop)
                if ((direction == "BULLISH" and ratcheted < spot and ratcheted > stop)
                        or (direction == "BEARISH" and ratcheted > spot and ratcheted < stop)):
                    stop = float(ratcheted)
                    tracker["trailing_stop"] = stop
                    tracker["trailing_stop_source"] = f"POST_T1_CURRENT_{wall.side}_WALL_MINUS_PLUS_0.10_ATR"
                    tracker["trailing_stop_updated_at"] = ist_iso(now)
                    trailing_changed = abs(stop - old_stop) >= 0.01

        common_event = {
            "event_at": ist_iso(now), "tracker_fingerprint": tracker.get("signal_fingerprint", ""),
            "direction": direction, "scenario": tracker.get("scenario", ""),
            "instrument_key": instrument_key, "trading_symbol": tracker.get("trading_symbol", ""),
            "option_type": tracker.get("option_type", ""), "strike": tracker.get("strike"),
            "spot": spot, "option_ltp": option_ltp, "option_quote_status": quote_status,
            "option_quote_age_seconds": quote.age_seconds if quote is not None else None,
            "T1": t1, "T2": t2 if finite(t2) else None,
            "SL": tracker.get("stop_loss"), "trailing_SL": stop,
            "entry_reference_ltp": tracker.get("entry_reference_ltp"),
            "option_ltp_change_pct_from_signal": tracker.get("option_ltp_change_pct_from_signal"),
        }
        if t1_newly_hit:
            events.append({**common_event, "event_type": "T1_REACHED",
                           "message": "NIFTY reached T1. The virtual trailing stop is now updated to the current intact structural OI wall where a favorable ratchet is available."})
        elif trailing_changed:
            events.append({**common_event, "event_type": "TRAILING_STOP_UPDATED",
                           "previous_trailing_SL": old_stop, "new_trailing_SL": stop,
                           "message": "NIFTY structural support/resistance changed; the virtual trailing stop moved only in the favorable direction."})

        stop_hit = (direction == "BULLISH" and spot <= stop) or (direction == "BEARISH" and spot >= stop)
        t2_hit = finite(t2) and ((direction == "BULLISH" and spot >= t2) or (direction == "BEARISH" and spot <= t2))
        if stop_hit:
            event_type = "TRAILING_STOP_REACHED" if bool(tracker.get("target_1_hit", False)) else "INITIAL_STOP_LOSS_REACHED"
            tracker["status"] = "VIRTUAL_TRAILING_STOP_REACHED" if event_type == "TRAILING_STOP_REACHED" else "VIRTUAL_STOP_LOSS_REACHED"
            tracker["completed_at"] = ist_iso(now)
            events.append({**common_event, "event_type": event_type,
                           "message": "NIFTY reached the recommendation's structural stop level. This is a virtual signal-monitor event, not an order or actual-position confirmation."})
        elif t2_hit:
            # If a scan gap jumps past T2 and the T1 event was not previously observed,
            # emit T1 before T2 so the alert history follows the proper level sequence.
            if not bool(tracker.get("target_1_hit", False)):
                tracker["target_1_hit"] = True
                tracker["target_1_hit_at"] = ist_iso(now)
                events.append({**common_event, "event_type": "T1_REACHED",
                               "message": "NIFTY crossed T1 and T2 between scans; reporting T1 before T2."})
            tracker["status"] = "VIRTUAL_T2_REACHED"
            tracker["completed_at"] = ist_iso(now)
            events.append({**common_event, "event_type": "T2_REACHED",
                           "message": "NIFTY reached T2. Virtual recommendation monitoring is complete."})

        monitor_rows.append({
            "status": tracker.get("status", "TRACKING"), "direction": direction,
            "scenario": tracker.get("scenario", ""), "instrument_key": instrument_key,
            "trading_symbol": tracker.get("trading_symbol", ""), "option_type": tracker.get("option_type", ""),
            "strike": tracker.get("strike"), "option_ltp": option_ltp,
            "option_quote_status": quote_status,
            "option_quote_age_seconds": quote.age_seconds if quote is not None else None,
            "option_ltp_change_pct_from_signal": tracker.get("option_ltp_change_pct_from_signal"),
            "last_nifty_spot": spot, "target_1_hit": bool(tracker.get("target_1_hit", False)),
            "T1": t1, "T2": t2 if finite(t2) else None, "SL": tracker.get("stop_loss"),
            "trailing_SL": tracker.get("trailing_stop", tracker.get("stop_loss")),
            "last_monitored_at": tracker.get("last_monitored_at"),
        })

    # Keep only a bounded same-session history; the latest recommendation is the legacy view.
    state["recommendation_trackers"] = trackers[-60:]
    if trackers:
        primary_fp = str(state.get("last_signal_fingerprint", ""))
        primary = next((x for x in reversed(trackers) if str(x.get("signal_fingerprint", "")) == primary_fp), trackers[-1])
        state["recommendation_tracker"] = primary
    else:
        state["recommendation_tracker"] = None
    primary = state.get("recommendation_tracker") if isinstance(state.get("recommendation_tracker"), dict) else {}
    active_count = sum(1 for x in trackers if str(x.get("status", "")).upper() == "TRACKING")
    return {
        "status": str(primary.get("status", "NONE")), "direction": primary.get("direction"),
        "target_1_hit": bool(primary.get("target_1_hit", False)),
        "target_1": primary.get("target_1"), "target_2": primary.get("target_2"),
        "trailing_stop": primary.get("trailing_stop", primary.get("stop_loss")),
        "active_tracker_count": active_count, "trackers": monitor_rows,
        "events": events,
        "message": ("Virtual recommendation(s) monitored using NIFTY index levels and the selected option's live quote. No order was placed."
                    if monitor_rows else "No active recommendation tracker."),
    }


def register_recommendation_tracker(
    state: dict[str, Any], signal: dict[str, Any], fingerprint: str, now: datetime,
    max_active_trackers: int = 5, reentry_cooldown_minutes: int = 6,
) -> dict[str, Any]:
    """Register a signal for virtual monitoring without resetting an identical tracker.

    Several distinct alerts may remain monitored independently, so a later signal does
    not silently stop the prior recommendation's T1/T2/stop alerts. The active tracker
    count is bounded; if the cap is reached, the oldest tracker is explicitly retired.
    """
    raw = state.get("recommendation_trackers")
    trackers = [dict(x) for x in raw if isinstance(x, dict)] if isinstance(raw, list) else []
    legacy = state.get("recommendation_tracker")
    if not trackers and isinstance(legacy, dict):
        trackers = [dict(legacy)]
    base_identity = str(fingerprint)
    old = next((x for x in reversed(trackers)
                if str(x.get("base_signal_fingerprint", x.get("signal_fingerprint", ""))) == base_identity
                and str(x.get("status", "")).upper() == "TRACKING"), None)
    if old is None:
        terminal_match = next((x for x in reversed(trackers)
                               if str(x.get("base_signal_fingerprint", x.get("signal_fingerprint", ""))) == base_identity
                               and str(x.get("status", "")).upper() in {"VIRTUAL_STOP_LOSS_REACHED", "VIRTUAL_TRAILING_STOP_REACHED", "VIRTUAL_T2_REACHED", "INVALIDATED_STATE", "VIRTUAL_SESSION_ENDED", "VIRTUAL_MONITOR_CAP_REACHED"}), None)
        if terminal_match is not None:
            completed_at = parse_timestamp(terminal_match.get("completed_at"))
            elapsed = (now - completed_at).total_seconds() / 60.0 if completed_at else 0.0
            if elapsed < max(1, int(reentry_cooldown_minutes)):
                primary = terminal_match
                state["recommendation_trackers"] = trackers
                state["recommendation_tracker"] = primary
                state["last_signal_fingerprint"] = str(primary.get("signal_fingerprint", fingerprint))
                state["last_signal_timestamp"] = now.isoformat()
                return {"status": primary.get("status"), "direction": primary.get("direction"),
                        "target_1": primary.get("target_1"), "target_2": primary.get("target_2"),
                        "trailing_stop": primary.get("trailing_stop", primary.get("stop_loss")),
                        "target_1_hit": bool(primary.get("target_1_hit", False)),
                        "active_tracker_count": sum(1 for x in trackers if str(x.get("status", "")).upper() == "TRACKING"),
                        "signal_fingerprint": primary.get("signal_fingerprint"),
                        "message": f"Same-contract re-entry blocked until {max(1, int(reentry_cooldown_minutes))} minutes after terminal level."}
            # Create a new signal generation only after the cooldown and a fresh current scan.
            fingerprint = hashlib.sha256(f"{fingerprint}|REENTRY|{ist_iso(now)[:16]}".encode()).hexdigest()
    old = next((x for x in trackers if str(x.get("signal_fingerprint", "")) == fingerprint), None)
    if old is not None and str(old.get("status", "")).upper() == "TRACKING":
        old["last_signal_seen_at"] = now.isoformat()
        old["latest_signal_score"] = signal.get("score")
        old["latest_signal_confidence_pct"] = signal.get("confidence_pct")
        # Preserve initial levels and progress for a repeated scan; never reset T1/SL.
        primary = old
        result_message = "Same recommendation retained; target/stop progress is not reset by repeated scans."
    else:
        tracker = {
            "status": "TRACKING", "signal_fingerprint": fingerprint,
            "base_signal_fingerprint": str(signal.get("base_signal_fingerprint", base_identity)),
            "created_at": now.isoformat(), "last_signal_seen_at": now.isoformat(),
            "session_date": str(signal.get("timestamp", now.isoformat()))[:10],
            "direction": signal["direction"], "scenario": signal.get("scenario", ""),
            "instrument_key": signal["instrument_key"], "trading_symbol": signal["trading_symbol"],
            "strike": signal["strike"], "option_type": signal["option_type"],
            "entry_reference_ltp": signal["option_ltp"],
            "last_option_ltp_observed": signal["option_ltp"],
            "last_option_quote_status": "FRESH",
            "last_nifty_spot": signal["nifty_spot"],
            "nifty_entry_reference": signal["nifty_spot"],
            "target_1": signal["T1"], "target_2": signal.get("T2"),
            "stop_loss": signal["SL"], "trailing_stop": signal["SL"],
            "target_1_hit": False, "alerted_events": [],
            "latest_signal_score": signal.get("score"),
            "latest_signal_confidence_pct": signal.get("confidence_pct"),
            "tracker_notice": "Hypothetical signal monitoring only; this is not evidence of an actual open position.",
        }
        trackers.append(tracker)
        primary = tracker
        result_message = "New recommendation tracker initialized; hypothetical signal only."

        # Bound concurrently monitored recommendations without silently dropping state.
        max_active = min(12, max(1, int(max_active_trackers)))
        while sum(1 for x in trackers if str(x.get("status", "")).upper() == "TRACKING") > max_active:
            oldest = next((x for x in trackers if str(x.get("status", "")).upper() == "TRACKING" and x is not primary), None)
            if oldest is None:
                break
            oldest["status"] = "VIRTUAL_MONITOR_CAP_REACHED"
            oldest["completed_at"] = now.isoformat()
            oldest["completion_reason"] = "Retired because the configured virtual-monitor tracker cap was reached."
            # The warning event is returned to the caller and emailed below.
            primary.setdefault("tracker_cap_retirements", []).append({
                "signal_fingerprint": oldest.get("signal_fingerprint"),
                "instrument_key": oldest.get("instrument_key"), "strike": oldest.get("strike"),
                "direction": oldest.get("direction"), "retired_at": now.isoformat(),
            })

    trackers = trackers[-60:]
    state["recommendation_trackers"] = trackers
    state["recommendation_tracker"] = primary
    state["last_signal_fingerprint"] = fingerprint
    state["last_signal_timestamp"] = now.isoformat()
    return {"status": primary.get("status", "TRACKING"), "direction": primary.get("direction"),
            "target_1": primary.get("target_1"), "target_2": primary.get("target_2"),
            "trailing_stop": primary.get("trailing_stop", primary.get("stop_loss")),
            "target_1_hit": bool(primary.get("target_1_hit", False)),
            "active_tracker_count": sum(1 for x in trackers if str(x.get("status", "")).upper() == "TRACKING"),
            "tracker_cap_retirements": list(primary.get("tracker_cap_retirements", [])),
            "signal_fingerprint": primary.get("signal_fingerprint"),
            "message": result_message}


# =============================================================================
# Stage 3 — execution readiness (separate from detection and ranking)
# =============================================================================

def evaluate_trade_readiness(
    now: datetime, scenario: Scenario, indicators: IndicatorSet, oi: OIAnalysis,
    risk: RiskPlan, index_quote: LiveQuote, future_regime: str,
    candidate: Optional[OptionContract], config: Config,
) -> dict[str, Any]:
    """Apply readiness rules without erasing a previously detected setup."""
    blockers: list[str] = []
    if scenario.hard_veto:
        blockers.append(scenario.hard_veto)
    if index_quote.freshness != "FRESH":
        blockers.append("NIFTY_QUOTE_NOT_FRESH")
    if not finite(indicators.adx):
        blockers.append("ADX_UNAVAILABLE_NO_DIRECTIONAL_ENTRY")
    local_time = now.astimezone(IST).time() if now.tzinfo else now.replace(tzinfo=IST).time()
    if local_time < ENTRY_START:
        blockers.append("BASELINE_ONLY_BEFORE_09_16")
    if local_time >= ENTRY_CUTOFF:
        blockers.append("NEW_ENTRY_CUTOFF_15_15_MONITOR_ONLY")
    if scenario.direction in {"BULLISH", "BEARISH"}:
        opposing = "STRONG_SHORT_BUILDUP" if scenario.direction == "BULLISH" else "STRONG_LONG_BUILDUP"
        if future_regime == opposing:
            blockers.append(f"FUTURES_CONFLICT_{future_regime}")
    if not risk.valid:
        blockers.append(f"STRUCTURAL_RISK_PLAN_INVALID:{risk.reason}")
    if scenario.direction not in {"BULLISH", "BEARISH"} or not scenario.executable_candidate:
        blockers.append("NO_DIRECTIONAL_EXECUTABLE_SETUP")
    if candidate is None:
        blockers.append("NO_CANDIDATE_WITH_A_LIVE_QUOTE")
        if not oi.tactical_available:
            blockers.append("TACTICAL_COI_BASELINE_UNAVAILABLE_NO_COLD_START_VELOCITY_CLAIM")
    else:
        blockers.extend(candidate.vetoes)
    blockers = list(dict.fromkeys(blockers))
    ready = not blockers and candidate is not None
    return {
        "status": "READY" if ready else "BLOCKED",
        "ready": ready,
        "blocking_reasons": blockers,
        "hard_safety_gates": [
            "fresh index quote", "API/data integrity", "NSE entry cutoff",
            "strict sideways/pinning veto", "valid T1 and structural stop",
        ],
        "strategy_filters": [
            "ADX regime availability", "tactical COI for executable scoring",
            "non-conflicting futures regime", "fresh option quote", "bid/ask spread threshold",
            "premium above its own 1-minute VWAP", "minimum delta", "full 40/30/30 score threshold",
        ],
        "strategy_thresholds": {
            "min_score": config.min_score, "default_min_score": 0.650,
            "max_spread_ratio": config.max_spread_ratio,
            "minimum_delta": config.min_exhaustion_delta if "EXHAUSTION" in scenario.state else config.min_directional_delta,
            "target_2_required": False,
        },
    }


def candidate_report(candidate: Optional[OptionContract]) -> Optional[dict[str, Any]]:
    """Return a reviewable candidate record; this does not imply execution readiness."""
    if candidate is None:
        return None
    return {
        "instrument_key": candidate.instrument_key, "trading_symbol": candidate.trading_symbol,
        "option_type": candidate.option_type, "strike": candidate.strike, "expiry": candidate.expiry,
        "ltp": candidate.ltp, "delta": candidate.delta, "delta_source": candidate.delta_source,
        "premium_vwap": candidate.premium_vwap, "score": candidate.total_score,
        "score_basis": candidate.score_basis,
        "score_components_available": list(candidate.score_components_available),
        "flow_score": candidate.flow_score, "vwap_lift_score": candidate.vwap_lift_score,
        "coi_score": candidate.coi_score, "spread_ratio": candidate.spread_ratio,
        "quote_freshness": candidate.quote_freshness, "quote_age_seconds": candidate.quote_age_seconds,
        "execution_eligible": not candidate.vetoes, "blocking_reasons": list(candidate.vetoes),
    }


# =============================================================================
# Main orchestration and reporting
# =============================================================================

# =============================================================================
# Durable email outbox and alert deduplication
# =============================================================================

def email_is_configured(config: Config) -> bool:
    return bool(config.email_sender and config.email_password and config.email_receiver and config.smtp_host and config.smtp_port > 0)


def _bounded_mapping(mapping: dict[str, Any], limit: int = 600) -> dict[str, Any]:
    if len(mapping) <= limit:
        return mapping
    ordered = sorted(mapping.items(), key=lambda item: str((item[1] or {}).get("last_at", "") if isinstance(item[1], dict) else item[1]))
    return dict(ordered[-limit:])


def enqueue_email_alert(
    state: dict[str, Any], *, now: datetime, event_type: str, dedupe_key: str,
    subject: str, payload: Mapping[str, Any], cooldown_minutes: Optional[int] = None,
) -> Optional[dict[str, Any]]:
    """Place an email notification in a durable outbox; network sending happens later.

    One-time events are deduplicated for the current state lifetime. Repeating watches and
    quote-health notices may be reissued only after their configured cooldown.
    """
    dedupe = state.setdefault("alert_dedupe", {})
    if not isinstance(dedupe, dict):
        dedupe = {}
        state["alert_dedupe"] = dedupe
    prior = dedupe.get(dedupe_key)
    prior_ts = parse_timestamp(prior.get("last_at")) if isinstance(prior, dict) else parse_timestamp(prior)
    if prior_ts is not None:
        if cooldown_minutes is None:
            return None
        if (now - prior_ts).total_seconds() < max(1, cooldown_minutes) * 60:
            return None
    serial_payload = json_safe(dict(payload))
    event_seed = f"{dedupe_key}|{ist_iso(now)}"
    event_id = hashlib.sha256(event_seed.encode("utf-8")).hexdigest()
    alert = {
        "event_id": event_id, "event_type": event_type, "subject": str(subject)[:240],
        "created_at": ist_iso(now), "dedupe_key": dedupe_key,
        "payload": serial_payload, "status": "PENDING", "attempts": 0,
        "last_error": "",
    }
    outbox = state.setdefault("alert_outbox", [])
    if not isinstance(outbox, list):
        outbox = []
        state["alert_outbox"] = outbox
    if not any(isinstance(item, dict) and item.get("event_id") == event_id for item in outbox):
        outbox.append(alert)
    dedupe[dedupe_key] = {"last_at": ist_iso(now), "event_id": event_id, "event_type": event_type}
    state["alert_dedupe"] = _bounded_mapping(dedupe, 600)
    # Keep pending alerts intact, while bounding delivery history/state-file growth.
    sent = [x for x in outbox if isinstance(x, dict) and str(x.get("status", "")).upper() == "SENT"]
    pending = [x for x in outbox if isinstance(x, dict) and str(x.get("status", "PENDING")).upper() != "SENT"]
    state["alert_outbox"] = (pending[-300:] + sent[-100:])[-400:]
    return alert


def _alert_body(alert: Mapping[str, Any]) -> str:
    payload = alert.get("payload", {})
    event_type = str(alert.get("event_type", "SCANNER_ALERT"))
    created = str(alert.get("created_at", ""))
    lines = [
        f"NIFTY Predictive Scanner V59 — {event_type}",
        f"Timestamp (IST): {created}",
        "",
        "IMPORTANT: This is a scanner recommendation/monitoring alert only. No order was placed and no actual position is inferred.",
        "",
        "Event details:",
        json.dumps(json_safe(payload), indent=2, ensure_ascii=False, allow_nan=False),
        "",
        "Scanner version: " + SCANNER_VERSION,
    ]
    return "\n".join(lines)


def _schedule_email_retry(alert: dict[str, Any], now: datetime) -> None:
    """Apply bounded exponential retry delay to a persistently queued email."""
    attempts = max(1, int(safe_float(alert.get("attempts"), 1)))
    delay_seconds = min(300, 15 * (2 ** min(attempts - 1, 5)))
    alert["next_attempt_at"] = ist_iso(now + timedelta(seconds=delay_seconds))


def deliver_email_outbox(state: dict[str, Any], config: Config, now: datetime, *, max_messages: int = 12) -> dict[str, Any]:
    """Attempt queued messages with retry-on-next-run semantics and clear delivery status."""
    outbox = state.get("alert_outbox")
    if not isinstance(outbox, list):
        state["alert_outbox"] = []
        outbox = state["alert_outbox"]
    all_pending = [x for x in outbox if isinstance(x, dict) and str(x.get("status", "PENDING")).upper() == "PENDING"]
    if not all_pending:
        return {"status": "IDLE", "attempted": 0, "sent": 0, "pending": 0, "smtp_configured": email_is_configured(config)}
    if not email_is_configured(config):
        LOGGER.warning("EMAIL OUTBOX has %d pending alert(s), but EMAIL_SENDER / EMAIL_PASSWORD / EMAIL_RECEIVER are not fully configured; alerts remain queued.", len(all_pending))
        return {"status": "NOT_CONFIGURED", "attempted": 0, "sent": 0,
                "pending": len(all_pending), "smtp_configured": False}
    due: list[dict[str, Any]] = []
    for alert in all_pending:
        retry_at = parse_timestamp(alert.get("next_attempt_at"))
        if retry_at is None or retry_at <= now:
            due.append(alert)
    pending = due[:max(1, max_messages)]
    if not pending:
        return {"status": "RETRY_QUEUED", "attempted": 0, "sent": 0,
                "pending": len(all_pending), "smtp_configured": True,
                "next_attempt_at": min((str(x.get("next_attempt_at", "")) for x in all_pending if x.get("next_attempt_at")), default=None)}

    sent_count = 0
    attempted = 0
    connection = None
    try:
        if int(config.smtp_port) == 465:
            connection = smtplib.SMTP_SSL(config.smtp_host, config.smtp_port, timeout=15, context=ssl.create_default_context())
        else:
            connection = smtplib.SMTP(config.smtp_host, config.smtp_port, timeout=15)
            connection.ehlo()
            connection.starttls(context=ssl.create_default_context())
            connection.ehlo()
        connection.login(config.email_sender, config.email_password)
        for alert in pending:
            attempted += 1
            alert["attempts"] = int(alert.get("attempts", 0)) + 1
            try:
                message = MIMEMultipart("alternative")
                message["Subject"] = str(alert.get("subject", "NIFTY V59 scanner alert"))
                message["From"] = config.email_sender
                message["To"] = config.email_receiver
                message.attach(MIMEText(_alert_body(alert), "plain", "utf-8"))
                refused = connection.sendmail(config.email_sender, [config.email_receiver], message.as_string())
                if refused:
                    raise smtplib.SMTPRecipientsRefused(refused)
                alert["status"] = "SENT"
                alert["sent_at"] = ist_iso(now)
                alert["last_error"] = ""
                alert.pop("next_attempt_at", None)
                sent_count += 1
                LOGGER.info("EMAIL SENT: event=%s id=%s", alert.get("event_type"), str(alert.get("event_id", ""))[:12])
            except (OSError, smtplib.SMTPException, ValueError) as exc:
                alert["last_error"] = str(exc)[:800]
                _schedule_email_retry(alert, now)
                LOGGER.error("EMAIL DELIVERY FAILED: event=%s error=%s; retained for retry at %s.", alert.get("event_type"), exc, alert.get("next_attempt_at"))
                # A per-message SMTP failure can leave the connection in an uncertain state.
                break
    except (OSError, smtplib.SMTPException, ssl.SSLError) as exc:
        for alert in pending:
            alert["attempts"] = int(alert.get("attempts", 0)) + 1
            alert["last_error"] = str(exc)[:800]
            _schedule_email_retry(alert, now)
        LOGGER.error("SMTP CONNECTION/AUTHENTICATION FAILURE; queued alerts retained for backoff retry: %s", exc)
    finally:
        if connection is not None:
            try:
                connection.quit()
            except (OSError, smtplib.SMTPException):
                pass
    # Trim only already-sent history; pending records are retained for subsequent runs.
    outbox = state.get("alert_outbox", [])
    sent = [x for x in outbox if isinstance(x, dict) and str(x.get("status", "")).upper() == "SENT"]
    pending_all = [x for x in outbox if isinstance(x, dict) and str(x.get("status", "PENDING")).upper() != "SENT"]
    state["alert_outbox"] = pending_all[-300:] + sent[-100:]
    pending_count = sum(1 for x in state["alert_outbox"] if isinstance(x, dict) and str(x.get("status", "")).upper() == "PENDING")
    status = "SENT" if sent_count and not pending_count else "PARTIAL" if sent_count else "RETRY_QUEUED"
    next_attempt = min((str(x.get("next_attempt_at", "")) for x in state["alert_outbox"]
                        if isinstance(x, dict) and str(x.get("status", "")).upper() == "PENDING" and x.get("next_attempt_at")), default=None)
    return {"status": status, "attempted": attempted, "sent": sent_count, "pending": pending_count,
            "smtp_configured": True, "next_attempt_at": next_attempt}


class PredictiveScanner:
    def __init__(self, config: Config, client: Optional[UpstoxClient] = None,
                 store: Optional[StateStore] = None) -> None:
        self.config = config
        self.client = client or UpstoxClient(config)
        self.store = store or StateStore(config.state_file)

    def _get_quotes_or_empty(self, keys: Sequence[str]) -> dict[str, LiveQuote]:
        try:
            return self.client.quotes(keys)
        except ScannerError as exc:
            LOGGER.warning("QUOTE BATCH FAILURE: %s", exc)
            return {}

    def _queue_monitor_events(self, state: dict[str, Any], events: Sequence[Mapping[str, Any]], now: datetime) -> None:
        """Queue deduplicated monitoring/level events for email delivery."""
        for raw_event in events:
            event = dict(raw_event)
            event_type = str(event.get("event_type", "MONITOR_EVENT")).upper()
            tracker_id = str(event.get("tracker_fingerprint", "NO_TRACKER"))
            if event_type == "TRAILING_STOP_UPDATED":
                identity = f"{tracker_id}|{event_type}|{safe_float(event.get('new_trailing_SL'), -1.0):.1f}"
                cooldown = None
            elif event_type in {"SELECTED_OPTION_QUOTE_UNAVAILABLE", "SELECTED_OPTION_QUOTE_RECOVERED"}:
                identity = f"{tracker_id}|{event_type}"
                cooldown = self.config.monitor_quote_alert_cooldown_minutes if event_type == "SELECTED_OPTION_QUOTE_UNAVAILABLE" else None
            else:
                identity = f"{tracker_id}|{event_type}"
                cooldown = None
            strike = safe_float(event.get("strike"), 0.0)
            direction = str(event.get("direction", "")).upper()
            subject_suffix = f" {direction} {safe_float(event.get('strike'), 0.0):.0f}" if strike else f" {direction}" if direction else ""
            enqueue_email_alert(
                state, now=now, event_type=event_type,
                dedupe_key=f"{now.astimezone(IST).date().isoformat()}|{identity}",
                subject=f"NIFTY V59 {event_type.replace('_', ' ')}{subject_suffix}",
                payload=event, cooldown_minutes=cooldown,
            )

    def _finish(self, state: dict[str, Any], report: dict[str, Any], now: datetime) -> dict[str, Any]:
        """Persist queued alerts before delivery, then persist delivery/attempt status."""
        try:
            self.store.save()
        except Exception as exc:
            LOGGER.error("STATE PERSISTENCE FAILURE before email delivery: %s", exc)
            report["state_persistence"] = {"status": "FAILED", "error": str(exc)}
            report["email_delivery"] = {"status": "NOT_ATTEMPTED_STATE_SAVE_FAILED", "sent": 0, "pending": None}
            return json_safe(report)
        delivery = deliver_email_outbox(state, self.config, now)
        state["last_email_delivery_summary"] = {
            "timestamp": ist_iso(now), "status": delivery.get("status"),
            "attempted": delivery.get("attempted", 0), "sent": delivery.get("sent", 0),
            "pending": delivery.get("pending", 0), "smtp_configured": delivery.get("smtp_configured", False),
        }
        try:
            self.store.save()
            report["state_persistence"] = {"status": "SAVED", "path": str(self.config.state_file)}
        except Exception as exc:
            LOGGER.error("STATE PERSISTENCE FAILURE after email delivery: %s", exc)
            report["state_persistence"] = {"status": "FAILED_AFTER_DELIVERY", "error": str(exc)}
        report["email_delivery"] = delivery
        if delivery.get("status") == "NOT_CONFIGURED":
            report.setdefault("warnings", []).append("Email secrets are incomplete; notifications remain queued in state for retry.")
        elif delivery.get("status") == "RETRY_QUEUED":
            report.setdefault("warnings", []).append("One or more emails could not be sent; they remain queued for retry on the next scan.")
        return json_safe(report)

    def _queue_scan_error(self, state: dict[str, Any], now: datetime, exc: Exception, error_kind: str) -> None:
        enqueue_email_alert(
            state, now=now, event_type=error_kind,
            dedupe_key=f"{now.astimezone(IST).date().isoformat()}|{error_kind}|{type(exc).__name__}",
            subject=f"NIFTY V59 scanner {error_kind.replace('_', ' ').lower()}",
            payload={"timestamp": ist_iso(now), "scanner_version": SCANNER_VERSION,
                     "error_type": type(exc).__name__, "error": str(exc)[:1200],
                     "note": "No new recommendation was produced by the failed scan."},
            cooldown_minutes=15,
        )

    def scan_once(self, now: Optional[datetime] = None, *, skip_market_status: bool = False) -> dict[str, Any]:
        current = now or now_ist()
        if current.tzinfo is None:
            current = current.replace(tzinfo=IST)
        current = current.astimezone(IST)
        state = self.store.load(current.date())
        report: dict[str, Any] = {
            "scanner_version": SCANNER_VERSION,
            "timestamp": current.isoformat(),
            "market_state": "NO_TRADE",
            "scenario": "UNINITIALIZED",
            "direction": "NEUTRAL",
            "confidence_pct": 0.0,
            "trigger_rationale": "",
            "selected_option": None,
            "nifty_levels": {"spot": None, "T1": None, "T2": None, "SL": None, "trailing_SL": None},
            "indicators": {}, "oi": {}, "futures": {}, "risk": {}, "candidate_diagnostics": [],
            "predictive_detection": {"detected": False, "stage": "NOT_RUN"},
            "candidate_ranking": {"best_candidate": None, "ranking_basis": "NOT_RUN"},
            "trade_readiness": {"status": "NOT_EVALUATED", "blocking_reasons": []},
            "vetoes": [], "state_file": str(self.config.state_file),
            "execution_mode": "SIGNAL_ONLY_NO_ORDER_PLACEMENT",
            "signal_ready": False,
        }
        # Explicitly end virtual monitoring after the NSE regular session instead of carrying
        # yesterday's levels into a new date without telling the user.
        if current.weekday() < 5 and current.time() >= MARKET_END:
            trackers = state.get("recommendation_trackers")
            if not isinstance(trackers, list):
                legacy_tracker = state.get("recommendation_tracker")
                trackers = [legacy_tracker] if isinstance(legacy_tracker, dict) else []
            for tracker in trackers:
                if not isinstance(tracker, dict) or str(tracker.get("status", "")).upper() != "TRACKING":
                    continue
                tracker["status"] = "VIRTUAL_SESSION_ENDED"
                tracker["completed_at"] = ist_iso(current)
                tracker["completion_reason"] = "Regular NSE session ended; no overnight signal-level monitoring is performed."
                event = {
                    "event_type": "VIRTUAL_SESSION_ENDED", "event_at": ist_iso(current),
                    "tracker_fingerprint": tracker.get("signal_fingerprint", ""),
                    "direction": tracker.get("direction"), "scenario": tracker.get("scenario"),
                    "instrument_key": tracker.get("instrument_key"), "trading_symbol": tracker.get("trading_symbol"),
                    "option_type": tracker.get("option_type"), "strike": tracker.get("strike"),
                    "spot": tracker.get("last_nifty_spot"), "option_ltp": tracker.get("last_option_ltp_observed"),
                    "option_quote_status": tracker.get("last_option_quote_status", "LAST_OBSERVED"),
                    "T1": tracker.get("target_1"), "T2": tracker.get("target_2"),
                    "SL": tracker.get("stop_loss"), "trailing_SL": tracker.get("trailing_stop", tracker.get("stop_loss")),
                    "target_1_hit": tracker.get("target_1_hit", False),
                    "message": "The regular session has ended. This virtual recommendation is no longer actively monitored; levels are not carried forward overnight.",
                }
                self._queue_monitor_events(state, [event], current)
            if isinstance(state.get("recommendation_trackers"), list):
                state["recommendation_trackers"] = trackers[-60:]
                primary = state.get("recommendation_tracker")
                if isinstance(primary, dict):
                    for item in trackers:
                        if item.get("signal_fingerprint") == primary.get("signal_fingerprint"):
                            state["recommendation_tracker"] = item
                            break
            report["scenario"] = "SESSION_MONITOR_CLOSED"
            report["market_state"] = "MONITORING_ENDED"
            report["trigger_rationale"] = "NSE regular session ended; active virtual trackers were finalized and overnight monitoring is disabled."
            state["last_scan_timestamp"] = current.isoformat()
            return self._finish(state, report, current)

        allowed, time_reason = market_time_allowed(current)
        if not allowed:
            report["trigger_rationale"] = time_reason
            report["vetoes"] = [time_reason]
            return self._finish(state, report, current)
        if not skip_market_status:
            try:
                status = self.client.market_status()
                report["market_status"] = status
                if status != "OPEN":
                    report["trigger_rationale"] = f"NSE market status is {status}; live entries suppressed."
                    report["vetoes"] = ["NSE_MARKET_NOT_NORMAL_OPEN"]
                    return self._finish(state, report, current)
            except ScannerError as exc:
                report["market_status"] = "UNVERIFIED"
                report["trigger_rationale"] = f"Market-status API unavailable; fail-closed: {exc}"
                report["vetoes"] = ["MARKET_STATUS_UNVERIFIED"]
                self._queue_scan_error(state, current, exc, "MARKET_STATUS_API_ERROR")
                return self._finish(state, report, current)

        try:
            # Fetch index quote first: it is the true spot source and is required to choose ATM.
            index_quotes = self.client.quotes([self.config.nifty_key])
            index_quote = index_quotes.get(self.config.nifty_key)
            if index_quote is None or not finite(index_quote.ltp) or index_quote.ltp <= 0:
                raise ScannerError("Fresh NIFTY index quote unavailable.")
            spot = index_quote.ltp
            report["nifty_levels"]["spot"] = spot
            if index_quote.freshness != "FRESH":
                raise ScannerError(f"NIFTY index quote is {index_quote.freshness}; entry triggers suppressed.")

            expiry = self.client.option_expiry(state, current.date())
            chain = self.client.option_chain(expiry)
            chain_map = chain_rows_by_strike(chain)
            strikes = sorted(chain_map)
            atm = nearest_strike(spot, strikes)
            step = infer_strike_step(strikes)
            # A 09:15 warm-up pass only fetches index/chain and persists an authentic OI
            # snapshot. It deliberately does not require a first 1m candle to have formed.
            # This gives the scheduled 09:16 scan a true elapsed-time COI baseline.
            if current.time() < ENTRY_START:
                prior = self.store.recent_chain_snapshots(current)
                warm_oi = analyze_option_oi(chain, prior, current, spot, self.config,
                                            session_baseline=state.get("session_oi_baseline"),
                                            session_baseline_source=str(state.get("session_oi_baseline_source", "UNAVAILABLE")))
                warm_snapshot = make_chain_snapshot(chain, warm_oi, current, expiry)
                self.store.append_chain_snapshot(warm_snapshot, current)
                if not isinstance(state.get("session_oi_baseline"), dict):
                    state["session_oi_baseline"] = warm_snapshot
                    state["session_oi_baseline_source"] = "MARKET_OPEN_09_15"
                report.update({
                    "scenario": "PREOPENING_BASELINE_WARMUP",
                    "market_state": "BASELINE_WARMUP",
                    "direction": "NEUTRAL",
                    "confidence_pct": 0.0,
                    "trigger_rationale": "09:15 OI baseline stored for the first tactical COI comparison. No entry is eligible before 09:16 IST.",
                    "oi": {"expiry": expiry, "atm": atm, "strike_step": step,
                           "call_total_oi": warm_oi.call_total, "put_total_oi": warm_oi.put_total,
                           "pcr": warm_oi.pcr, "tactical_available": warm_oi.tactical_available,
                           "baseline_quality": warm_oi.baseline_quality,
                           "session_baseline_source": state.get("session_oi_baseline_source", "UNAVAILABLE")},
                    "vetoes": ["BASELINE_ONLY_BEFORE_09_16"],
                    "signal_ready": False,
                })
                state["last_scan_timestamp"] = current.isoformat()
                return self._finish(state, report, current)
            # Always analyze the full returned chain for PCR / walls; the execution universe is constrained later.
            future = self.client.nearest_future(state, current.date())
            future_key = future["instrument_key"] if future else ""
            all_keys = [self.config.nifty_key] + ([future_key] if future_key else [])
            # Persisted recommendation trackers may have a strike outside the current ATM window.
            # Include those instruments in this same quote batch so monitoring never relies on chain LTP.
            active_trackers = state.get("recommendation_trackers")
            if isinstance(active_trackers, list):
                all_keys.extend(str(item.get("instrument_key", "")) for item in active_trackers
                                if isinstance(item, dict) and str(item.get("status", "")).upper() == "TRACKING")
            elif isinstance(state.get("recommendation_tracker"), dict):
                old_tracker = state["recommendation_tracker"]
                if str(old_tracker.get("status", "")).upper() == "TRACKING":
                    all_keys.append(str(old_tracker.get("instrument_key", "")))
            for s in (atm, atm - step, atm - 2 * step, atm + step, atm + 2 * step):
                row = chain_map.get(round(s, 2))
                if not row:
                    continue
                for typ in ("CE", "PE"):
                    key = parse_option_side(row, typ)["instrument_key"]
                    if key:
                        all_keys.append(key)
            quote_map = self._get_quotes_or_empty(all_keys)
            # Keep initial index quote if bulk quote batch omitted it.
            quote_map.setdefault(self.config.nifty_key, index_quote)
            index_quote = quote_map[self.config.nifty_key]
            futures_quote = quote_map.get(future_key) if future_key else None

            index_session = self.client.candles(self.config.nifty_key, interval=1, historical=False)
            if index_session.empty:
                raise ScannerError("NIFTY 1-minute intraday candles unavailable.")
            futures_session = pd.DataFrame()
            if future_key:
                try:
                    futures_session = self.client.candles(future_key, interval=1, historical=False)
                except ScannerError as exc:
                    LOGGER.warning("FUTURES 1m candles unavailable; price regime uses live quote snapshots only: %s", exc)
            historical_seed = load_historical_seed(self.client, state, self.config.nifty_key, current)
            indicators = build_indicators(current, spot, index_session, futures_session, historical_seed,
                                          self.config, previous_close=index_quote.previous_close)
            # Use live NIFTY price as spot; candles calculate the indicators only.
            indicators = IndicatorSet(**{**asdict(indicators), "spot": spot})

            prior_snapshots = self.store.recent_chain_snapshots(current)
            oi = analyze_option_oi(chain, prior_snapshots, current, spot, self.config,
                                   session_baseline=state.get("session_oi_baseline"),
                                   session_baseline_source=str(state.get("session_oi_baseline_source", "UNAVAILABLE")))
            future_regime, future_detail = futures_regime_from_snapshots(futures_quote, state, current)
            scenario = detect_scenario(current, indicators, oi, future_regime, self.config)
            # Fetch 1-minute option candles only for the direction and strikes that can be ranked.
            # The prior design fetched both CE and PE candles at every strike (up to ten requests per scan).
            option_candles: dict[str, pd.DataFrame] = {}
            if scenario.direction in {"BULLISH", "BEARISH"}:
                _, permitted_candles = allowed_strikes(spot, strikes, scenario.direction, current, scenario, indicators)
                option_side = "CE" if scenario.direction == "BULLISH" else "PE"
                for strike_value, _moneyness in permitted_candles:
                    option_row = chain_map.get(round(strike_value, 2))
                    if not isinstance(option_row, dict):
                        continue
                    option_key = parse_option_side(option_row, option_side)["instrument_key"]
                    if not option_key:
                        continue
                    try:
                        option_candles[option_key] = self.client.candles(option_key, interval=1, historical=False)
                    except ScannerError as exc:
                        option_candles[option_key] = pd.DataFrame()
                        LOGGER.warning("OPTION 1m candle unavailable key=%s: %s", option_key, exc)
            risk = route_targets_and_stop(scenario, spot, indicators, oi, self.config) if scenario.direction in {"BULLISH", "BEARISH"} else RiskPlan(False, None, None, None, "", "", "", (), "No directional scenario.")
            # Monitor earlier recommendations every scan using current index levels and batched live option quotes.
            tracked = update_recommendation_tracker(
                state, spot, indicators, oi, current, quote_map,
                quote_alert_cooldown_minutes=self.config.monitor_quote_alert_cooldown_minutes,
            )
            self._queue_monitor_events(state, tracked.get("events", []), current)

            report.update({
                "scenario": scenario.state,
                "market_state": scenario.state if scenario.direction != "NEUTRAL" else "SIDEWAYS" if scenario.state.startswith("SIDEWAYS") else "WATCH",
                "direction": scenario.direction,
                "confidence_pct": round(scenario.confidence, 1),
                "trigger_rationale": scenario.trigger_reason,
                "future_contract": future,
                "futures": {"quote_freshness": futures_quote.freshness if futures_quote else "UNAVAILABLE",
                            "quote_age_seconds": futures_quote.age_seconds if futures_quote else None,
                            "regime": future_regime, **future_detail},
                "indicators": {
                    "spot": spot, "vwap": indicators.vwap, "vwap_slope": indicators.vwap_slope,
                    "stddev": indicators.stddev, "upper_1sd": indicators.upper_1sd,
                    "lower_1sd": indicators.lower_1sd, "upper_2sd": indicators.upper_2sd,
                    "lower_2sd": indicators.lower_2sd, "atr_1m": indicators.atr,
                    "adx": indicators.adx, "plus_di": indicators.plus_di, "minus_di": indicators.minus_di,
                    "rsi": indicators.rsi, "momentum_3m_pct": indicators.momentum_3m_pct,
                    "compressed": indicators.compressed, "recent_range": indicators.recent_range,
                    "prior_range": indicators.prior_range, "swing_low_1m": indicators.swing_low,
                    "swing_high_1m": indicators.swing_high, "vwap_volume_source": indicators.volume_source,
                    "seeded_from_history": indicators.indicators_seeded, "one_minute_bars": indicators.candles_count,
                },
                "oi": {
                    "expiry": expiry, "atm": atm, "strike_step": step,
                    "call_total_oi": oi.call_total, "put_total_oi": oi.put_total, "pcr": oi.pcr,
                    "pcr_previous": oi.pcr_previous, "pcr_spiking": oi.pcr_spiking,
                    "call_coi_tactical_pct": oi.call_coi_pct * 100.0 if finite(oi.call_coi_pct) else None,
                    "put_coi_tactical_pct": oi.put_coi_pct * 100.0 if finite(oi.put_coi_pct) else None,
                    "call_coi_session_pct": oi.session_call_coi_pct * 100.0 if finite(oi.session_call_coi_pct) else None,
                    "put_coi_session_pct": oi.session_put_coi_pct * 100.0 if finite(oi.session_put_coi_pct) else None,
                    "tactical_source": oi.tactical_source, "tactical_available": oi.tactical_available,
                    "call_coi_acceleration_pct": oi.call_coi_acceleration_pct * 100.0 if finite(oi.call_coi_acceleration_pct) else None,
                    "put_coi_acceleration_pct": oi.put_coi_acceleration_pct * 100.0 if finite(oi.put_coi_acceleration_pct) else None,
                    "acceleration_available": oi.acceleration_available,
                    "baseline_quality": oi.baseline_quality,
                    "session_baseline_source": oi.session_baseline_source,
                    "pin_strikes": oi.pin_strikes,
                    "both_sides_building": oi.both_sides_building, "reasons": oi.reasons,
                    "resistance_walls": [asdict(w) for w in oi.walls_resistance[:8]],
                    "support_walls": [asdict(w) for w in oi.walls_support[:8]],
                },
                "risk": asdict(risk),
                "recommendation_tracker": {k: v for k, v in tracked.items() if k not in {"events", "trackers"}},
                "monitoring": {
                    "active_and_recent_trackers": tracked.get("trackers", []),
                    "events_this_scan": tracked.get("events", []),
                    "note": "NIFTY structural levels are authoritative; option LTP/freshness is shown alongside them. Virtual alerts do not confirm an actual position.",
                },
                "wall_level": scenario.wall_level,
                "wall_state": scenario.wall_state,
                "scenario_features": scenario.features,
            })
            # STAGE 1 — directional market prediction is reported before any option-quality gate.
            report["predictive_detection"] = {
                "detected": scenario.direction in {"BULLISH", "BEARISH"},
                "stage": ("PREDICTIVE_SETUP" if scenario.executable_candidate else "WATCH_ONLY")
                         if scenario.direction in {"BULLISH", "BEARISH"} else "NO_DIRECTIONAL_SETUP",
                "scenario": scenario.state, "direction": scenario.direction,
                "confidence_pct": round(scenario.confidence, 1),
                "trigger_rationale": scenario.trigger_reason,
                "execution_candidate": scenario.executable_candidate,
                "features": scenario.features,
                "confidence_type": "RULE_BASED_HEURISTIC_NOT_CALIBRATED_PROBABILITY",
            }

            prior_tracker = state.get("recommendation_tracker")
            preferred_key = None
            if (isinstance(prior_tracker, dict)
                    and str(prior_tracker.get("status", "")).upper() == "TRACKING"
                    and str(prior_tracker.get("direction", "")).upper() == scenario.direction
                    and str(prior_tracker.get("created_at", ""))[:10] == current.date().isoformat()):
                preferred_key = str(prior_tracker.get("instrument_key", "")) or None
            # STAGE 2 — rank observable contracts even when execution gates fail, so a
            # blocked opportunity remains inspectable instead of being reported as no signal.
            candidate, diagnostics = select_option_contract(chain, spot, scenario, current, indicators, oi,
                                                            quote_map, option_candles, expiry, self.config,
                                                            preferred_instrument_key=preferred_key)
            report["candidate_diagnostics"] = diagnostics
            report["candidate_ranking"] = {
                "best_candidate": candidate_report(candidate),
                "ranking_basis": candidate.score_basis if candidate else "NO_QUOTED_CANDIDATE",
                "option_gate_eligible_count": sum(1 for item in diagnostics if item.get("execution_eligible")),
                "candidate_count": len(diagnostics),
                "note": "Ranking may identify a candidate even when blocked; readiness is decided separately.",
            }

            # STAGE 3 — one authoritative, testable readiness decision.
            readiness = evaluate_trade_readiness(current, scenario, indicators, oi, risk,
                                                 index_quote, future_regime, candidate, self.config)
            if candidate is not None and scenario.direction in {"BULLISH", "BEARISH"}:
                base_fingerprint = hashlib.sha256(
                    f"{current.date()}|{scenario.direction}|{candidate.instrument_key}|{candidate.strike}".encode()
                ).hexdigest()
                completed_statuses = {"VIRTUAL_STOP_LOSS_REACHED", "VIRTUAL_TRAILING_STOP_REACHED", "VIRTUAL_T2_REACHED", "INVALIDATED_STATE", "VIRTUAL_SESSION_ENDED", "VIRTUAL_MONITOR_CAP_REACHED"}
                matching_terminal = next((item for item in reversed(state.get("recommendation_trackers", []))
                    if isinstance(item, dict)
                    and str(item.get("base_signal_fingerprint", item.get("signal_fingerprint", ""))) == base_fingerprint
                    and str(item.get("status", "")).upper() in completed_statuses), None)
                if matching_terminal is not None:
                    ended = parse_timestamp(matching_terminal.get("completed_at"))
                    if ended is None or (current - ended).total_seconds() < self.config.reentry_cooldown_minutes * 60:
                        readiness["ready"] = False
                        readiness["status"] = "BLOCKED"
                        readiness["blocking_reasons"] = list(dict.fromkeys(
                            list(readiness.get("blocking_reasons", [])) + ["SAME_CONTRACT_REENTRY_COOLDOWN"]
                        ))
            report["trade_readiness"] = readiness
            hard_vetoes = list(readiness["blocking_reasons"])
            report["vetoes"] = hard_vetoes
            current_chain_snapshot = make_chain_snapshot(chain, oi, current, expiry)
            self.store.append_chain_snapshot(current_chain_snapshot, current)
            if not isinstance(state.get("session_oi_baseline"), dict):
                state["session_oi_baseline"] = current_chain_snapshot
                state["session_oi_baseline_source"] = "FIRST_OBSERVATION_AFTER_SCANNER_START_NOT_MARKET_OPEN"
            append_futures_snapshot(state, futures_quote, current)
            state["market_history"] = (state.get("market_history", []) + [{
                "timestamp": ist_iso(current), "spot": spot, "direction": scenario.direction,
                "scenario": scenario.state, "confidence_pct": scenario.confidence,
            }])[-300:]
            if candidate is not None:
                report["candidate_preview"] = {
                    **(candidate_report(candidate) or {}),
                    "timestamp": current.isoformat(), "scenario": scenario.state,
                    "direction": scenario.direction,
                    "note": "Best observable candidate only; not an executable recommendation unless trade_readiness.status=READY.",
                }
            if readiness["ready"] and candidate and risk.valid:
                signal_payload = {
                    "timestamp": current.isoformat(), "scenario": scenario.state, "direction": scenario.direction,
                    "confidence_pct": round(scenario.confidence, 1), "trigger_reason": scenario.trigger_reason,
                    "option_type": candidate.option_type, "strike": candidate.strike,
                    "trading_symbol": candidate.trading_symbol, "instrument_key": candidate.instrument_key,
                    "delta": candidate.delta, "delta_source": candidate.delta_source,
                    "option_ltp": candidate.ltp, "option_premium_vwap": candidate.premium_vwap,
                    "score": round(candidate.total_score, 4), "flow_score": round(candidate.flow_score, 4),
                    "vwap_lift_score": round(candidate.vwap_lift_score, 4), "coi_score": round(candidate.coi_score, 4),
                    "nifty_spot": spot, "T1": risk.target_1, "T2": risk.target_2,
                    "SL": risk.stop_loss, "trailing_SL": risk.stop_loss,
                    "SL_source": risk.stop_source, "T1_source": risk.target_1_source,
                    "T2_source": risk.target_2_source, "skipped_weak_walls": list(risk.skipped_weak_walls),
                    "invalidation": f"Invalidate if NIFTY crosses {risk.stop_loss:.2f} against the position or the supporting/defending OI structure flips materially; this is a signal plan, not an order.",
                    "vwap": indicators.vwap, "adx": indicators.adx, "rsi": indicators.rsi,
                    "pcr": oi.pcr, "tactical_coi_source": oi.tactical_source,
                    "call_coi_acceleration_pct": oi.call_coi_acceleration_pct * 100.0 if finite(oi.call_coi_acceleration_pct) else None,
                    "put_coi_acceleration_pct": oi.put_coi_acceleration_pct * 100.0 if finite(oi.put_coi_acceleration_pct) else None,
                    "coi_acceleration_available": oi.acceleration_available,
                }
                report["market_state"] = scenario.state
                report["selected_option"] = signal_payload
                report["nifty_levels"] = {"spot": spot, "T1": risk.target_1, "T2": risk.target_2,
                                          "SL": risk.stop_loss, "trailing_SL": risk.stop_loss}
                report["vetoes"] = []
                report["signal_ready"] = True
                fingerprint = hashlib.sha256(f"{current.date()}|{scenario.direction}|{candidate.instrument_key}|{candidate.strike}".encode()).hexdigest()
                # Preserve T1/trailing-stop progress for a repeated identical signal;
                # a genuinely changed direction/scenario/contract gets a fresh tracker.
                registration = register_recommendation_tracker(
                    state, signal_payload, fingerprint, current, self.config.max_active_trackers,
                    self.config.reentry_cooldown_minutes,
                )
                fingerprint = str(registration.get("signal_fingerprint", fingerprint))
                report["recommendation_tracker"] = registration
                for retired in registration.get("tracker_cap_retirements", []):
                    retired_fp = str(retired.get("signal_fingerprint", ""))
                    enqueue_email_alert(
                        state, now=current, event_type="TRACKER_MONITOR_CAP_REACHED",
                        dedupe_key=f"{current.date().isoformat()}|TRACKER_MONITOR_CAP_REACHED|{retired_fp}",
                        subject=f"NIFTY V59 monitor-cap retirement {retired.get('strike', '')}",
                        payload={"timestamp": current.isoformat(), "retired_tracker": retired,
                                 "message": "This older virtual recommendation is no longer monitored because the configured active tracker limit was reached."},
                    )
                report["recommendation_trackers"] = [
                    {"status": item.get("status"), "direction": item.get("direction"),
                     "scenario": item.get("scenario"), "trading_symbol": item.get("trading_symbol"),
                     "option_type": item.get("option_type"), "strike": item.get("strike"),
                     "T1": item.get("target_1"), "T2": item.get("target_2"),
                     "SL": item.get("stop_loss"), "trailing_SL": item.get("trailing_stop"),
                     "target_1_hit": item.get("target_1_hit", False),
                     "last_option_ltp_observed": item.get("last_option_ltp_observed"),
                     "last_option_quote_status": item.get("last_option_quote_status")}
                    for item in state.get("recommendation_trackers", []) if isinstance(item, dict)
                ]
                enqueue_email_alert(
                    state, now=current, event_type="SIGNAL_READY",
                    dedupe_key=f"{current.date().isoformat()}|SIGNAL_READY|{fingerprint}",
                    subject=f"NIFTY V59 SIGNAL READY {scenario.direction} {candidate.option_type} {candidate.strike:.0f}",
                    payload={**signal_payload, "alert_type": "TRADE_READY_RECOMMENDATION",
                             "execution_mode": "VIRTUAL_SIGNAL_ONLY_NO_ORDER_PLACEMENT",
                             "readiness": readiness,
                             "tracker": registration},
                )
            else:
                report["signal_ready"] = False
                if scenario.hard_veto and "SIDEWAYS" in scenario.hard_veto:
                    report["market_state"] = "SIDEWAYS"
                elif scenario.direction in {"BULLISH", "BEARISH"}:
                    report["market_state"] = "PREDICTIVE_WATCH_BLOCKED" if not scenario.executable_candidate else "DIRECTIONAL_SETUP_NOT_TRADE_READY"
                else:
                    report["market_state"] = scenario.state
                local_time = current.astimezone(IST).time()
                should_email_watch = (
                    self.config.email_watch_alerts
                    and local_time < ENTRY_CUTOFF
                    and scenario.direction in {"BULLISH", "BEARISH"}
                    and scenario.confidence >= self.config.watch_alert_min_confidence
                    and not scenario.hard_veto
                    and (scenario.executable_candidate or scenario.state.startswith("PREDICTIVE_") or candidate is not None)
                )
                if should_email_watch:
                    best = candidate_report(candidate)
                    watch_identity = f"{current.date().isoformat()}|WATCH|{scenario.direction}|{scenario.state}|{scenario.wall_level}|{candidate.instrument_key if candidate else 'NO_CANDIDATE'}"
                    watch_payload = {
                        "timestamp": current.isoformat(), "scenario": scenario.state,
                        "direction": scenario.direction, "confidence_pct": round(scenario.confidence, 1),
                        "trigger_reason": scenario.trigger_reason, "nifty_spot": spot,
                        "vwap": indicators.vwap, "adx": indicators.adx, "rsi": indicators.rsi,
                        "pcr": oi.pcr, "tactical_coi_available": oi.tactical_available,
                        "tactical_coi_source": oi.tactical_source, "wall_level": scenario.wall_level,
                        "wall_state": scenario.wall_state, "best_candidate": best,
                        "candidate_blockers": list(candidate.vetoes) if candidate else ["NO_CANDIDATE_WITH_LIVE_QUOTE"],
                        "readiness_blockers": readiness.get("blocking_reasons", []),
                        "risk_plan": asdict(risk),
                        "note": "Predictive watch only; this email is not a trade-ready recommendation and no order was placed.",
                    }
                    enqueue_email_alert(
                        state, now=current, event_type="PREDICTIVE_WATCH",
                        dedupe_key=watch_identity,
                        subject=f"NIFTY V59 PREDICTIVE WATCH {scenario.direction} {scenario.state}",
                        payload=watch_payload,
                        cooldown_minutes=self.config.watch_alert_cooldown_minutes,
                    )
            # Ensure state/outbox are durable, then send; failures remain queued for the next invocation.
            state["last_scan_timestamp"] = current.isoformat()
            return self._finish(state, report, current)
        except (ScannerError, requests.RequestException, ValueError, KeyError, TypeError, IndexError) as exc:
            LOGGER.error("SCAN FAILED CLOSED: %s", exc)
            report["scenario"] = "DATA_ERROR_NO_TRADE"
            report["market_state"] = "NO_TRADE"
            report["trigger_rationale"] = f"Data/API/integration error; no entry emitted: {exc}"
            report["vetoes"] = ["DATA_QUALITY_OR_API_FAILURE", str(exc)]
            report["signal_ready"] = False
            self._queue_scan_error(state, current, exc, "SCAN_DATA_ERROR")
            state["last_scan_timestamp"] = current.isoformat()
            return self._finish(state, report, current)
        except Exception as exc:
            LOGGER.error("UNEXPECTED SCAN FAILURE CLOSED: %s\n%s", exc, traceback.format_exc())
            report["scenario"] = "UNEXPECTED_ERROR_NO_TRADE"
            report["market_state"] = "NO_TRADE"
            report["trigger_rationale"] = f"Unexpected error; no entry emitted: {exc}"
            report["vetoes"] = ["UNEXPECTED_ERROR_NO_TRADE"]
            report["signal_ready"] = False
            self._queue_scan_error(state, current, exc, "UNEXPECTED_SCAN_ERROR")
            return self._finish(state, report, current)




def print_report(report: dict[str, Any]) -> None:
    print(json.dumps(json_safe(report), indent=2, ensure_ascii=False, allow_nan=False))


def scan_exit_code(report: Mapping[str, Any]) -> int:
    """Return a non-zero exit code for failed/unverified scans and alert delivery failures.

    A closed market or a clean no-signal scan is a successful scan. API/data errors,
    failed state persistence, or queued-but-unsent email alerts should be visible to
    GitHub Actions while its `if: always()` persistence step still records state.
    """
    scenario = str(report.get("scenario", "")).upper()
    vetoes = {str(x).upper() for x in report.get("vetoes", [])} if isinstance(report.get("vetoes"), list) else set()
    persistence = report.get("state_persistence")
    if scenario in {"DATA_ERROR_NO_TRADE", "UNEXPECTED_ERROR_NO_TRADE", "CONFIGURATION_ERROR"}:
        return 2
    if "MARKET_STATUS_UNVERIFIED" in vetoes:
        return 2
    if isinstance(persistence, dict) and str(persistence.get("status", "")).startswith("FAILED"):
        return 3
    delivery = report.get("email_delivery")
    if isinstance(delivery, dict):
        status = str(delivery.get("status", "")).upper()
        pending = int(safe_float(delivery.get("pending"), 0))
        if pending > 0 and status in {"NOT_CONFIGURED", "RETRY_QUEUED", "PARTIAL"}:
            return 4
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="NIFTY 50 Predictive Market Scanner & Strike Router V59")
    parser.add_argument("--loop", action="store_true", help="Scan approximately once per minute during market hours.")
    parser.add_argument("--interval", type=float, default=60.0, help="Loop interval seconds (minimum 15).")
    parser.add_argument("--skip-market-status", action="store_true", help="Testing only: skip Upstox NSE market-status check.")
    args = parser.parse_args(argv)
    config = Config()
    try:
        config.validate(require_token=True)
    except ScannerError as exc:
        current = now_ist()
        report = {"scanner_version": SCANNER_VERSION, "timestamp": current.isoformat(),
                  "scenario": "CONFIGURATION_ERROR", "market_state": "NO_TRADE",
                  "direction": "NEUTRAL", "confidence_pct": 0.0, "signal_ready": False,
                  "trigger_rationale": str(exc), "vetoes": ["CONFIGURATION_ERROR"],
                  "execution_mode": "SIGNAL_ONLY_NO_ORDER_PLACEMENT"}
        # Configuration failures are also written to the durable outbox. If email is
        # configured, the operator can be notified that a required secret/config is missing.
        try:
            store = StateStore(config.state_file)
            state = store.load(current.date())
            enqueue_email_alert(
                state, now=current, event_type="CONFIGURATION_ERROR",
                dedupe_key=f"{current.date().isoformat()}|CONFIGURATION_ERROR|{type(exc).__name__}",
                subject="NIFTY V59 scanner configuration error",
                payload={"timestamp": current.isoformat(), "scanner_version": SCANNER_VERSION,
                         "error_type": type(exc).__name__, "error": str(exc),
                         "note": "The scan was stopped before market analysis; no recommendation or order was produced."},
                cooldown_minutes=15,
            )
            store.save()
            delivery = deliver_email_outbox(state, config, current)
            store.save()
            report["email_delivery"] = delivery
            report["state_persistence"] = {"status": "SAVED", "path": str(config.state_file)}
        except Exception as persist_exc:
            LOGGER.error("Unable to persist configuration-error alert: %s", persist_exc)
            report["state_persistence"] = {"status": "FAILED", "error": str(persist_exc)}
        print_report(report)
        return 2
    scanner = PredictiveScanner(config)
    if not args.loop:
        report = scanner.scan_once(skip_market_status=args.skip_market_status)
        print_report(report)
        return scan_exit_code(report)
    interval = max(15.0, float(args.interval))
    LOGGER.info("V59 minute loop started; interval=%.1fs; new entries stop at 15:15 IST.", interval)
    while True:
        cycle_start = time_module.monotonic()
        report = scanner.scan_once(skip_market_status=args.skip_market_status)
        print_report(report)
        elapsed = time_module.monotonic() - cycle_start
        # Default minute loop aligns to the next minute to keep COI snapshot spacing meaningful.
        if interval == 60.0:
            sleep_for = max(2.0, 60.0 - now_ist().second - now_ist().microsecond / 1_000_000.0)
        else:
            sleep_for = max(1.0, interval - elapsed)
        time_module.sleep(sleep_for)


if __name__ == "__main__":
    raise SystemExit(main())
