"""
NIFTY 50 Predictive Options Scanner — Authoritative PA/OI Market-Structure Engine

What this version fixes:
- Uses the NIFTY INDEX as the primary market-price/VWAP/intraday structure feed.
- Uses NIFTY futures price/OI as a separate derivatives confirmation, not the price proxy.
- Uses completed 3-minute NIFTY price action for structural persistence and risk.
- Uses NIFTY futures price/OI regime as a confirmation and positioning factor.
- Uses INDEX VWAP level + VWAP slope/position.
- Uses both option-chain OI concentration and Change-in-OI to derive
  dynamic support/resistance and directional pressure.
- Separates market-state detection from trade-entry readiness.
- Detects continuous bullish/bearish states, weakening, sideways, and directional watch states; entries are limited to continuous structure.
- Uses persistent continuous-structure entries plus a separately gated, high-confirmation exhaustion reversal scalp; ordinary pullbacks cannot flip an established trend.
- Classifies Direction x Intensity (NORMAL / STRONG / EXHAUSTION / SIDEWAYS).
- Applies time-of-day gates, expiry-day OTM bans, option-premium VWAP filters,
  15-30 minute OI velocity, delta floors, moneyness weighting, and a 5% safety override.
- Forces new-entry cutoff at 15:15 IST and detects 3-candle 5-minute stagnation exits.
- Builds NIFTY T1/T2/SL directly from price action + option OI; option Greeks
  are ranking/context only and are not used to forecast target premiums.
- No order placement. The script only creates a signal, persists state,
  and sends email.
- Uses current Upstox endpoints: v2 for option chain/contracts/status/
  instrument search/change-OI/option-chain; v3 for Full Market Quotes and candle data because the
  older v2 intraday candle API is deprecated.

Run:
    python market_scanner_v27_regime_matrix.py --self-test
    python market_scanner_v27_regime_matrix.py

Environment:
    UPSTOX_ANALYTICS_TOKEN   required
    NIFTY_INSTRUMENT_KEY     optional, default NSE_INDEX|Nifty 50

Optional email:
    EMAIL_SENDER
    EMAIL_PASSWORD
    EMAIL_RECEIVER
    SMTP_HOST (default smtp.gmail.com)
    SMTP_PORT (default 465)

Optional tuning:
    STATE_FILE
"""

from __future__ import annotations

import hashlib
import html
import json
import logging
import math
import os
import smtplib
import sys
import time as time_module
import traceback
import urllib.parse
from dataclasses import asdict, dataclass, replace
from datetime import date, datetime, time
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Optional
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests

HTTP_SESSION = requests.Session()


# =============================================================================
# CONFIG
# =============================================================================

IST = ZoneInfo("Asia/Kolkata")
BASE_URL = "https://api.upstox.com"

NIFTY_KEY = os.getenv("NIFTY_INSTRUMENT_KEY", "NSE_INDEX|Nifty 50").strip()
UPSTOX_TOKEN = os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip()

EMAIL_SENDER = os.getenv("EMAIL_SENDER", "").strip()
EMAIL_PASSWORD = os.getenv("EMAIL_PASSWORD", "").strip()
EMAIL_RECEIVER = os.getenv("EMAIL_RECEIVER", "").strip()
SMTP_HOST = os.getenv("SMTP_HOST", "smtp.gmail.com").strip()
SMTP_PORT = int(os.getenv("SMTP_PORT", "465"))

REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "12"))

# Price-action regime thresholds.
REGIME_SIDEWAYS_RANGE_ATR = float(os.getenv("REGIME_SIDEWAYS_RANGE_ATR", "2.40"))
REGIME_SIDEWAYS_NET_ATR = float(os.getenv("REGIME_SIDEWAYS_NET_ATR", "0.45"))
REGIME_SIDEWAYS_VWAP_DISTANCE_ATR = float(os.getenv("REGIME_SIDEWAYS_VWAP_DISTANCE_ATR", "0.90"))
REGIME_SIDEWAYS_ALTERNATION = float(os.getenv("REGIME_SIDEWAYS_ALTERNATION", "0.35"))
MIN_ENTRY_TIME = time(9, 18)


# Market-state memory. This prevents a neutral scan from erasing the last
# decisive directional regime.
STATE_HISTORY_LIMIT = int(os.getenv("STATE_HISTORY_LIMIT", "60"))


STATE_FILE = Path(os.getenv("STATE_FILE", "state/market_state.json"))

SCANNER_VERSION = "2026-10-09-STRUCTURE-V27-REGIME-TOD-COI"
OPTION_TARGET_ENGINE_VERSION = "V27_REGIME_TOD_COI_PA_OI"

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)
NEW_ENTRY_CUTOFF = time(15, 15)
OPENING_END = time(10, 30)
MIDDAY_END = time(13, 30)

ATR_PERIOD = 14
ADX_PERIOD = int(os.getenv("ADX_PERIOD", "14"))
ADX_SIDEWAYS_THRESHOLD = float(os.getenv("ADX_SIDEWAYS_THRESHOLD", "20"))
ADX_STRONG_THRESHOLD = float(os.getenv("ADX_STRONG_THRESHOLD", "25"))
MIDDAY_MIN_ADX = float(os.getenv("MIDDAY_MIN_ADX", "23"))
MIDDAY_MIN_PERSISTENCE = int(os.getenv("MIDDAY_MIN_PERSISTENCE", "3"))
STRONG_VOLUME_MULTIPLIER = float(os.getenv("STRONG_VOLUME_MULTIPLIER", "1.20"))
OPTION_OI_MIN_AGE_MINUTES = int(os.getenv("OPTION_OI_MIN_AGE_MINUTES", "15"))
OPTION_OI_MAX_AGE_MINUTES = int(os.getenv("OPTION_OI_MAX_AGE_MINUTES", "30"))
OPTION_OI_HISTORY_KEEP_MINUTES = int(os.getenv("OPTION_OI_HISTORY_KEEP_MINUTES", "60"))
COI_STRONG_CHANGE_PCT = float(os.getenv("COI_STRONG_CHANGE_PCT", "0.01"))
STAGNATION_RANGE_PCT = float(os.getenv("STAGNATION_RANGE_PCT", "0.001"))
STAGNATION_REQUIRED_BARS = int(os.getenv("STAGNATION_REQUIRED_BARS", "3"))
OPENING_MAX_SPREAD_PCT = float(os.getenv("OPENING_MAX_SPREAD_PCT", "0.08"))

# Option-flow classification threshold.
STRUCTURE_ACTIVITY_PRICE_NOISE_PCT = float(os.getenv("STRUCTURE_ACTIVITY_PRICE_NOISE_PCT", "0.002"))
PCR_BULL_THRESHOLD = 1.10
PCR_BEAR_THRESHOLD = 0.90

# Futures price/OI is secondary context only; this threshold is never used
# to decide the primary NIFTY market direction.
FUTURES_OI_MIN_PERSISTENCE = float(os.getenv("FUTURES_OI_MIN_PERSISTENCE", "0.50"))

# PRIMARY MARKET-STRUCTURE ENGINE
# The hierarchy is intentionally explicit:
#   1) NIFTY price relative to VWAP defines the directional environment
#   2) Option OI + Change-OI define authoritative structural support/resistance
#   3) Multi-window NIFTY price movement establishes persistence
#   4) Change-OI confirms the same direction
#   5) A support/resistance break strengthens the signal but is not required
#      for an already-established continuous trend
# Futures price/OI and PCR are context only; neither can override PA/VWAP/Change-OI structure.
STRUCTURE_BREAK_BUFFER_ATR = float(os.getenv("STRUCTURE_BREAK_BUFFER_ATR", "0.08"))
STRUCTURE_HOLD_BARS = int(os.getenv("STRUCTURE_HOLD_BARS", "2"))
STRUCTURE_CHANGE_OI_CONFIRM = float(os.getenv("STRUCTURE_CHANGE_OI_CONFIRM", "0.08"))
STRUCTURE_CHANGE_OI_STRONG = float(os.getenv("STRUCTURE_CHANGE_OI_STRONG", "0.20"))
STRUCTURE_CHANGE_OI_CONFLICT = float(os.getenv("STRUCTURE_CHANGE_OI_CONFLICT", "0.35"))
# A strong opposite futures price/OI regime blocks a fresh option entry; it does
# not independently reverse the NIFTY structure.
STRUCTURE_FUTURES_CONFLICT_STRENGTH = float(os.getenv("STRUCTURE_FUTURES_CONFLICT_STRENGTH", "0.50"))
STRUCTURE_VWAP_RECLAIM_BUFFER_ATR = float(os.getenv("STRUCTURE_VWAP_RECLAIM_BUFFER_ATR", "0.05"))
# Structural levels are option-OI levels. Price swings are retained only as
# secondary context for risk/targets and are never silently substituted into
# the authoritative support/resistance decision.
# Continuous-trend classification: a small countertrend move is a pullback,
# not a regime reversal, while a material multi-bar recovery can weaken the
# directional state.

# Entry confirmation controls. One scanner pass is sufficient once the overall
# market is aligned; forcing two polls would delay fast reversal/continuation entries.
# Require the same directional regime on two distinct completed 3-minute bars.
# This suppresses one-scan opening noise and rapid CE/PE reversals.
CONTINUATION_CONFIRMATIONS_REQUIRED = int(
    os.getenv("CONTINUATION_CONFIRMATIONS_REQUIRED", "2")
)

# Active-trade protection uses 1m OHLC when available so an intrabar stop/target
# is not silently missed between the normal scanner polls.
ACTIVE_TRADE_INTRABAR_MONITOR = os.getenv(
    "ACTIVE_TRADE_INTRABAR_MONITOR", "1"
).strip().lower() not in {"0", "false", "no"}
# A 1m option stop is only allowed to close a trade when the NIFTY index itself
# has breached the structural stop. This keeps the option SL subordinate to the
# underlying market structure instead of allowing IV/theta/option noise to
# terminate a structurally-valid NIFTY trend.
ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION = os.getenv(
    "ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION", "1"
).strip().lower() not in {"0", "false", "no"}
# Number of recent 1m bars inspected on each scan. The monitor additionally
# filters these bars to the period after the trade was opened / last checked.
ACTIVE_TRADE_INTRABAR_LOOKBACK = int(
    os.getenv("ACTIVE_TRADE_INTRABAR_LOOKBACK", "15")
)
MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED = int(
    os.getenv("MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED", "2")
)

# Do not immediately re-enter the same direction after a completed trade.
# A fresh completed 3m bar is required, and the short cooldown prevents
# stop -> new strike -> stop churn when ATM moves between two strikes.
REENTRY_COOLDOWN_MINUTES = int(os.getenv("REENTRY_COOLDOWN_MINUTES", "6"))
REENTRY_REQUIRE_NEW_3M_BAR = os.getenv("REENTRY_REQUIRE_NEW_3M_BAR", "1").strip().lower() not in {"0", "false", "no"}
STRUCTURAL_STOP_CONFIRM_BARS = int(os.getenv("STRUCTURAL_STOP_CONFIRM_BARS", "1"))



# Strike health.
MAX_SPREAD_PCT = 0.12
# Theta is a ranking/risk factor for long-option selection, not a hard entry gate.
# Near expiry, theta can become very large and a rigid percentage cutoff can
# incorrectly reject every otherwise-tradable directional option.
EXPECTED_HOLDING_MINUTES = 60.0
THETA_WARNING_BURDEN = 0.10
MIN_OI = 100.0
MIN_VOLUME = 1.0

# Price-action + OI structural trade levels. These levels are authoritative;
# option Greeks are not used to manufacture T1/T2/SL prices.
PA_OI_SWING_LOOKBACK = int(os.getenv("PA_OI_SWING_LOOKBACK", "12"))
PA_OI_TARGET_MIN_STEPS = float(os.getenv("PA_OI_TARGET_MIN_STEPS", "1.0"))
PA_OI_STOP_BUFFER_STEPS = float(os.getenv("PA_OI_STOP_BUFFER_STEPS", "0.25"))
PA_OI_SECONDARY_OI_RATIO = float(os.getenv("PA_OI_SECONDARY_OI_RATIO", "0.30"))

# T1/T2/SL are no longer option-Greek-derived.
# They are authoritative NIFTY structural levels from current PA + OI.

# Trade monitoring.

# Phase-aware state thresholds. These classify market movement separately from
# entry readiness, so conflicting derivatives can mark a weakening trend
# without falsely flipping the market direction.

# URLs.
INSTRUMENT_SEARCH_URL = f"{BASE_URL}/v2/instruments/search"
OPTION_CONTRACT_URL = f"{BASE_URL}/v2/option/contract"
OPTION_CHAIN_URL = f"{BASE_URL}/v2/option/chain"
MARKET_QUOTE_URL = f"{BASE_URL}/v3/market-quote/quotes"
MARKET_STATUS_URL = f"{BASE_URL}/v2/market/status/NSE"
CHANGE_OI_URL = f"{BASE_URL}/v2/market/change-oi"
HISTORICAL_V3_URL = f"{BASE_URL}/v3/historical-candle"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
logger = logging.getLogger("nifty_scanner")


# =============================================================================
# DATA TYPES
# =============================================================================

@dataclass(frozen=True)
class FuturesContract:
    instrument_key: str
    trading_symbol: str
    expiry: str


@dataclass(frozen=True)
class OptionCandidate:
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
    spread_pct: float
    theta_burden_pct_day: float
    premium_vwap: float = float("nan")
    flow_score: float = float("nan")
    vwap_score: float = float("nan")
    oi_momentum_score: float = float("nan")
    delta_weight: float = float("nan")
    call_oi_change_pct_15m: float = float("nan")
    put_oi_change_pct_15m: float = float("nan")
    oi_velocity_baseline_minutes: float = float("nan")
    market_intensity: str = "UNKNOWN"


@dataclass(frozen=True)
class StructureResult:
    direction: str
    score: float
    confidence: float
    interpretation: str
    components: dict[str, Any]
    vwap: float
    vwap_slope: float
    futures_regime: str
    futures_bias: int
    futures_oi_strength: float
    futures_oi_persistence: float
    futures_live_oi_change: float
    intraday_bias: int
    intraday_strength: float
    intraday_score: float
    chain_predictive_bias: int
    chain_predictive_strength: float
    chain_level_bias: int
    support_strength: float
    resistance_strength: float
    support_change_strength: float
    resistance_change_strength: float
    support_1: float
    support_2: float
    resistance_1: float
    resistance_2: float
    market_phase: str
    entry_confirmed: bool
    reversal_confirmations: int
    confirmation_state: str
    pcr: float
    pcr_bias: int
    false_breakout: bool
    trap_level: float
    entry_trigger: str
    invalidation_rule: str
    reasons: list[str]


@dataclass(frozen=True)
class Signal:
    timestamp: str
    direction: str
    regime: str
    market_state: str
    bias: str
    entry_trigger: str
    invalidation_rule: str
    confidence: float
    spot: float
    futures_state: str
    option_type: str
    strike: float
    trading_symbol: str
    instrument_key: str
    entry: float
    target_1: float
    target_2: float
    stop_loss: float
    underlying_stop: float
    underlying_target_1: float
    underlying_target_2: float
    delta: float
    theta: float
    support_1: float
    support_2: float
    resistance_1: float
    resistance_2: float
    reasons: list[str]
    market_intensity: str = "NORMAL"


class ScannerError(Exception):
    """Expected scanner/API failure."""


# =============================================================================
# BASIC HELPERS
# =============================================================================

def now_ist() -> datetime:
    return datetime.now(IST)


def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        v = float(value)
        return v if math.isfinite(v) else default
    except (TypeError, ValueError):
        return default


def parse_date(raw: str) -> Optional[date]:
    try:
        return datetime.strptime(str(raw)[:10], "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return None


def market_window_open() -> bool:
    # NSE status is checked immediately afterwards and is the authoritative
    # open/closed gate. Avoid a separate holiday API call on every 5-minute run.
    now = now_ist()
    return now.weekday() < 5 and MARKET_START <= now.time() <= MARKET_END


# =============================================================================
# UPSTOX HTTP
# =============================================================================

def api_headers() -> dict[str, str]:
    if not UPSTOX_TOKEN:
        raise ScannerError(
            "UPSTOX_ANALYTICS_TOKEN is missing. Set it in the environment."
        )
    return {
        "Accept": "application/json",
        "Content-Type": "application/json",
        "Authorization": f"Bearer {UPSTOX_TOKEN}",
    }


def api_get(
    url: str,
    params: Optional[dict[str, Any]] = None,
    retries: int = 3,
) -> dict[str, Any]:
    last_error = "Unknown Upstox error."

    for attempt in range(1, retries + 1):
        try:
            response = HTTP_SESSION.get(
                url,
                params=params,
                headers=api_headers(),
                timeout=REQUEST_TIMEOUT,
            )
        except requests.RequestException as exc:
            last_error = f"Network error: {exc}"
            if attempt < retries:
                time_module.sleep(attempt)
                continue
            raise ScannerError(last_error) from exc

        if response.status_code == 200:
            try:
                payload = response.json()
            except ValueError as exc:
                raise ScannerError(
                    f"Upstox returned invalid JSON from {url}"
                ) from exc

            if not isinstance(payload, dict):
                raise ScannerError(f"Unexpected Upstox payload from {url}.")
            if str(payload.get("status", "")).lower() == "error":
                raise ScannerError(json.dumps(payload)[:2000])
            return payload

        last_error = (
            f"Upstox HTTP {response.status_code} | "
            f"{url} | {response.text[:1500]}"
        )

        transient = response.status_code in {429, 500, 502, 503, 504}
        if transient and attempt < retries:
            time_module.sleep(min(2 * attempt, 6))
            continue

        raise ScannerError(last_error)

    raise ScannerError(last_error)


# =============================================================================
# MARKET STATUS / HOLIDAYS
# =============================================================================



def get_market_status() -> str:
    payload = api_get(MARKET_STATUS_URL, retries=3)
    data = payload.get("data", {})
    if isinstance(data, dict):
        status = str(data.get("status", "")).upper()
        if status in {"NORMAL_OPEN", "OPEN"}:
            return "OPEN"
        if status in {"NORMAL_CLOSE", "CLOSED"}:
            return "CLOSED"
        return status or "UNKNOWN"

    return "UNKNOWN"


# =============================================================================
# QUOTES
# =============================================================================

def get_quote(instrument_key: str) -> dict[str, Any]:
    payload = api_get(
        MARKET_QUOTE_URL,
        {"instrument_key": instrument_key},
        retries=3,
    )
    data = payload.get("data", {})
    if not isinstance(data, dict):
        raise ScannerError("Upstox quote data is not an object.")
    if instrument_key in data:
        return data[instrument_key]
    # Full Market Quotes V3 uses a colon-delimited response key in some cases
    # (for example NSE_INDEX:NIFTY) even when the request used the pipe key.
    colon_key = instrument_key.replace("|", ":", 1)
    if colon_key in data:
        return data[colon_key]
    if len(data) == 1:
        return next(iter(data.values()))
    raise ScannerError(f"Quote not found for {instrument_key}.")


def extract_ltp(quote: dict[str, Any]) -> float:
    for key in ("last_price", "ltp", "lastPrice"):
        value = safe_float(quote.get(key), 0.0)
        if value > 0:
            return value
    raise ScannerError("LTP not present in quote.")


# =============================================================================
# INSTRUMENT DISCOVERY
# =============================================================================

def get_current_nifty_future(state: Optional[dict[str, Any]] = None) -> FuturesContract:
    # The nearest NIFTY future normally remains unchanged throughout the session.
    # Persisting it avoids two instrument-search requests on every scan.
    today = now_ist().date()
    if isinstance(state, dict):
        cached = state.get("nifty_future")
        if isinstance(cached, dict):
            expiry = parse_date(str(cached.get("expiry", "")))
            key = str(cached.get("instrument_key", "")).strip()
            symbol = str(cached.get("trading_symbol", "")).strip()
            if key and symbol and expiry and expiry >= today:
                return FuturesContract(key, symbol, expiry.isoformat())

    candidates: list[dict[str, Any]] = []

    for expiry_filter in ("current_month", "next_month"):
        payload = api_get(
            INSTRUMENT_SEARCH_URL,
            {
                "query": "NIFTY",
                "exchanges": "NSE",
                "segments": "FO",
                "instrument_types": "FUT",
                "expiry": expiry_filter,
                "page_number": 1,
                "records": 30,
            },
        )
        rows = payload.get("data", [])
        if isinstance(rows, list):
            candidates.extend(x for x in rows if isinstance(x, dict))

    today = now_ist().date()
    valid: list[dict[str, Any]] = []

    for row in candidates:
        key = str(row.get("instrument_key", "")).strip()
        symbol = str(row.get("trading_symbol", "")).strip()
        expiry = parse_date(str(row.get("expiry", "")))
        underlying = str(row.get("underlying_symbol", "")).upper()

        if (
            key
            and symbol
            and expiry
            and expiry >= today
            and ("NIFTY" in underlying or "NIFTY" in symbol.upper())
        ):
            valid.append(row)

    if not valid:
        raise ScannerError("No active NIFTY futures found.")

    valid.sort(key=lambda x: parse_date(str(x["expiry"])) or date.max)
    selected = valid[0]

    logger.info(
        "Selected NIFTY future: %s | expiry=%s | key=%s",
        selected["trading_symbol"],
        selected["expiry"],
        selected["instrument_key"],
    )

    contract = FuturesContract(
        instrument_key=str(selected["instrument_key"]),
        trading_symbol=str(selected["trading_symbol"]),
        expiry=str(selected["expiry"])[:10],
    )
    if isinstance(state, dict):
        state["nifty_future"] = asdict(contract)
    return contract


# =============================================================================
# CANDLES
# =============================================================================

def _parse_candles(candles: Any) -> pd.DataFrame:
    rows: list[dict[str, Any]] = []

    if not isinstance(candles, list):
        return pd.DataFrame()

    for row in candles:
        if not isinstance(row, (list, tuple)) or len(row) < 6:
            continue
        try:
            rows.append(
                {
                    "timestamp": row[0],
                    "open": float(row[1]),
                    "high": float(row[2]),
                    "low": float(row[3]),
                    "close": float(row[4]),
                    "volume": float(row[5]),
                    "oi": (
                        float(row[6])
                        if len(row) >= 7 and row[6] is not None
                        else np.nan
                    ),
                }
            )
        except (TypeError, ValueError):
            continue

    if not rows:
        return pd.DataFrame()

    df = pd.DataFrame(rows)
    df["timestamp"] = pd.to_datetime(
        df["timestamp"], utc=True, errors="coerce"
    )
    df = (
        df.dropna(subset=["timestamp"])
        .sort_values("timestamp")
        .drop_duplicates("timestamp")
        .reset_index(drop=True)
    )
    return df


def get_intraday_candles(
    instrument_key: str,
    interval_minutes: int,
    *,
    strict: bool = True,
) -> pd.DataFrame:
    """Fetch today's intraday candles without turning normal opening-data lag into a fatal error."""
    encoded = urllib.parse.quote(instrument_key, safe="")
    url = f"{HISTORICAL_V3_URL}/intraday/{encoded}/minutes/{interval_minutes}"

    try:
        payload = api_get(url, retries=3)
    except ScannerError:
        if strict:
            raise
        return pd.DataFrame()

    data = payload.get("data", {})
    df = _parse_candles(data.get("candles", []) if isinstance(data, dict) else [])
    if df.empty:
        if strict:
            raise ScannerError(f"No intraday {interval_minutes}m candles for {instrument_key}.")
        return pd.DataFrame()

    session_date = now_ist().date()
    local_dates = df["timestamp"].dt.tz_convert(IST).dt.date
    df = df.loc[local_dates == session_date].reset_index(drop=True)
    if df.empty and strict:
        raise ScannerError(f"No current-session {interval_minutes}m candles for {instrument_key}.")
    return df


def _resample_one_minute_to_three(df: pd.DataFrame) -> pd.DataFrame:
    """Build 3-minute bars from 1-minute data, preserving an incomplete opening bar."""
    if df is None or df.empty:
        return pd.DataFrame()
    work = df.copy().sort_values("timestamp").drop_duplicates("timestamp", keep="last")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"]).set_index("timestamp")
    for c in ("open", "high", "low", "close", "volume", "oi"):
        if c in work.columns:
            work[c] = pd.to_numeric(work[c], errors="coerce")
    agg = work.resample("3min", origin="start_day", offset="9h15min", label="left", closed="left").agg(
        open=("open", "first"), high=("high", "max"), low=("low", "min"),
        close=("close", "last"), volume=("volume", "sum"), oi=("oi", "last"),
    )
    return agg.dropna(subset=["open", "high", "low", "close"]).reset_index()


def get_current_session_3m_candles(instrument_key: str) -> pd.DataFrame:
    """Prefer native 3m data; fall back to 1m aggregation during opening/API lag."""
    native = get_intraday_candles(instrument_key, 3, strict=False)
    if not native.empty:
        logger.info("Current-session 3m candles: %d", len(native))
        return native

    one_min = get_intraday_candles(instrument_key, 1, strict=False)
    if not one_min.empty:
        rebuilt = _resample_one_minute_to_three(one_min)
        if not rebuilt.empty:
            logger.warning(
                "Native 3m futures candles unavailable; rebuilt %d 3m bars from 1m data.",
                len(rebuilt),
            )
            return rebuilt

    logger.warning("Current-session 3m/1m candles unavailable; using quote/historical fallbacks.")
    return pd.DataFrame()


def _subtract_months(d: date, months: int) -> date:
    """Subtract calendar months without exceeding the target month."""
    year = d.year
    month = d.month - months
    while month <= 0:
        month += 12
        year -= 1

    import calendar
    day = min(d.day, calendar.monthrange(year, month)[1])
    return date(year, month, day)


def get_historical_candles(
    instrument_key: str,
    interval_minutes: int,
) -> pd.DataFrame:
    encoded = urllib.parse.quote(instrument_key, safe="")
    end = now_ist().date()

    # Upstox V3 historical-candle limits:
    #   1..15 minute intervals -> max 1 calendar month/request
    #   >15 minute minute intervals -> max 1 calendar quarter/request
    # Use calendar-month subtraction instead of a fixed day count.
    if interval_minutes <= 15:
        start = _subtract_months(end, 1)
    else:
        start = _subtract_months(end, 3)

    url = (
        f"{HISTORICAL_V3_URL}/{encoded}/minutes/{interval_minutes}"
        f"/{end.isoformat()}/{start.isoformat()}"
    )

    payload = api_get(url, retries=3)
    data = payload.get("data", {})
    df = _parse_candles(data.get("candles", []) if isinstance(data, dict) else [])

    if df.empty:
        raise ScannerError(
            f"No historical {interval_minutes}m candles for {instrument_key}."
        )
    return df


def filter_completed_candles(
    df: pd.DataFrame,
    interval_minutes: int,
    now: Optional[datetime] = None,
) -> pd.DataFrame:
    """Keep only fully completed OHLC bars for the requested interval."""
    if df is None or df.empty:
        return pd.DataFrame()
    current = now or now_ist()
    work = df.copy()
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"]).sort_values("timestamp")
    local_ts = work["timestamp"].dt.tz_convert(IST)
    completed = local_ts + pd.to_timedelta(int(interval_minutes), unit="m") <= current
    return work.loc[completed].reset_index(drop=True)


# =============================================================================
# INDICATORS
# =============================================================================

def calculate_atr(df: pd.DataFrame, period: int = ATR_PERIOD) -> pd.Series:
    previous = df["close"].shift(1)
    tr = pd.concat(
        [
            df["high"] - df["low"],
            (df["high"] - previous).abs(),
            (df["low"] - previous).abs(),
        ],
        axis=1,
    ).max(axis=1)

    return tr.ewm(
        alpha=1 / period,
        adjust=False,
        min_periods=1,
    ).mean()


def calculate_vwap(df: pd.DataFrame) -> pd.Series:
    if df.empty:
        return pd.Series(dtype=float)

    typical = (df["high"] + df["low"] + df["close"]) / 3.0
    volume = (
        pd.to_numeric(df["volume"], errors="coerce")
        .fillna(0.0)
        .clip(lower=0.0)
    )

    local_date = (
        pd.to_datetime(df["timestamp"], utc=True, errors="coerce")
        .dt.tz_convert(IST)
        .dt.date
    )

    cum_vol = volume.groupby(local_date).cumsum()
    cum_pv = (typical * volume).groupby(local_date).cumsum()

    vwap = cum_pv / cum_vol.replace(0, np.nan)

    if vwap.isna().all():
        vwap = typical.groupby(local_date, sort=False).transform(
            lambda x: x.expanding().mean()
        )
    return vwap.ffill()

def calculate_rsi(close: pd.Series, period: int = 14) -> pd.Series:
    """Wilder RSI, returning NaN until there is enough real price history."""
    values = pd.to_numeric(close, errors="coerce")
    delta = values.diff()
    gain = delta.clip(lower=0.0)
    loss = -delta.clip(upper=0.0)
    warmup = max(5, int(period) // 2)
    avg_gain = gain.ewm(alpha=1.0 / max(int(period), 1), adjust=False, min_periods=warmup).mean()
    avg_loss = loss.ewm(alpha=1.0 / max(int(period), 1), adjust=False, min_periods=warmup).mean()
    rs = avg_gain / avg_loss.replace(0.0, np.nan)
    rsi = 100.0 - (100.0 / (1.0 + rs))
    rsi = rsi.where(avg_loss > 0.0, 100.0)
    rsi = rsi.where(avg_gain > 0.0, 0.0).where(avg_loss > 0.0, rsi)
    both_flat = (avg_gain == 0.0) & (avg_loss == 0.0)
    return rsi.where(~both_flat, 50.0).clip(0.0, 100.0)


def calculate_adx(df: pd.DataFrame, period: int = ADX_PERIOD) -> pd.Series:
    """Wilder ADX with a conservative warm-up for intraday bar sets."""
    if df is None or df.empty or not {"high", "low", "close"}.issubset(df.columns):
        return pd.Series(dtype=float)
    work = df.copy()
    high = pd.to_numeric(work["high"], errors="coerce")
    low = pd.to_numeric(work["low"], errors="coerce")
    close = pd.to_numeric(work["close"], errors="coerce")
    up = high.diff()
    down = -low.diff()
    plus_dm = pd.Series(np.where((up > down) & (up > 0), up, 0.0), index=work.index)
    minus_dm = pd.Series(np.where((down > up) & (down > 0), down, 0.0), index=work.index)
    previous_close = close.shift(1)
    true_range = pd.concat(
        [(high - low), (high - previous_close).abs(), (low - previous_close).abs()], axis=1
    ).max(axis=1)
    n = max(int(period), 2)
    warmup = max(5, n // 2)
    atr = true_range.ewm(alpha=1.0 / n, adjust=False, min_periods=warmup).mean()
    plus_smoothed = plus_dm.ewm(alpha=1.0 / n, adjust=False, min_periods=warmup).mean()
    minus_smoothed = minus_dm.ewm(alpha=1.0 / n, adjust=False, min_periods=warmup).mean()
    plus_di = 100.0 * plus_smoothed / atr.replace(0.0, np.nan)
    minus_di = 100.0 * minus_smoothed / atr.replace(0.0, np.nan)
    dx = 100.0 * (plus_di - minus_di).abs() / (plus_di + minus_di).replace(0.0, np.nan)
    return dx.ewm(alpha=1.0 / n, adjust=False, min_periods=warmup).mean().clip(0.0, 100.0)


def calculate_vwap_bands(df: pd.DataFrame) -> tuple[float, float, float]:
    """Return current-session VWAP, upper 1-sigma band and lower 1-sigma band."""
    if df is None or df.empty:
        return float("nan"), float("nan"), float("nan")
    work = df.copy()
    for column in ("high", "low", "close", "volume"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    typical = (work["high"] + work["low"] + work["close"]) / 3.0
    volume = work["volume"].fillna(0.0).clip(lower=0.0)
    local_date = pd.to_datetime(work["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
    cum_v = volume.groupby(local_date).cumsum()
    cum_pv = (typical * volume).groupby(local_date).cumsum()
    cum_p2v = (typical.pow(2) * volume).groupby(local_date).cumsum()
    vwap_series = cum_pv / cum_v.replace(0.0, np.nan)
    variance = (cum_p2v / cum_v.replace(0.0, np.nan)) - vwap_series.pow(2)
    std_series = np.sqrt(variance.clip(lower=0.0))
    if vwap_series.notna().any():
        vwap_now = safe_float(vwap_series.dropna().iloc[-1], float("nan"))
        std_now = safe_float(std_series.dropna().iloc[-1], float("nan")) if std_series.notna().any() else float("nan")
    else:
        vwap_now, std_now = float("nan"), float("nan")
    return vwap_now, vwap_now + std_now, vwap_now - std_now


def _resample_ohlcv(df: pd.DataFrame, minutes: int) -> pd.DataFrame:
    if df is None or df.empty:
        return pd.DataFrame()
    work = df.copy()
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"]).set_index("timestamp").sort_index()
    for c in ("open", "high", "low", "close", "volume"):
        if c in work:
            work[c] = pd.to_numeric(work[c], errors="coerce")
    result = work.resample(
        f"{int(minutes)}min", origin="start_day", offset="9h15min", label="left", closed="left"
    ).agg(open=("open", "first"), high=("high", "max"), low=("low", "min"),
          close=("close", "last"), volume=("volume", "sum"))
    result = result.dropna(subset=["open", "high", "low", "close"]).reset_index()
    return filter_completed_candles(result, minutes)


def detect_rsi_divergence(df: pd.DataFrame, window: int = 5) -> str:
    """Detect a basic confirmed price/RSI divergence over two non-overlapping windows."""
    if df is None or df.empty or len(df) < 2 * window:
        return "NONE"
    work = df.copy().reset_index(drop=True)
    work["close"] = pd.to_numeric(work["close"], errors="coerce")
    work["high"] = pd.to_numeric(work["high"], errors="coerce")
    work["low"] = pd.to_numeric(work["low"], errors="coerce")
    work["rsi"] = calculate_rsi(work["close"], 14)
    previous = work.iloc[-2 * window:-window]
    recent = work.iloc[-window:]
    if previous["rsi"].notna().sum() < max(3, window // 2) or recent["rsi"].notna().sum() < max(3, window // 2):
        return "NONE"
    p_low_i = previous["low"].idxmin()
    r_low_i = recent["low"].idxmin()
    p_high_i = previous["high"].idxmax()
    r_high_i = recent["high"].idxmax()
    previous_low, recent_low = work.loc[p_low_i], work.loc[r_low_i]
    previous_high, recent_high = work.loc[p_high_i], work.loc[r_high_i]
    bullish = (
        safe_float(recent_low["low"]) < safe_float(previous_low["low"])
        and safe_float(recent_low["rsi"], float("nan")) >= safe_float(previous_low["rsi"], float("nan")) + 2.0
    )
    bearish = (
        safe_float(recent_high["high"]) > safe_float(previous_high["high"])
        and safe_float(recent_high["rsi"], float("nan")) <= safe_float(previous_high["rsi"], float("nan")) - 2.0
    )
    if bullish and not bearish:
        return "BULLISH"
    if bearish and not bullish:
        return "BEARISH"
    return "NONE"


def time_of_day_window(now: Optional[datetime] = None) -> str:
    current = now or now_ist()
    clock = current.astimezone(IST).time() if current.tzinfo else current.time()
    if clock >= NEW_ENTRY_CUTOFF:
        return "CUTOFF"
    if clock < OPENING_END:
        return "OPENING"
    if clock < MIDDAY_END:
        return "MIDDAY"
    return "AFTERNOON"


def classify_market_regime(
    price_session: pd.DataFrame,
    current_spot: float,
    current_vwap: float,
    proposed_direction: str,
    support: float,
    resistance: float,
) -> dict[str, Any]:
    """Classify direction/intensity; unknown or sideways conditions never authorize buying."""
    work = filter_completed_candles(price_session, 3) if price_session is not None and not price_session.empty else pd.DataFrame()
    result: dict[str, Any] = {
        "direction": "NEUTRAL", "intensity": "UNKNOWN", "adx": float("nan"),
        "rsi_3m": float("nan"), "rsi_15m": float("nan"), "upper_vwap_band": float("nan"),
        "lower_vwap_band": float("nan"), "volume_confirmed": False, "divergence": "NONE",
        "near_structural_level": False, "reversal_price_confirmed": False,
        "reason": "Insufficient completed candles.",
    }
    if work.empty or len(work) < 8 or not math.isfinite(current_vwap) or current_spot <= 0:
        return result
    work = work.sort_values("timestamp").reset_index(drop=True)
    for column in ("high", "low", "close", "volume"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    adx_values = calculate_adx(work, ADX_PERIOD)
    rsi_values = calculate_rsi(work["close"], 14)
    adx = safe_float(adx_values.iloc[-1], float("nan")) if not adx_values.empty else float("nan")
    rsi_3m = safe_float(rsi_values.iloc[-1], float("nan")) if not rsi_values.empty else float("nan")
    _, upper_band, lower_band = calculate_vwap_bands(work)
    recent = work.tail(3)
    previous = work.iloc[-6:-3] if len(work) >= 6 else work.iloc[:-3]
    if previous.empty:
        return result
    higher_high = float(recent["high"].max()) > float(previous["high"].max())
    higher_low = float(recent["low"].min()) > float(previous["low"].min())
    lower_high = float(recent["high"].max()) < float(previous["high"].max())
    lower_low = float(recent["low"].min()) < float(previous["low"].min())
    above_vwap = current_spot > current_vwap
    below_vwap = current_spot < current_vwap
    pa_direction = "BULLISH" if higher_high and higher_low else "BEARISH" if lower_high and lower_low else "NEUTRAL"
    direction = str(proposed_direction or "NEUTRAL").upper()
    if not ((direction == "BULLISH" and above_vwap and pa_direction == "BULLISH") or
            (direction == "BEARISH" and below_vwap and pa_direction == "BEARISH")):
        direction = "NEUTRAL"

    current_volume = safe_float(work["volume"].iloc[-1], 0.0)
    reference_volume = work["volume"].iloc[-21:-1] if len(work) > 2 else work["volume"].iloc[:-1]
    median_volume = safe_float(reference_volume.median(), 0.0) if not reference_volume.empty else 0.0
    volume_confirmed = median_volume > 0 and current_volume >= median_volume * STRONG_VOLUME_MULTIPLIER
    divergence_3m = detect_rsi_divergence(work, window=5)
    fifteen = _resample_ohlcv(work, 15)
    divergence_15m = detect_rsi_divergence(fifteen, window=3) if len(fifteen) >= 6 else "NONE"
    divergence = divergence_3m if divergence_3m == divergence_15m else "NONE"
    atr_series = calculate_atr(work, ATR_PERIOD)
    atr = safe_float(atr_series.iloc[-1], 0.0) if not atr_series.empty else 0.0
    level_tolerance = max(0.75 * atr, current_spot * 0.0015)
    near_support = math.isfinite(safe_float(support, float("nan"))) and abs(current_spot - support) <= level_tolerance
    near_resistance = math.isfinite(safe_float(resistance, float("nan"))) and abs(current_spot - resistance) <= level_tolerance
    near_level = (divergence == "BULLISH" and near_support) or (divergence == "BEARISH" and near_resistance)
    # Divergence by itself is not an entry. Require the latest completed 3m bar
    # to confirm a local reversal through the preceding bar's extreme.
    last_bar = work.iloc[-1]
    prior_bar = work.iloc[-2]
    bullish_reversal_bar = (
        safe_float(last_bar.get("close"), float("nan")) > safe_float(prior_bar.get("high"), float("inf"))
        and safe_float(last_bar.get("close"), float("nan")) > safe_float(prior_bar.get("close"), float("inf"))
    )
    bearish_reversal_bar = (
        safe_float(last_bar.get("close"), float("nan")) < safe_float(prior_bar.get("low"), float("-inf"))
        and safe_float(last_bar.get("close"), float("nan")) < safe_float(prior_bar.get("close"), float("-inf"))
    )
    reversal_price_confirmed = bool(
        near_level and (
            (divergence == "BULLISH" and bullish_reversal_bar)
            or (divergence == "BEARISH" and bearish_reversal_bar)
        )
    )

    if not math.isfinite(adx):
        intensity = "UNKNOWN"
        reason = "ADX has insufficient valid bars."
        direction = "NEUTRAL"
    elif adx < ADX_SIDEWAYS_THRESHOLD:
        intensity = "SIDEWAYS"
        reason = f"ADX {adx:.1f} below {ADX_SIDEWAYS_THRESHOLD:.1f}."
        direction = "NEUTRAL"
    elif divergence != "NONE" and near_level:
        intensity = "EXHAUSTION"
        direction = divergence
        reason = (
            f"Confirmed 3m/15m RSI {divergence.lower()} divergence near structural level; "
            + ("local reversal-price confirmation passed." if reversal_price_confirmed else "waiting for price to clear the preceding 3m bar extreme.")
        )
    elif (adx > ADX_STRONG_THRESHOLD and volume_confirmed and
          ((direction == "BULLISH" and math.isfinite(upper_band) and current_spot >= upper_band) or
           (direction == "BEARISH" and math.isfinite(lower_band) and current_spot <= lower_band))):
        intensity = "STRONG"
        reason = f"ADX {adx:.1f} > {ADX_STRONG_THRESHOLD:.1f}, price at outer VWAP band and volume confirmed."
    else:
        intensity = "NORMAL"
        reason = f"Directional structure with ADX {adx:.1f}; strong-breakout confirmation absent."
    return {
        "direction": direction, "intensity": intensity, "adx": adx, "rsi_3m": rsi_3m,
        "rsi_15m": safe_float(calculate_rsi(fifteen["close"], 14).iloc[-1], float("nan")) if len(fifteen) >= 8 else float("nan"),
        "upper_vwap_band": upper_band, "lower_vwap_band": lower_band,
        "volume_confirmed": bool(volume_confirmed), "divergence": divergence,
        "near_structural_level": bool(near_level),
        "reversal_price_confirmed": bool(reversal_price_confirmed), "reason": reason,
    }


def trend_direction(
    df: pd.DataFrame,
    lookback: int = 6,
) -> int:
    if df is None or len(df) < 2:
        return 0

    closes = (
        pd.to_numeric(df["close"], errors="coerce")
        .dropna()
        .tail(max(2, lookback))
    )
    if len(closes) < 2:
        return 0

    diffs = np.diff(closes.to_numpy(dtype=float))
    net = float(closes.iloc[-1] - closes.iloc[0])
    pos = int(np.sum(diffs > 0))
    neg = int(np.sum(diffs < 0))

    if net > 0 and pos >= neg:
        return 1
    if net < 0 and neg >= pos:
        return -1
    return 1 if net > 0 else -1 if net < 0 else 0


# =============================================================================
# FUTURES PRICE/OI REGIME
# =============================================================================

def _extract_quote_oi(quote: Optional[dict[str, Any]]) -> float:
    """Extract live futures OI from the common Upstox v2 quote shapes."""
    if not isinstance(quote, dict):
        return float("nan")

    candidates = [
        quote.get("oi"),
        quote.get("open_interest"),
        (quote.get("eFeedDetails") or {}).get("oi")
        if isinstance(quote.get("eFeedDetails"), dict) else None,
    ]
    for value in candidates:
        parsed = safe_float(value, float("nan"))
        if math.isfinite(parsed) and parsed >= 0:
            return parsed
    return float("nan")


def futures_oi_structure(
    futures_3m: pd.DataFrame,
    live_quote: Optional[dict[str, Any]] = None,
) -> dict[str, Any]:
    """Build a predictive Futures price/OI regime.

    Unlike a single-candle OI test, this measures:
      - multi-candle price/OI direction,
      - directional OI persistence,
      - OI acceleration versus recent typical change, and
      - the live quote OI versus the most recent completed candle.

    The result is deliberately independent from the option-chain score.
    """
    if futures_3m is None or len(futures_3m) < 4:
        return {
            "regime": "UNAVAILABLE", "bias": 0, "price_delta": 0.0,
            "oi_delta": 0.0, "oi_strength": 0.0, "oi_persistence": 0.0,
            "live_oi_change": float("nan"), "oi_acceleration": 0.0,
        }

    recent = futures_3m.tail(12).copy()
    price = pd.to_numeric(recent["close"], errors="coerce")
    oi = pd.to_numeric(recent["oi"], errors="coerce")
    valid = pd.DataFrame({"price": price, "oi": oi}).dropna()

    if len(valid) < 4:
        pdir = trend_direction(recent, min(6, len(recent)))
        return {
            "regime": "PRICE_ONLY_BULLISH" if pdir > 0 else "PRICE_ONLY_BEARISH" if pdir < 0 else "NEUTRAL",
            "bias": pdir, "price_delta": float(price.dropna().iloc[-1] - price.dropna().iloc[0]) if price.notna().sum() >= 2 else 0.0,
            "oi_delta": 0.0, "oi_strength": 0.0, "oi_persistence": 0.0,
            "live_oi_change": float("nan"), "oi_acceleration": 0.0,
        }

    price_delta = float(valid["price"].iloc[-1] - valid["price"].iloc[0])
    oi_delta = float(valid["oi"].iloc[-1] - valid["oi"].iloc[0])
    price_dir = 1 if price_delta > 0 else -1 if price_delta < 0 else 0
    oi_dir = 1 if oi_delta > 0 else -1 if oi_delta < 0 else 0

    price_deltas = valid["price"].diff().dropna()
    oi_deltas = valid["oi"].diff().dropna()
    aligned = ((price_deltas < 0) & (oi_deltas > 0)) if price_dir < 0 else ((price_deltas > 0) & (oi_deltas > 0)) if price_dir > 0 else pd.Series(dtype=bool)
    opposing = ((price_deltas < 0) & (oi_deltas < 0)) if price_dir < 0 else ((price_deltas > 0) & (oi_deltas < 0)) if price_dir > 0 else pd.Series(dtype=bool)
    persistence = float(aligned.mean()) if len(aligned) else 0.0

    median_abs_oi_change = float(np.median(np.abs(oi_deltas.to_numpy(dtype=float)))) if len(oi_deltas) else 0.0
    last_oi_change = float(oi_deltas.iloc[-1]) if len(oi_deltas) else 0.0
    acceleration = (
        last_oi_change / median_abs_oi_change
        if median_abs_oi_change > 0 else 0.0
    )

    live_oi = _extract_quote_oi(live_quote)
    last_completed_oi = float(valid["oi"].iloc[-1])
    live_oi_change = live_oi - last_completed_oi if math.isfinite(live_oi) else float("nan")

    bullish_regime = price_dir > 0 and oi_dir > 0
    bearish_regime = price_dir < 0 and oi_dir > 0
    bullish_cover = price_dir > 0 and oi_dir < 0
    bearish_unwind = price_dir < 0 and oi_dir < 0

    if bearish_regime:
        regime, bias = "SHORT_BUILDUP", -1
    elif bullish_regime:
        regime, bias = "LONG_BUILDUP", 1
    elif bullish_cover:
        regime, bias = "SHORT_COVERING", 1
    elif bearish_unwind:
        regime, bias = "LONG_UNWINDING", -1
    elif price_dir < 0:
        regime, bias = "PRICE_ONLY_BEARISH", -1
    elif price_dir > 0:
        regime, bias = "PRICE_ONLY_BULLISH", 1
    else:
        regime, bias = "NEUTRAL", 0

    # Strength is intentionally dominated by persistence and OI magnitude.
    price_range = float(valid["price"].max() - valid["price"].min())
    price_component = min(abs(price_delta) / max(price_range, 1.0), 1.0)
    persistence_component = min(persistence / FUTURES_OI_MIN_PERSISTENCE, 1.0)
    acceleration_component = min(abs(acceleration) / 2.0, 1.0)
    live_component = (
        min(abs(live_oi_change) / max(median_abs_oi_change, 1.0), 1.0)
        if math.isfinite(live_oi_change) else 0.0
    )
    strength = 0.40 * persistence_component + 0.25 * price_component + 0.20 * acceleration_component + 0.15 * live_component

    # For short build-up, only a positive OI trend is predictive; an OI fall
    # while price falls is a different regime (long unwinding).
    if regime in {"SHORT_BUILDUP", "LONG_BUILDUP"} and persistence < FUTURES_OI_MIN_PERSISTENCE:
        strength *= 0.70

    logger.info(
        "FUTURES OI ENGINE: regime=%s bias=%+d price_delta=%+.2f oi_delta=%+.0f "
        "persistence=%.2f acceleration=%.2f live_oi_change=%+.0f strength=%.3f",
        regime, bias, price_delta, oi_delta, persistence, acceleration,
        live_oi_change if math.isfinite(live_oi_change) else float("nan"), strength,
    )

    return {
        "regime": regime,
        "bias": bias,
        "price_delta": price_delta,
        "oi_delta": oi_delta,
        "oi_strength": float(strength),
        "oi_persistence": persistence,
        "live_oi_change": live_oi_change,
        "oi_acceleration": float(acceleration),
        "opposing_fraction": float(opposing.mean()) if len(opposing) else 0.0,
    }


# =============================================================================
# OPTION CHAIN
# =============================================================================

def _nearest_active_option_expiry() -> str:
    """Return the nearest non-expired NIFTY option expiry available to Upstox."""
    payload = api_get(
        OPTION_CONTRACT_URL,
        {"instrument_key": NIFTY_KEY},
        retries=4,
    )
    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError("No active NIFTY option contracts returned by Upstox.")

    today = now_ist().date()
    future_expiries: list[date] = []

    for contract in contracts:
        if not isinstance(contract, dict):
            continue
        expiry = parse_date(str(contract.get("expiry", "")))
        if expiry is not None and expiry >= today:
            future_expiries.append(expiry)

    if not future_expiries:
        raise ScannerError(
            f"No active NIFTY option expiry found on or after {today.isoformat()}."
        )

    selected = min(future_expiries)
    logger.info(
        "Selected nearest active NIFTY option expiry: %s",
        selected.isoformat(),
    )
    return selected.isoformat()


def get_option_chain(state: Optional[dict[str, Any]] = None) -> tuple[str, list[dict[str, Any]]]:
    """
    Load the nearest active NIFTY option expiry and then request its chain.

    We intentionally do not use Upstox's relative ``current_week`` keyword
    here. On the trading day immediately after a weekly expiry, that keyword
    can resolve to a completed week and the chain may be empty. Resolving the
    nearest active expiry from the option-contract endpoint makes the scanner
    roll automatically from (for example) 17-Sep to 24-Sep.
    """
    expiry = None
    today = now_ist().date()
    if isinstance(state, dict):
        cached_expiry = parse_date(str(state.get("option_expiry", "")))
        if cached_expiry and cached_expiry >= today:
            expiry = cached_expiry.isoformat()
    if not expiry:
        expiry = _nearest_active_option_expiry()
        if isinstance(state, dict):
            state["option_expiry"] = expiry

    payload = api_get(
        OPTION_CHAIN_URL,
        {
            "instrument_key": NIFTY_KEY,
            "expiry_date": expiry,
        },
        retries=4,
    )
    data = payload.get("data", [])

    if not isinstance(data, list) or not data:
        raise ScannerError(
            f"NIFTY option chain is empty for active expiry {expiry}."
        )

    # Guard against an unexpected mixed-expiry response.
    normalized_expiry = expiry[:10]
    filtered = [
        row
        for row in data
        if isinstance(row, dict)
        and str(row.get("expiry", ""))[:10] == normalized_expiry
    ]

    if filtered:
        data = filtered

    logger.info(
        "Loaded option chain: expiry=%s rows=%d",
        expiry,
        len(data),
    )
    return expiry, data


def chain_rows(chain: list[dict[str, Any]]) -> dict[float, dict[str, Any]]:
    out: dict[float, dict[str, Any]] = {}
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"), float("nan"))
        if math.isfinite(strike):
            out[strike] = row

    if not out:
        raise ScannerError("No valid strikes in option chain.")
    return out


def nearest_strike(spot: float, strikes: list[float]) -> float:
    if not strikes:
        raise ScannerError("No option strikes available.")
    return min(strikes, key=lambda x: abs(x - spot))


def strike_step(strikes: list[float]) -> float:
    unique = sorted(set(float(x) for x in strikes))
    diffs = [
        unique[i + 1] - unique[i]
        for i in range(len(unique) - 1)
        if unique[i + 1] > unique[i]
    ]
    if not diffs:
        raise ScannerError("Unable to determine strike interval.")

    # Median is robust against one-off gaps/anomalous strikes. Using the raw
    # minimum can accidentally turn a 100-point chain into a 50-point chain and
    # corrupt ATM/adjacent-strike selection.
    return float(np.median(np.asarray(diffs, dtype=float)))


def option_side_data(
    row: dict[str, Any],
    option_type: str,
) -> dict[str, Any]:
    key = "call_options" if option_type == "CE" else "put_options"
    block = row.get(key) or {}
    market = block.get("market_data") or {}
    greeks = block.get("option_greeks") or {}

    return {
        "instrument_key": block.get("instrument_key"),
        "ltp": safe_float(market.get("ltp")),
        "close_price": safe_float(market.get("close_price")),
        "oi": safe_float(market.get("oi")),
        "prev_oi": safe_float(market.get("prev_oi")),
        "volume": safe_float(market.get("volume")),
        "bid": safe_float(market.get("bid_price")),
        "ask": safe_float(market.get("ask_price")),
        "bid_qty": safe_float(market.get("bid_qty")),
        "ask_qty": safe_float(market.get("ask_qty")),
        "delta": safe_float(greeks.get("delta"), float("nan")),
        "theta": safe_float(greeks.get("theta"), 0.0),
    }



def classify_option_flow(
    option_type: str,
    price_change_pct: float,
    oi_change: float,
    noise_pct: float = STRUCTURE_ACTIVITY_PRICE_NOISE_PCT,
) -> tuple[str, int]:
    """Classify option price/OI flow into underlying directional bias."""
    option_type = str(option_type).upper()
    if option_type not in {"CE", "PE"}:
        return "UNKNOWN", 0
    if abs(float(oi_change)) <= 0:
        return "NO_OI_CHANGE", 0
    if abs(float(price_change_pct)) < noise_pct:
        return (
            "OI_BUILDING_UNCERTAIN" if oi_change > 0 else "OI_UNWINDING_UNCERTAIN",
            0,
        )

    price_up = price_change_pct > 0
    oi_up = oi_change > 0

    if option_type == "CE":
        if price_up and oi_up:
            return "CALL_BUYING", 1
        if (not price_up) and oi_up:
            return "CALL_WRITING", -1
        if price_up and (not oi_up):
            return "CALL_SHORT_COVERING", 1
        return "CALL_LONG_UNWINDING", -1

    if price_up and oi_up:
        return "PUT_BUYING", -1
    if (not price_up) and oi_up:
        return "PUT_WRITING", 1
    if price_up and (not oi_up):
        return "PUT_SHORT_COVERING", -1
    return "PUT_LONG_UNWINDING", 1


def build_option_oi_snapshot(
    chain: list[dict[str, Any]],
    expiry: str,
) -> dict[str, Any]:
    """Persist current option OI/LTP by strike so the next scan can calculate true intraday changes."""
    snapshot: dict[str, Any] = {
        "date": now_ist().date().isoformat(),
        "expiry": expiry,
        "timestamp": now_ist().isoformat(),
        "strikes": {},
    }
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"), float("nan"))
        if not math.isfinite(strike):
            continue
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        snapshot["strikes"][str(float(strike))] = {
            "call_oi": safe_float(ce.get("oi")),
            "put_oi": safe_float(pe.get("oi")),
            "call_ltp": safe_float(ce.get("ltp")),
            "put_ltp": safe_float(pe.get("ltp")),
        }
    return snapshot


def update_option_oi_velocity_history(
    state: dict[str, Any],
    chain: list[dict[str, Any]],
    expiry: str,
    *,
    now: Optional[datetime] = None,
) -> dict[float, dict[str, Any]]:
    """Measure per-strike OI change versus a 15-30 minute-old same-session snapshot."""
    current_time = now or now_ist()
    if current_time.tzinfo is None:
        current_time = current_time.replace(tzinfo=IST)
    else:
        current_time = current_time.astimezone(IST)
    today = current_time.date().isoformat()
    current_by_key: dict[str, dict[str, Any]] = {}
    rows = chain_rows(chain)
    for strike, row in rows.items():
        for side in ("CE", "PE"):
            data = option_side_data(row, side)
            key = str(data.get("instrument_key") or "").strip()
            oi = safe_float(data.get("oi"), float("nan"))
            if key and math.isfinite(oi) and oi > 0:
                current_by_key[key] = {"strike": float(strike), "side": side, "oi": oi}

    history = state.get("option_oi_history")
    if not isinstance(history, list):
        history = []
    valid_history: list[dict[str, Any]] = []
    eligible_baselines: list[tuple[float, dict[str, Any]]] = []
    now_stamp = pd.Timestamp(current_time)
    for item in history:
        if not isinstance(item, dict) or item.get("date") != today or str(item.get("expiry"))[:10] != str(expiry)[:10]:
            continue
        try:
            stamp = pd.Timestamp(item.get("timestamp"))
            if stamp.tzinfo is None:
                stamp = stamp.tz_localize(IST)
            else:
                stamp = stamp.tz_convert(IST)
        except Exception:
            continue
        age = (now_stamp - stamp).total_seconds() / 60.0
        if age < 0 or age > OPTION_OI_HISTORY_KEEP_MINUTES:
            continue
        item_copy = dict(item)
        item_copy["timestamp"] = stamp.isoformat()
        valid_history.append(item_copy)
        if OPTION_OI_MIN_AGE_MINUTES <= age <= OPTION_OI_MAX_AGE_MINUTES:
            eligible_baselines.append((age, item_copy))

    baseline_age = float("nan")
    baseline: dict[str, Any] = {}
    if eligible_baselines:
        baseline_age, baseline = min(eligible_baselines, key=lambda pair: abs(pair[0] - 20.0))
    baseline_map = baseline.get("oi_by_instrument", {}) if baseline else {}
    by_strike: dict[float, dict[str, Any]] = {}
    for strike, row in rows.items():
        current_ce = option_side_data(row, "CE")
        current_pe = option_side_data(row, "PE")
        ce_key = str(current_ce.get("instrument_key") or "")
        pe_key = str(current_pe.get("instrument_key") or "")
        ce_old = baseline_map.get(ce_key, {}) if isinstance(baseline_map, dict) else {}
        pe_old = baseline_map.get(pe_key, {}) if isinstance(baseline_map, dict) else {}
        old_call_oi = safe_float(ce_old.get("oi"), float("nan")) if isinstance(ce_old, dict) else float("nan")
        old_put_oi = safe_float(pe_old.get("oi"), float("nan")) if isinstance(pe_old, dict) else float("nan")
        current_call_oi = safe_float(current_ce.get("oi"), float("nan"))
        current_put_oi = safe_float(current_pe.get("oi"), float("nan"))
        call_available = math.isfinite(old_call_oi) and old_call_oi > 0 and math.isfinite(current_call_oi) and current_call_oi > 0
        put_available = math.isfinite(old_put_oi) and old_put_oi > 0 and math.isfinite(current_put_oi) and current_put_oi > 0
        call_change = current_call_oi - old_call_oi if call_available else float("nan")
        put_change = current_put_oi - old_put_oi if put_available else float("nan")
        by_strike[float(strike)] = {
            "available": bool(call_available and put_available and math.isfinite(baseline_age)),
            "call_oi_change": call_change,
            "put_oi_change": put_change,
            "call_oi_change_pct": call_change / old_call_oi if call_available else float("nan"),
            "put_oi_change_pct": put_change / old_put_oi if put_available else float("nan"),
            "baseline_minutes": baseline_age,
        }

    current_snapshot = {
        "date": today,
        "expiry": str(expiry)[:10],
        "timestamp": current_time.isoformat(),
        "oi_by_instrument": current_by_key,
    }
    if not valid_history or str(valid_history[-1].get("timestamp")) != current_snapshot["timestamp"]:
        valid_history.append(current_snapshot)
    state["option_oi_history"] = valid_history[-40:]
    logger.info(
        "OPTION OI VELOCITY: baseline=%s age_min=%s strikes_with_15_30m_data=%d/%d",
        "AVAILABLE" if eligible_baselines else "WARMING_UP",
        f"{baseline_age:.1f}" if math.isfinite(baseline_age) else "-",
        sum(1 for item in by_strike.values() if item.get("available")), len(by_strike),
    )
    return by_strike


def permitted_strikes_for_regime(
    atm: float,
    step: float,
    direction: str,
    intensity: str,
    *,
    is_expiry_day: bool = False,
    now: Optional[datetime] = None,
) -> list[float]:
    """Return the single authoritative strike-routing array for all call sites."""
    direction = str(direction).upper()
    intensity = str(intensity).upper()
    if direction not in {"BULLISH", "BEARISH"} or step <= 0 or intensity in {"SIDEWAYS", "UNKNOWN"}:
        return []
    if is_expiry_day:
        return [atm - step, atm] if direction == "BULLISH" else [atm, atm + step]
    window = time_of_day_window(now)
    if window == "CUTOFF":
        return []
    if intensity == "EXHAUSTION":
        return [atm - 2 * step, atm - 3 * step] if direction == "BULLISH" else [atm + 2 * step, atm + 3 * step]
    # OTM candidates are only allowed after 13:30 and only for a confirmed STRONG regime.
    if intensity == "STRONG" and window == "AFTERNOON":
        return [atm, atm + step, atm + 2 * step] if direction == "BULLISH" else [atm - 2 * step, atm - step, atm]
    # Opening and normal/midday conditions keep the candidate set ATM/ITM only.
    return [atm - step, atm] if direction == "BULLISH" else [atm, atm + step]


def collect_option_premium_vwaps(
    chain: list[dict[str, Any]],
    spot: float,
    direction: str,
    intensity: str,
    *,
    is_expiry_day: bool,
    now: Optional[datetime] = None,
) -> dict[str, dict[str, float]]:
    """Fetch completed 1-minute option candles and calculate each contract's own VWAP."""
    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    option_type = "CE" if direction == "BULLISH" else "PE"
    targets = permitted_strikes_for_regime(
        atm, step, direction, intensity, is_expiry_day=is_expiry_day, now=now
    )
    result: dict[str, dict[str, float]] = {}
    for target in targets:
        matched = min(strikes, key=lambda value: abs(value - target))
        if abs(matched - target) > 0.01:
            continue
        data = option_side_data(rows[matched], option_type)
        key = str(data.get("instrument_key") or "").strip()
        if not key:
            continue
        try:
            candles = get_intraday_candles(key, 1, strict=False)
            completed = filter_completed_candles(candles, 1) if not candles.empty else pd.DataFrame()
            if completed.empty or safe_float(completed["volume"].sum(), 0.0) <= 0:
                logger.info("OPTION PREMIUM VWAP UNAVAILABLE: %s %.0f; candidate will be rejected.", option_type, matched)
                continue
            vwap_series = calculate_vwap(completed)
            premium_vwap = safe_float(vwap_series.iloc[-1], float("nan")) if not vwap_series.empty else float("nan")
            if math.isfinite(premium_vwap) and premium_vwap > 0:
                result[key] = {"premium_vwap": premium_vwap}
                logger.info(
                    "OPTION PREMIUM VWAP: %s %.0f LTP=%.2f VWAP=%.2f above=%s",
                    option_type, matched, safe_float(data.get("ltp")), premium_vwap,
                    safe_float(data.get("ltp")) > premium_vwap,
                )
        except (ScannerError, KeyError, ValueError, TypeError) as exc:
            logger.info("OPTION PREMIUM VWAP UNAVAILABLE: %s %.0f: %s", option_type, matched, exc)
    return result


def _intraday_option_changes(
    chain: list[dict[str, Any]],
    previous_snapshot: Optional[dict[str, Any]],
    change_oi_by_strike: Optional[dict[float, dict[str, float]]],
    expiry: str,
) -> tuple[dict[float, dict[str, Any]], str]:
    """Calculate scan-to-scan OI changes; use API day-change only on the first scan of a session."""
    rows = chain_rows(chain)
    today = now_ist().date().isoformat()
    same_day = bool(
        isinstance(previous_snapshot, dict)
        and str(previous_snapshot.get("date", "")) == today
        and str(previous_snapshot.get("expiry", "")) == str(expiry)
        and isinstance(previous_snapshot.get("strikes"), dict)
    )
    prior = previous_snapshot.get("strikes", {}) if same_day else {}
    mode = "INTRADAY_SNAPSHOT" if same_day and prior else "DAY_CHANGE_API_WARMUP"
    out: dict[float, dict[str, Any]] = {}

    for strike, row in rows.items():
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        api = (change_oi_by_strike or {}).get(float(strike), {})
        old = prior.get(str(float(strike)), {}) if same_day else {}

        if same_day and old:
            call_oi_change = safe_float(ce.get("oi")) - safe_float(old.get("call_oi"))
            put_oi_change = safe_float(pe.get("oi")) - safe_float(old.get("put_oi"))
            old_call_ltp = safe_float(old.get("call_ltp"))
            old_put_ltp = safe_float(old.get("put_ltp"))
            call_price_change = (
                (safe_float(ce.get("ltp")) - old_call_ltp) / old_call_ltp
                if old_call_ltp > 0 else 0.0
            )
            put_price_change = (
                (safe_float(pe.get("ltp")) - old_put_ltp) / old_put_ltp
                if old_put_ltp > 0 else 0.0
            )
        else:
            call_oi_change = safe_float(
                api.get("call_oi_change", api.get("call_change")),
                safe_float(ce.get("oi")) - safe_float(ce.get("prev_oi")),
            )
            put_oi_change = safe_float(
                api.get("put_oi_change", api.get("put_change")),
                safe_float(pe.get("oi")) - safe_float(pe.get("prev_oi")),
            )
            ce_close = safe_float(ce.get("close_price"))
            pe_close = safe_float(pe.get("close_price"))
            call_price_change = (
                (safe_float(ce.get("ltp")) - ce_close) / ce_close
                if ce_close > 0 else 0.0
            )
            put_price_change = (
                (safe_float(pe.get("ltp")) - pe_close) / pe_close
                if pe_close > 0 else 0.0
            )

        call_activity, call_bias = classify_option_flow("CE", call_price_change, call_oi_change)
        put_activity, put_bias = classify_option_flow("PE", put_price_change, put_oi_change)
        out[float(strike)] = {
            "call_oi_change": float(call_oi_change),
            "put_oi_change": float(put_oi_change),
            "call_price_change_pct": float(call_price_change),
            "put_price_change_pct": float(put_price_change),
            "call_bias": int(call_bias),
            "put_bias": int(put_bias),
            "call_activity": call_activity,
            "put_activity": put_activity,
        }
    return out, mode



def chain_oi_support_resistance(
    chain: list[dict[str, Any]],
    spot: float,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
    previous_option_snapshot: Optional[dict[str, Any]] = None,
    expiry: str = "",
    previous_support: Optional[float] = None,
    previous_resistance: Optional[float] = None,
) -> dict[str, Any]:
    """Build authoritative support/resistance from current option OI.

    OI concentration is the structural source. Change-OI/option price behavior
    is used only to describe the wall and to break ties; it never replaces OI
    with a price-derived level.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    flow_map, flow_mode = _intraday_option_changes(
        chain, previous_option_snapshot, change_oi_by_strike, expiry
    )

    entries: list[dict[str, Any]] = []
    for strike, row in rows.items():
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        flow = flow_map.get(float(strike), {})
        dist_steps = abs(float(strike) - atm) / max(step, 1.0)
        entries.append({
            "strike": float(strike),
            "call_oi": max(safe_float(ce.get("oi")), 0.0),
            "put_oi": max(safe_float(pe.get("oi")), 0.0),
            "call_oi_change": safe_float(flow.get("call_oi_change")),
            "put_oi_change": safe_float(flow.get("put_oi_change")),
            "call_bias": int(flow.get("call_bias", 0)),
            "put_bias": int(flow.get("put_bias", 0)),
            "call_activity": str(flow.get("call_activity", "NO_OI_CHANGE")),
            "put_activity": str(flow.get("put_activity", "NO_OI_CHANGE")),
            "dist_steps": float(dist_steps),
        })

    if not entries:
        raise ScannerError("No option-chain strikes available for structural analysis.")

    def pick_wall(side: str) -> Optional[dict[str, Any]]:
        pool = [
            x for x in entries
            if (float(x["strike"]) < spot if side == "support" else float(x["strike"]) > spot)
        ]
        if not pool:
            return None
        oi_key = "put_oi" if side == "support" else "call_oi"
        change_key = "put_oi_change" if side == "support" else "call_oi_change"
        max_oi = max(float(x[oi_key]) for x in pool)
        median_oi = float(np.median([float(x[oi_key]) for x in pool]))
        meaningful = [x for x in pool if float(x[oi_key]) >= max(0.30 * max_oi, median_oi)]
        source_pool = meaningful or sorted(pool, key=lambda x: (-float(x[oi_key]), float(x["dist_steps"])))[:6]
        # For the authoritative active structural level, nearest meaningful OI
        # wall is used; OI size breaks ties. This makes T1 an actionable wall.
        source_pool.sort(key=lambda x: (float(x["dist_steps"]), -float(x[oi_key]), -abs(float(x[change_key]))))
        return source_pool[0]

    support_row = pick_wall("support")
    resistance_row = pick_wall("resistance")

    def rank_other(side: str, primary: Optional[dict[str, Any]]) -> list[dict[str, Any]]:
        pool = [
            x for x in entries
            if (float(x["strike"]) < spot if side == "support" else float(x["strike"]) > spot)
            and (primary is None or abs(float(x["strike"]) - float(primary["strike"])) > 0.01)
        ]
        oi_key = "put_oi" if side == "support" else "call_oi"
        max_oi = max((float(x[oi_key]) for x in pool), default=1.0)
        median_oi = float(np.median([float(x[oi_key]) for x in pool])) if pool else 0.0
        meaningful = [x for x in pool if float(x[oi_key]) >= max(0.30 * max_oi, median_oi)]
        pool = meaningful or pool
        return sorted(pool, key=lambda x: (float(x["dist_steps"]), -float(x[oi_key]), float(x["strike"])))

    support_level = float(support_row["strike"]) if support_row else float("nan")
    resistance_level = float(resistance_row["strike"]) if resistance_row else float("nan")
    support_others = rank_other("support", support_row)
    resistance_others = rank_other("resistance", resistance_row)
    support_2 = float(support_others[0]["strike"]) if support_others else support_level
    resistance_2 = float(resistance_others[0]["strike"]) if resistance_others else resistance_level

    support_source = "OPTION_OI" if support_row else "NONE"
    resistance_source = "OPTION_OI" if resistance_row else "NONE"

    # Persist the last OI wall only as a temporary data-quality stabilizer. It is
    # never synthesized from VWAP or price swings.
    if support_row is None and math.isfinite(safe_float(previous_support, float("nan"))):
        ps = safe_float(previous_support, float("nan"))
        if ps < spot and abs(ps - spot) / max(step, 1.0) <= 6.0:
            support_level = ps
            support_2 = ps
            support_source = "PERSISTED_OPTION_OI"
    if resistance_row is None and math.isfinite(safe_float(previous_resistance, float("nan"))):
        pr = safe_float(previous_resistance, float("nan"))
        if pr > spot and abs(pr - spot) / max(step, 1.0) <= 6.0:
            resistance_level = pr
            resistance_2 = pr
            resistance_source = "PERSISTED_OPTION_OI"

    total_put_oi = sum(float(x["put_oi"]) for x in entries)
    total_call_oi = sum(float(x["call_oi"]) for x in entries)
    pcr = total_put_oi / total_call_oi if total_call_oi > 0 else float("nan")
    pcr_bias = 1 if math.isfinite(pcr) and pcr >= PCR_BULL_THRESHOLD else -1 if math.isfinite(pcr) and pcr <= PCR_BEAR_THRESHOLD else 0

    nearby = [x for x in entries if abs(float(x["strike"]) - atm) <= step * 5]
    bull_pressure = sum(
        max(float(x["put_oi_change"]), 0.0) + max(-float(x["call_oi_change"]), 0.0) for x in nearby
    )
    bear_pressure = sum(
        max(float(x["call_oi_change"]), 0.0) + max(-float(x["put_oi_change"]), 0.0) for x in nearby
    )
    pressure_den = bull_pressure + bear_pressure
    pressure_score = (bull_pressure - bear_pressure) / pressure_den if pressure_den > 0 else 0.0
    oi_bias = 1 if pressure_score >= 0.08 else -1 if pressure_score <= -0.08 else 0

    support_change_strength = 0.0
    if support_row and total_put_oi > 0:
        support_change_strength = min(abs(float(support_row["put_oi_change"])) / total_put_oi, 1.0)
    resistance_change_strength = 0.0
    if resistance_row and total_call_oi > 0:
        resistance_change_strength = min(abs(float(resistance_row["call_oi_change"])) / total_call_oi, 1.0)

    support_flow_bias = int(support_row["put_bias"]) if support_row else 0
    resistance_flow_bias = int(resistance_row["call_bias"]) if resistance_row else 0
    support_activity = str(support_row["put_activity"]) if support_row else "NO_OI_DATA"
    resistance_activity = str(resistance_row["call_activity"]) if resistance_row else "NO_OI_DATA"

    logger.info(
        "CHAIN STRUCTURE: support=%s/%s resistance=%s/%s source=%s/%s flow_mode=%s pressure=%+.3f bias=%+d PCR=%s",
        f"{support_level:.0f}" if math.isfinite(support_level) else "NA",
        f"{support_2:.0f}" if math.isfinite(support_2) else "NA",
        f"{resistance_level:.0f}" if math.isfinite(resistance_level) else "NA",
        f"{resistance_2:.0f}" if math.isfinite(resistance_2) else "NA",
        support_source, resistance_source, flow_mode, pressure_score, oi_bias,
        f"{pcr:.3f}" if math.isfinite(pcr) else "NA",
    )

    return {
        "support_1": float(support_level), "support_2": float(support_2),
        "resistance_1": float(resistance_level), "resistance_2": float(resistance_2),
        "support_source": support_source, "resistance_source": resistance_source,
        "support_strength": float((support_row or {}).get("put_oi", 0.0)),
        "resistance_strength": float((resistance_row or {}).get("call_oi", 0.0)),
        "support_change_strength": float(support_change_strength),
        "resistance_change_strength": float(resistance_change_strength),
        "major_support": float(support_level), "major_resistance": float(resistance_level),
        "support_flow_bias": support_flow_bias, "resistance_flow_bias": resistance_flow_bias,
        "support_activity": support_activity, "resistance_activity": resistance_activity,
        "put_writing_at_support": support_activity == "PUT_WRITING",
        "put_unwinding_at_support": support_activity in {"PUT_LONG_UNWINDING", "PUT_SHORT_COVERING"},
        "call_writing_at_resistance": resistance_activity == "CALL_WRITING",
        "call_unwinding_at_resistance": resistance_activity in {"CALL_LONG_UNWINDING", "CALL_SHORT_COVERING"},
        "pressure_score": float(pressure_score), "normalized_diff": float(pressure_score),
        "oi_bias": int(oi_bias), "change_bias": int(oi_bias),
        "predictive_bias": int(oi_bias), "predictive_strength": float(abs(pressure_score)),
        "level_bias": 0, "pcr": float(pcr) if math.isfinite(pcr) else float("nan"),
        "pcr_bias": int(pcr_bias), "flow_mode": flow_mode,
        "change_flow_score": float(pressure_score), "change_flow_bias": int(oi_bias),
        "option_flow_by_strike": flow_map,
    }


def get_change_oi_confirmation(
    expiry: str,
) -> tuple[int, float, dict[float, dict[str, float]]]:
    """Fetch aggregate and per-strike Change-in-OI in one API call."""
    today = now_ist().date().isoformat()
    by_strike: dict[float, dict[str, float]] = {}

    try:
        payload = api_get(
            CHANGE_OI_URL,
            {
                "instrument_key": NIFTY_KEY,
                "expiry": expiry,
                "date": today,
                "interval": 1,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("Change-OI endpoint unavailable: %s", exc)
        return 0, 0.0, by_strike

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return 0, 0.0, by_strike

    put_change = safe_float(data.get("total_put_change_oi"))
    call_change = safe_float(data.get("total_call_change_oi"))

    detail_rows = data.get("call_put_oi_data_list", [])
    if isinstance(detail_rows, list):
        for item in detail_rows:
            if not isinstance(item, dict):
                continue
            strike = safe_float(item.get("strike_price"), float("nan"))
            if not math.isfinite(strike):
                continue
            call_change_value = safe_float(item.get("call_change_oi"))
            put_change_value = safe_float(item.get("put_change_oi"))
            by_strike[float(strike)] = {
                "call_oi_change": call_change_value,
                "put_oi_change": put_change_value,
                # Legacy aliases retained defensively for older state/tests.
                "call_change": call_change_value,
                "put_change": put_change_value,
            }

    den = abs(put_change) + abs(call_change)
    if den <= 0:
        return 0, 0.0, by_strike

    score = (put_change - call_change) / den
    bias = 1 if score > 0.10 else -1 if score < -0.10 else 0

    logger.info(
        "CHANGE-OI CONFIRMATION: put_change=%+.0f call_change=%+.0f score=%+.3f bias=%+d per_strike=%d",
        put_change, call_change, score, bias, len(by_strike),
    )
    return bias, score, by_strike



# =============================================================================
# VWAP / PRICE ACTION
# =============================================================================

def vwap_snapshot(
    price_session: pd.DataFrame,
) -> tuple[float, float, int]:
    """Calculate session VWAP from the NIFTY index price feed.

    Futures are deliberately excluded from the primary price/VWAP calculation;
    futures price/OI is treated separately as a derivatives confirmation.
    """
    if price_session is None or price_session.empty:
        raise ScannerError("Index session candles unavailable for VWAP.")

    work = price_session.copy()
    required = {"timestamp", "high", "low", "close"}
    missing = required.difference(work.columns)
    if missing:
        raise ScannerError(
            f"Index session candles missing VWAP columns: {sorted(missing)}"
        )

    for col in ("high", "low", "close"):
        work[col] = pd.to_numeric(work[col], errors="coerce")
    if "volume" not in work.columns:
        work["volume"] = 0.0
    work["volume"] = pd.to_numeric(work["volume"], errors="coerce").fillna(0.0)

    work = (
        work.dropna(subset=["timestamp", "high", "low", "close"])
        .sort_values("timestamp")
        .drop_duplicates("timestamp", keep="last")
    )
    if work.empty:
        raise ScannerError("No valid index session candles available for VWAP.")

    vwap_series = calculate_vwap(work).replace([np.inf, -np.inf], np.nan).dropna()
    if vwap_series.empty:
        typical = (work["high"] + work["low"] + work["close"]) / 3.0
        vwap_series = typical.expanding().mean().dropna()

    current_vwap = float(vwap_series.iloc[-1])
    slope = float(vwap_series.iloc[-1] - vwap_series.iloc[-2]) if len(vwap_series) >= 2 else 0.0
    price = float(work["close"].iloc[-1])
    level_bias = 1 if price > current_vwap else -1 if price < current_vwap else 0

    logger.info(
        "INDEX VWAP: price=%.2f vwap=%.2f slope=%+.2f level_bias=%+d bars=%d",
        price, current_vwap, slope, level_bias, len(vwap_series),
    )
    return current_vwap, slope, level_bias



def price_action_regime_snapshot(
    price_session: pd.DataFrame,
    vwap: float,
    atr3: float,
) -> dict[str, Any]:
    """Describe NIFTY price regime using multi-window persistence.

    Recent 3 bars are deliberately contextual. Primary directional persistence is
    measured from the session, a 12-bar window and the ratio/efficiency of recent
    directional movement. This prevents a short bounce from erasing an established
    trend while still detecting genuinely strong reversals.
    """
    result: dict[str, Any] = {
        "state": "UNKNOWN", "bias": 0, "strength": 0.0,
        "session_move_atr": 0.0, "recent7_move_atr": 0.0,
        "recent3_move_atr": 0.0, "recent12_move_atr": 0.0,
        "directional_down_ratio": 0.0, "directional_up_ratio": 0.0,
        "trend_efficiency": 0.0,
        "range12_atr": 0.0, "alternation": 0.0,
        "structure": "MIXED", "vwap_distance_atr": float("inf"),
        "latest_move_atr": 0.0, "bullish_structure": False,
        "bearish_structure": False, "sideways": False,
    }
    if price_session is None or price_session.empty:
        return result

    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 8:
        return result
    for c in ("open", "high", "low", "close"):
        work[c] = pd.to_numeric(work[c], errors="coerce")
    work = work.dropna(subset=["open", "high", "low", "close"]).reset_index(drop=True)
    if len(work) < 8:
        return result

    atr = max(float(atr3), 1.0)
    closes = work["close"].to_numpy(dtype=float)
    diffs = np.diff(closes)
    session_move = float(closes[-1] - closes[0])

    recent7_count = min(8, len(closes))
    recent3_count = min(4, len(closes))
    recent12_count = min(13, len(closes))
    recent7_move = float(closes[-1] - closes[-recent7_count])
    recent3_move = float(closes[-1] - closes[-recent3_count])
    recent12_move = float(closes[-1] - closes[-recent12_count])
    latest_move = float(diffs[-1]) if len(diffs) else 0.0

    w12 = work.tail(min(12, len(work)))
    split = max(2, len(w12) // 2)
    early = w12.iloc[:split]
    late = w12.iloc[-split:]
    higher_structure = bool(
        float(late["high"].mean()) > float(early["high"].mean())
        and float(late["low"].mean()) > float(early["low"].mean())
    )
    lower_structure = bool(
        float(late["high"].mean()) < float(early["high"].mean())
        and float(late["low"].mean()) < float(early["low"].mean())
    )
    structure = "HH_HL" if higher_structure else "LH_LL" if lower_structure else "MIXED"

    movement_window = diffs[-min(12, len(diffs)):]
    down_count = int(np.sum(movement_window < 0)) if len(movement_window) else 0
    up_count = int(np.sum(movement_window > 0)) if len(movement_window) else 0
    valid_count = max(down_count + up_count, 1)
    down_ratio = down_count / valid_count
    up_ratio = up_count / valid_count
    abs_path = float(np.sum(np.abs(movement_window))) if len(movement_window) else 0.0
    efficiency = abs(recent12_move) / abs_path if abs_path > 0 else 0.0

    last12 = work.tail(min(12, len(work)))
    range12 = float(last12["high"].max() - last12["low"].min())
    sign_diffs = np.sign(movement_window) if len(movement_window) else np.array([])
    valid_signs = sign_diffs[sign_diffs != 0]
    alternation = (
        float(np.sum(valid_signs[1:] != valid_signs[:-1]) / max(len(valid_signs) - 1, 1))
        if len(valid_signs) >= 2 else 0.0
    )

    price = float(closes[-1])
    vwap_distance = abs(price - vwap) / atr if math.isfinite(vwap) else float("inf")
    below_vwap = price < vwap
    above_vwap = price > vwap

    session_atr = session_move / atr
    recent7_atr = recent7_move / atr
    recent3_atr = recent3_move / atr
    recent12_atr = recent12_move / atr
    latest_atr = latest_move / atr

    # Strong current price structure requires the trend to agree with VWAP, but
    # continuous persistence may also be established by the longer movement window.
    bullish_structure = bool(
        above_vwap
        and (
            higher_structure
            or recent12_atr >= 0.20
        )
        and up_ratio >= 0.45
    )
    bearish_structure = bool(
        below_vwap
        and (
            lower_structure
            or recent12_atr <= -0.20
        )
        and down_ratio >= 0.45
    )

    sideways = bool(
        range12 / atr <= REGIME_SIDEWAYS_RANGE_ATR
        and abs(recent12_atr) <= REGIME_SIDEWAYS_NET_ATR
        and vwap_distance <= REGIME_SIDEWAYS_VWAP_DISTANCE_ATR
        and alternation >= REGIME_SIDEWAYS_ALTERNATION
    )

    if bullish_structure and not sideways:
        state = "BULLISH"
        bias = 1
        strength = min(1.0, 0.40 * min(abs(recent12_atr) / 1.0, 1.0) + 0.25 * up_ratio + 0.20 * efficiency + 0.15 * min(vwap_distance, 1.0))
    elif bearish_structure and not sideways:
        state = "BEARISH"
        bias = -1
        strength = min(1.0, 0.40 * min(abs(recent12_atr) / 1.0, 1.0) + 0.25 * down_ratio + 0.20 * efficiency + 0.15 * min(vwap_distance, 1.0))
    elif sideways:
        state = "SIDEWAYS"
        bias = 0
        strength = max(0.0, min(1.0, 0.55 + 0.15 * alternation))
    elif session_atr > 0.15 and recent12_atr < -0.15:
        state = "BULLISH_WEAKENING"
        bias = -1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    elif session_atr < -0.15 and recent12_atr > 0.15:
        state = "BEARISH_WEAKENING"
        bias = 1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    elif recent12_atr > 0.15:
        state = "BULLISH"
        bias = 1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    elif recent12_atr < -0.15:
        state = "BEARISH"
        bias = -1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    else:
        state = "SIDEWAYS"
        bias = 0
        strength = 0.35

    result.update({
        "state": state, "bias": int(bias), "strength": float(strength),
        "session_move_atr": float(session_atr),
        "recent7_move_atr": float(recent7_atr),
        "recent3_move_atr": float(recent3_atr),
        "recent12_move_atr": float(recent12_atr),
        "directional_down_ratio": float(down_ratio),
        "directional_up_ratio": float(up_ratio),
        "trend_efficiency": float(efficiency),
        "range12_atr": float(range12 / atr), "alternation": float(alternation),
        "structure": structure, "vwap_distance_atr": float(vwap_distance),
        "latest_move_atr": float(latest_atr),
        "bullish_structure": bullish_structure, "bearish_structure": bearish_structure,
        "sideways": sideways,
    })
    return result



# =============================================================================
# MARKET STRUCTURE ENGINE
# =============================================================================

def resolve_change_oi_flow(
    intraday_score: float,
    day_score: float,
    flow_mode: str,
) -> tuple[float, int, str, bool]:
    """Resolve the Change-OI signal without allowing neutral/contradictory snapshots to mislead direction.

    Priority:
      1. Warm/strong scan-to-scan intraday flow is primary.
      2. If the intraday snapshot is neutral/insufficient, the current-session
         Upstox aggregate Change-OI is the fallback.
      3. A strong contradiction is reported as a conflict and supplies no
         directional Change-OI confirmation; price/VWAP may still retain a
         directional WATCH state, but the conflicting flow cannot authorize entry.
    """
    intra = float(intraday_score) if math.isfinite(float(intraday_score)) else 0.0
    day = float(day_score) if math.isfinite(float(day_score)) else 0.0
    intra_abs = abs(intra)
    day_abs = abs(day)
    intra_directional = intra_abs >= STRUCTURE_CHANGE_OI_CONFIRM
    day_directional = day_abs >= STRUCTURE_CHANGE_OI_STRONG

    if str(flow_mode).upper() == "INTRADAY_SNAPSHOT" and intra_directional:
        # Do not let one small scan-to-scan snapshot reverse a clearly directional
        # session-level Change-OI signal. If both sources are directional and
        # disagree, preserve the conflict and block a new entry until they align.
        # This specifically guards the 09-Oct case: intraday=-0.155 vs day=+0.760.
        if day_directional and (intra * day) < 0:
            return 0.0, 0, "INTRADAY_DAY_CONFLICT", True
        bias = 1 if intra >= STRUCTURE_CHANGE_OI_CONFIRM else -1
        return intra, bias, "INTRADAY_PRIMARY", False

    # Neutral/empty intraday snapshot: fall back to the aggregate current-session
    # Change-OI endpoint rather than turning a clearly bearish/bullish session into
    # SIDEWAYS merely because the latest scan's local changes cancelled out.
    if day_directional:
        bias = 1 if day >= STRUCTURE_CHANGE_OI_STRONG else -1
        source = "DAY_CHANGE_API_FALLBACK_NEUTRAL_INTRADAY" if str(flow_mode).upper() == "INTRADAY_SNAPSHOT" else "DAY_CHANGE_API"
        return day, bias, source, False

    if intra_abs > 0.0:
        bias = 1 if intra >= STRUCTURE_CHANGE_OI_CONFIRM else -1 if intra <= -STRUCTURE_CHANGE_OI_CONFIRM else 0
        return intra, bias, "INTRADAY_WEAK", False

    return 0.0, 0, "NO_DIRECTIONAL_CHANGE_OI", False


def build_market_structure(
    spot: float,
    futures_3m: pd.DataFrame,
    futures_session: pd.DataFrame,
    chain_levels: dict[str, Any],
    change_oi_score: float,
    futures_live_quote: Optional[dict[str, Any]] = None,
    previous_direction: Optional[str] = None,
    previous_phase: Optional[str] = None,
    price_session: Optional[pd.DataFrame] = None,
) -> StructureResult:
    """Authoritative NIFTY market-structure state machine.

    Direction is decided by exactly three primary conditions:
      1. NIFTY price vs VWAP;
      2. sustained NIFTY price action (session + recent structure);
      3. directional Change-OI confirmation.

    OI support/resistance defines structural levels. A break strengthens the
    setup but is not required for an already-continuous trend. Futures price/OI
    and PCR remain descriptive context only.
    """
    primary_session = price_session if price_session is not None and not price_session.empty else futures_session
    futures_info = futures_oi_structure(futures_3m, futures_live_quote)
    futures_regime = str(futures_info.get("regime", "UNAVAILABLE"))
    futures_bias = int(futures_info.get("bias", 0))
    futures_strength = safe_float(futures_info.get("oi_strength"), 0.0)
    completed = filter_completed_candles(primary_session.copy().sort_values("timestamp"), 3)
    for c in ("open", "high", "low", "close"):
        if c in completed.columns:
            completed[c] = pd.to_numeric(completed[c], errors="coerce")
    completed = completed.dropna(subset=["open", "high", "low", "close"]).reset_index(drop=True)

    vwap, vwap_slope, _ = vwap_snapshot(primary_session)
    volatility_unit = max(safe_float(calculate_atr(completed, period=ATR_PERIOD).iloc[-1], 50.0) if len(completed) else 50.0, 1.0)
    work = completed
    current_close = float(work["close"].iloc[-1]) if not work.empty else float(spot)
    latest_move = float(work["close"].iloc[-1] - work["close"].iloc[-2]) if len(work) >= 2 else 0.0

    support_1 = safe_float(chain_levels.get("support_1"), float("nan"))
    support_2 = safe_float(chain_levels.get("support_2"), float("nan"))
    resistance_1 = safe_float(chain_levels.get("resistance_1"), float("nan"))
    resistance_2 = safe_float(chain_levels.get("resistance_2"), float("nan"))

    break_buffer = STRUCTURE_BREAK_BUFFER_ATR * volatility_unit
    if not math.isfinite(break_buffer) or break_buffer <= 0:
        break_buffer = 1.0

    previous_support = safe_float(chain_levels.get("previous_support_1"), float("nan"))
    previous_resistance = safe_float(chain_levels.get("previous_resistance_1"), float("nan"))
    prior = str(previous_direction or "").upper()
    prior_phase = str(previous_phase or "").upper()
    bullish_prior = prior == "BULLISH" or prior_phase in {"BULLISH", "CONTINUOUS_BULLISH", "BULLISH_BREAKOUT"}
    bearish_prior = prior == "BEARISH" or prior_phase in {"BEARISH", "CONTINUOUS_BEARISH", "BEARISH_BREAKDOWN"}

    # Validate OI levels against the live underlying price. A previously broken
    # resistance/support is a breakout reference, NOT the current resistance/
    # support. The old implementation overwrote a fresh resistance with the
    # prior resistance and could report resistance below spot (e.g. 22400 while
    # NIFTY was trading near 22417 on 09-Oct).
    price_reference = max(
        x for x in (safe_float(spot, float("nan")), current_close)
        if math.isfinite(x)
    )
    original_supports = [support_1, support_2]
    original_resistances = [resistance_1, resistance_2]
    live_supports = sorted(
        {float(x) for x in original_supports if math.isfinite(safe_float(x, float("nan"))) and float(x) < price_reference},
        reverse=True,
    )
    live_resistances = sorted(
        {float(x) for x in original_resistances if math.isfinite(safe_float(x, float("nan"))) and float(x) > price_reference},
    )
    prior_support_valid = math.isfinite(previous_support) and previous_support < price_reference
    prior_resistance_valid = math.isfinite(previous_resistance) and previous_resistance > price_reference

    if live_supports:
        support_1 = live_supports[0]
        support_2 = live_supports[1] if len(live_supports) > 1 else float("nan")
        if len(live_supports) == 1 and prior_support_valid and previous_support < support_1:
            support_2 = previous_support
    elif prior_support_valid and abs(previous_support - price_reference) <= 300.0:
        support_1, support_2 = previous_support, float("nan")
        chain_levels["support_source"] = "PERSISTED_OPTION_OI"
    else:
        support_1 = support_2 = float("nan")

    if live_resistances:
        resistance_1 = live_resistances[0]
        resistance_2 = live_resistances[1] if len(live_resistances) > 1 else float("nan")
        if len(live_resistances) == 1 and prior_resistance_valid and previous_resistance > resistance_1:
            resistance_2 = previous_resistance
    elif prior_resistance_valid and abs(previous_resistance - price_reference) <= 300.0:
        resistance_1, resistance_2 = previous_resistance, float("nan")
        chain_levels["resistance_source"] = "PERSISTED_OPTION_OI"
    else:
        resistance_1 = resistance_2 = float("nan")

    if math.isfinite(support_1) and math.isfinite(resistance_1) and support_1 >= resistance_1:
        logger.warning(
            "INVALID OI LEVEL ORDER: support=%.2f resistance=%.2f price=%.2f; directional entries will be blocked.",
            support_1, resistance_1, price_reference,
        )
        support_1 = support_2 = resistance_1 = resistance_2 = float("nan")

    below_vwap = math.isfinite(vwap) and current_close < vwap - STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * volatility_unit
    above_vwap = math.isfinite(vwap) and current_close > vwap + STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * volatility_unit

    flow_mode = str(chain_levels.get("flow_mode", "DAY_CHANGE_API_WARMUP")).upper()
    raw_intraday_flow = safe_float(chain_levels.get("change_flow_score"), safe_float(change_oi_score))
    effective_flow, effective_bias, effective_source, flow_conflict = resolve_change_oi_flow(
        intraday_score=raw_intraday_flow,
        day_score=change_oi_score,
        flow_mode=flow_mode,
    )
    # Directional option entries require material, not merely marginal, Change-OI.
    # The lower CONFIRM threshold still detects/report conflicts; the STRONG
    # threshold is the authorization threshold for actual entries.
    bearish_flow_ok = effective_flow <= -STRUCTURE_CHANGE_OI_STRONG and not flow_conflict
    bullish_flow_ok = effective_flow >= STRUCTURE_CHANGE_OI_STRONG and not flow_conflict

    futures_conflict_bearish = bool(
        futures_bias > 0 and futures_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH
    )
    futures_conflict_bullish = bool(
        futures_bias < 0 and futures_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH
    )

    price_info = price_action_regime_snapshot(primary_session, vwap, volatility_unit)
    session_move = safe_float(price_info.get("session_move_atr"), 0.0)
    recent12_move = safe_float(price_info.get("recent12_move_atr"), 0.0)
    recent3_move = safe_float(price_info.get("recent3_move_atr"), 0.0)
    down_ratio = safe_float(price_info.get("directional_down_ratio"), 0.0)
    up_ratio = safe_float(price_info.get("directional_up_ratio"), 0.0)
    efficiency = safe_float(price_info.get("trend_efficiency"), 0.0)
    price_structure = str(price_info.get("structure", "MIXED")).upper()

    bearish_movement = bool(
        session_move <= -0.15
        or recent12_move <= -0.20
        or (price_structure == "LH_LL" and down_ratio >= 0.45)
    )
    bullish_movement = bool(
        session_move >= 0.15
        or recent12_move >= 0.20
        or (price_structure == "HH_HL" and up_ratio >= 0.45)
    )

    bearish_environment = below_vwap and bearish_movement
    bullish_environment = above_vwap and bullish_movement
    bearish_base = below_vwap and bearish_flow_ok
    bullish_base = above_vwap and bullish_flow_ok

    strong_bullish_reversal = bool(
        above_vwap and bullish_flow_ok
        and (bool(price_info.get("bullish_structure")) or recent12_move >= 0.35)
        and (efficiency >= 0.20 or recent3_move >= 0.35)
    )
    strong_bearish_reversal = bool(
        below_vwap and bearish_flow_ok
        and (bool(price_info.get("bearish_structure")) or recent12_move <= -0.35)
        and (efficiency >= 0.20 or recent3_move <= -0.35)
    )

    carried_bearish = bearish_prior and bearish_base and not strong_bullish_reversal
    carried_bullish = bullish_prior and bullish_base and not strong_bearish_reversal

    support_is_authoritative = str(chain_levels.get("support_source", "")).upper() in {"OPTION_OI", "PERSISTED_OPTION_OI"}
    resistance_is_authoritative = str(chain_levels.get("resistance_source", "")).upper() in {"OPTION_OI", "PERSISTED_OPTION_OI"}

    # Preserve a crossed prior OI wall only as a breakout/breakdown reference.
    # It must never replace the current support/resistance used for targets.
    breakdown_reference = (
        previous_support
        if bearish_prior and math.isfinite(previous_support) and previous_support > price_reference
        else support_1
    )
    breakout_reference = (
        previous_resistance
        if bullish_prior and math.isfinite(previous_resistance) and previous_resistance < price_reference
        else resistance_1
    )
    below_support_bars = int(np.sum(work["close"].tail(max(STRUCTURE_HOLD_BARS, 2)).to_numpy(dtype=float) < breakdown_reference - break_buffer)) if math.isfinite(breakdown_reference) and not work.empty else 0
    above_resistance_bars = int(np.sum(work["close"].tail(max(STRUCTURE_HOLD_BARS, 2)).to_numpy(dtype=float) > breakout_reference + break_buffer)) if math.isfinite(breakout_reference) and not work.empty else 0

    fresh_bearish_break = bool(support_is_authoritative and math.isfinite(breakdown_reference) and below_vwap and current_close < breakdown_reference - break_buffer and below_support_bars >= max(1, STRUCTURE_HOLD_BARS) and bearish_flow_ok)
    fresh_bullish_break = bool(resistance_is_authoritative and math.isfinite(breakout_reference) and above_vwap and current_close > breakout_reference + break_buffer and above_resistance_bars >= max(1, STRUCTURE_HOLD_BARS) and bullish_flow_ok)

    bearish_level_ok = bool(support_is_authoritative and math.isfinite(support_1) and support_1 < price_reference)
    bullish_level_ok = bool(resistance_is_authoritative and math.isfinite(resistance_1) and resistance_1 > price_reference)

    continuous_bearish = bool(
        bearish_base and bearish_level_ok and not futures_conflict_bearish
        and (bearish_movement or carried_bearish or fresh_bearish_break)
        and not strong_bullish_reversal
    )
    continuous_bullish = bool(
        bullish_base and bullish_level_ok and not futures_conflict_bullish
        and (bullish_movement or carried_bullish or fresh_bullish_break)
        and not strong_bearish_reversal
    )

    if continuous_bearish and continuous_bullish:
        if effective_flow < 0:
            continuous_bullish = False
        elif effective_flow > 0:
            continuous_bearish = False
        else:
            continuous_bearish = continuous_bullish = False

    if continuous_bearish:
        direction, market_phase = "BEARISH", "CONTINUOUS_BEARISH"
        entry_confirmed, confirmation_state = True, "STRUCTURAL_CONTINUATION"
        interpretation = "CONTINUOUS BEARISH — BELOW VWAP + SUSTAINED DOWNWARD PRICE ACTION + BEARISH CHANGE-OI"
        scenario_trigger = f"NIFTY remains below VWAP with sustained bearish price action and bearish Change-OI; OI support={support_1:.2f} is the T1/breakdown reference when available."
        scenario_invalidation = "Invalidate bearish structure after sustained VWAP reclaim with opposing Change-OI and decisive bullish price structure; a small 3m bounce alone does not invalidate the trend."
    elif continuous_bullish:
        direction, market_phase = "BULLISH", "CONTINUOUS_BULLISH"
        entry_confirmed, confirmation_state = True, "STRUCTURAL_CONTINUATION"
        interpretation = "CONTINUOUS BULLISH — ABOVE VWAP + SUSTAINED UPWARD PRICE ACTION + BULLISH CHANGE-OI"
        scenario_trigger = f"NIFTY remains above VWAP with sustained bullish price action and bullish Change-OI; OI resistance={resistance_1:.2f} is the T1/breakout reference when available."
        scenario_invalidation = "Invalidate bullish structure after sustained VWAP loss with opposing Change-OI and decisive bearish price structure; a small 3m dip alone does not invalidate the trend."
    elif below_vwap and flow_conflict:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "FLOW_CONFLICT"
        interpretation = "BEARISH WATCH — BELOW VWAP BUT CHANGE-OI CONFLICTING"
        scenario_trigger = f"Wait for non-conflicting bearish Change-OI and sustained bearish price action; support={support_1:.2f}."
        scenario_invalidation = "Bearish watch weakens on sustained VWAP reclaim and bullish price structure."
    elif above_vwap and flow_conflict:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "FLOW_CONFLICT"
        interpretation = "BULLISH WATCH — ABOVE VWAP BUT CHANGE-OI CONFLICTING"
        scenario_trigger = f"Wait for non-conflicting bullish Change-OI and sustained bullish price action; resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish watch weakens on sustained VWAP loss and bearish price structure."
    elif below_vwap and bearish_flow_ok and futures_conflict_bearish:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "FUTURES_CONFLICT"
        interpretation = "BEARISH WATCH — PRICE/VWAP + CHANGE-OI BEARISH, BUT FUTURES OI IS BULLISH"
        scenario_trigger = f"Wait for futures price/OI to stop contradicting the bearish structure; support={support_1:.2f}."
        scenario_invalidation = "Do not open a bearish option while strong futures positioning remains bullish."
    elif above_vwap and bullish_flow_ok and futures_conflict_bullish:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "FUTURES_CONFLICT"
        interpretation = "BULLISH WATCH — PRICE/VWAP + CHANGE-OI BULLISH, BUT FUTURES OI IS BEARISH"
        scenario_trigger = f"Wait for futures price/OI to stop contradicting the bullish structure; resistance={resistance_1:.2f}."
        scenario_invalidation = "Do not open a bullish option while strong futures positioning remains bearish."
    elif below_vwap and bearish_flow_ok:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "STRUCTURAL_WATCH"
        interpretation = "BEARISH WATCH — BELOW VWAP + BEARISH CHANGE-OI, PRICE PERSISTENCE OR OI LEVEL NOT CONFIRMED"
        scenario_trigger = f"Wait for sustained bearish price action and valid OI support; support={support_1:.2f}."
        scenario_invalidation = "Bearish watch weakens on sustained VWAP reclaim with opposing price structure and Change-OI."
    elif above_vwap and bullish_flow_ok:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "STRUCTURAL_WATCH"
        interpretation = "BULLISH WATCH — ABOVE VWAP + BULLISH CHANGE-OI, PRICE PERSISTENCE OR OI LEVEL NOT CONFIRMED"
        scenario_trigger = f"Wait for sustained bullish price action and valid OI resistance; resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish watch weakens on sustained VWAP loss with opposing price structure and Change-OI."
    elif bearish_environment:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "FLOW_WAIT"
        interpretation = "BEARISH WATCH — PRICE/VWAP STRUCTURE DOWN, CHANGE-OI NOT CONFIRMING"
        scenario_trigger = f"Wait for bearish Change-OI confirmation; support={support_1:.2f}."
        scenario_invalidation = "Bearish watch weakens on sustained VWAP reclaim and bullish price structure."
    elif bullish_environment:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "FLOW_WAIT"
        interpretation = "BULLISH WATCH — PRICE/VWAP STRUCTURE UP, CHANGE-OI NOT CONFIRMING"
        scenario_trigger = f"Wait for bullish Change-OI confirmation; resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish watch weakens on sustained VWAP loss and bearish price structure."
    else:
        direction, market_phase = "NEUTRAL", "SIDEWAYS"
        entry_confirmed, confirmation_state = False, "NO_TRADE"
        interpretation = "SIDEWAYS / MIXED — NO STRUCTURAL DIRECTION CONFIRMED"
        scenario_trigger = f"Wait for VWAP-side alignment + sustained price action + confirming Change-OI; support={support_1:.2f} resistance={resistance_1:.2f}."
        scenario_invalidation = "No directional entry while VWAP, price action and Change-OI remain mixed."

    pcr = safe_float(chain_levels.get("pcr"), float("nan"))
    pcr_bias = 1 if math.isfinite(pcr) and pcr >= 1.10 else -1 if math.isfinite(pcr) and pcr <= 0.90 else 0
    structure_score = 8.0 if continuous_bullish else -8.0 if continuous_bearish else 2.0 if direction == "BULLISH" else -2.0 if direction == "BEARISH" else 0.0
    confidence = 95.0 if (continuous_bullish or continuous_bearish) else 72.0 if direction in {"BULLISH", "BEARISH"} else 40.0

    reasons = [
        f"PRIMARY: NIFTY={current_close:.2f} vs VWAP={vwap:.2f}; below_vwap={below_vwap}; above_vwap={above_vwap}.",
        f"PRICE ACTION: structure={price_structure}; session={session_move:+.2f}vol; recent12={recent12_move:+.2f}vol; recent3={recent3_move:+.2f}vol; down_ratio={down_ratio:.2f}; up_ratio={up_ratio:.2f}; efficiency={efficiency:.2f}.",
        f"CHANGE-OI: effective={effective_flow:+.3f}; bias={effective_bias:+d}; source={effective_source}; conflict={flow_conflict}.",
        f"OI STRUCTURE: support={support_1:.2f}/{support_2:.2f}; resistance={resistance_1:.2f}/{resistance_2:.2f}; breakdown_ref={breakdown_reference:.2f}; breakout_ref={breakout_reference:.2f}; breakdown={fresh_bearish_break}; breakout={fresh_bullish_break}.",
        f"FUTURES CONTEXT: regime={futures_regime}; bias={futures_bias:+d}; strength={futures_strength:.3f}; conflict_bearish={futures_conflict_bearish}; conflict_bullish={futures_conflict_bullish}.",
        f"ENTRY GATES: bearish_level_ok={bearish_level_ok}; bullish_level_ok={bullish_level_ok}; minimum_entry_change_oi={STRUCTURE_CHANGE_OI_STRONG:.3f}.",
        f"PCR CONTEXT: value={pcr:.3f}; bias={pcr_bias:+d}." if math.isfinite(pcr) else "PCR CONTEXT: unavailable from current chain.",
    ]

    logger.info(
        "STRUCTURE ENGINE: phase=%s direction=%s price=%.2f VWAP=%.2f support=%s resistance=%s ChangeOI=%+.3f "
        "breakout=%s breakdown=%s Entry=%s",
        market_phase, direction, current_close, vwap,
        f"{support_1:.2f}" if math.isfinite(support_1) else "NA",
        f"{resistance_1:.2f}" if math.isfinite(resistance_1) else "NA",
        effective_flow, fresh_bullish_break, fresh_bearish_break, entry_confirmed,
    )

    components = {
        "structure_change_oi": float(effective_flow),
        "structure_change_oi_intraday_raw": float(raw_intraday_flow),
        "structure_change_oi_day_raw": float(change_oi_score),
        "structure_change_oi_conflict": 1.0 if flow_conflict else 0.0,
        "structure_change_oi_source": effective_source,
        "structure_futures_conflict_bullish": 1.0 if futures_conflict_bullish else 0.0,
        "structure_futures_conflict_bearish": 1.0 if futures_conflict_bearish else 0.0,
        "structure_vwap": 1.0 if above_vwap else -1.0 if below_vwap else 0.0,
        "structure_price_break": 1.0 if fresh_bullish_break else -1.0 if fresh_bearish_break else 0.0,
        "structure_score": float(structure_score),
        "intraday_trend": float(latest_move / volatility_unit),
        "vwap_level": 1.0 if above_vwap else -1.0 if below_vwap else 0.0,
        "recent3_movement_atr": float(recent3_move),
        "price_session_atr": float(session_move),
        "price_recent12_atr": float(recent12_move),
        "price_directional_down_ratio": float(down_ratio),
        "price_directional_up_ratio": float(up_ratio),
        "price_trend_efficiency": float(efficiency),
        "price_structure": 1.0 if price_structure == "HH_HL" else -1.0 if price_structure == "LH_LL" else 0.0,
        "vwap_distance_atr": float(abs(current_close - vwap) / volatility_unit) if math.isfinite(vwap) else float("inf"),
        "volatility_unit": float(volatility_unit),
        "active_structure_level": float(support_1 if direction == "BEARISH" else resistance_1 if direction == "BULLISH" else float("nan")),
    }

    return StructureResult(
        direction=direction, score=float(structure_score), confidence=float(confidence), interpretation=interpretation,
        components=components, vwap=float(vwap), vwap_slope=float(vwap_slope),
        futures_regime=futures_regime, futures_bias=futures_bias, futures_oi_strength=futures_strength,
        futures_oi_persistence=float(futures_info.get("oi_persistence", 0.0)),
        futures_live_oi_change=float(futures_info.get("live_oi_change", float("nan"))),
        intraday_bias=1 if latest_move > 0 else -1 if latest_move < 0 else 0,
        intraday_strength=float(min(abs(latest_move) / volatility_unit, 1.0)),
        intraday_score=float(latest_move / volatility_unit),
        chain_predictive_bias=int(chain_levels.get("predictive_bias", effective_bias)),
        chain_predictive_strength=float(chain_levels.get("predictive_strength", abs(effective_flow))),
        chain_level_bias=int(chain_levels.get("level_bias", 0)),
        support_strength=float(chain_levels.get("support_strength", 0.0)),
        resistance_strength=float(chain_levels.get("resistance_strength", 0.0)),
        support_change_strength=float(chain_levels.get("support_change_strength", 0.0)),
        resistance_change_strength=float(chain_levels.get("resistance_change_strength", 0.0)),
        support_1=float(support_1), support_2=float(support_2),
        resistance_1=float(resistance_1), resistance_2=float(resistance_2),
        market_phase=market_phase, entry_confirmed=bool(entry_confirmed), reversal_confirmations=0,
        confirmation_state=confirmation_state, pcr=pcr if math.isfinite(pcr) else float("nan"),
        pcr_bias=int(pcr_bias), false_breakout=False, trap_level=0.0,
        entry_trigger=scenario_trigger, invalidation_rule=scenario_invalidation, reasons=reasons,
    )
# OPTION SELECTION
# =============================================================================



def build_option_candidate(
    contract_meta: dict[str, Any],
    chain_data: dict[str, Any],
) -> OptionCandidate:
    # Accept either the wrapped contract-lookup object or raw option-side data.
    data = chain_data.get("data", chain_data)

    ltp = safe_float(data["ltp"])
    bid = safe_float(data["bid"])
    ask = safe_float(data["ask"])

    if ltp <= 0:
        raise ScannerError("Option LTP is invalid.")

    if bid > 0 and ask > 0 and ask >= bid:
        mid = (bid + ask) / 2.0
        spread_pct = (ask - bid) / mid if mid > 0 else 1.0
    else:
        spread_pct = 1.0

    theta = safe_float(data["theta"])
    theta_burden = abs(theta) / ltp if ltp > 0 else float("inf")

    delta = safe_float(data["delta"], float("nan"))
    if not math.isfinite(delta):
        raise ScannerError("Option delta unavailable.")

    return OptionCandidate(
        instrument_key=str(data["instrument_key"]),
        trading_symbol=str(
            data.get("trading_symbol")
            or contract_meta.get("trading_symbol")
            or data["instrument_key"]
        ),
        option_type=str(contract_meta["type"]),
        strike=float(contract_meta["strike"]),
        expiry=str(contract_meta["expiry"]),
        ltp=ltp,
        oi=safe_float(data["oi"]),
        prev_oi=safe_float(data["prev_oi"]),
        volume=safe_float(data["volume"]),
        bid=bid,
        ask=ask,
        bid_qty=safe_float(data["bid_qty"]),
        ask_qty=safe_float(data["ask_qty"]),
        delta=delta,
        theta=theta,
        spread_pct=spread_pct,
        theta_burden_pct_day=theta_burden,
        premium_vwap=safe_float(data.get("premium_vwap"), float("nan")),
    )


def option_health_score(
    option: OptionCandidate,
    atm: float,
    step: float,
) -> float:
    delta_abs = abs(option.delta)
    delta_score = max(
        0.0,
        1.0 - abs(delta_abs - 0.55) / 0.30,
    )

    spread_score = max(0.0, 1.0 - option.spread_pct / MAX_SPREAD_PCT)
    intraday_theta_burden = (
        option.theta_burden_pct_day
        * EXPECTED_HOLDING_MINUTES
        / 375.0
    )
    # Soft theta penalty: higher expected time-decay lowers the health score,
    # but does not make the candidate ineligible by itself. The formula is
    # monotonic and bounded, so even expiry-day options remain selectable when
    # the underlying, spread, liquidity and delta filters are healthy.
    theta_score = 1.0 / (1.0 + intraday_theta_burden / THETA_WARNING_BURDEN)

    liquidity_base = math.log1p(max(option.volume, 0.0))
    oi_base = math.log1p(max(option.oi, 0.0))
    liquidity_score = min(1.0, (liquidity_base + oi_base) / 20.0)

    distance_steps = abs(option.strike - atm) / step if step > 0 else 0.0
    distance_score = 1.0 if distance_steps <= 0.5 else 0.65 if distance_steps <= 1.0 else 0.20

    return (
        0.30 * delta_score
        + 0.30 * spread_score
        + 0.20 * theta_score
        + 0.15 * liquidity_score
        + 0.05 * distance_score
    )


def select_directional_option(
    chain: list[dict[str, Any]],
    direction: str,
    spot: float,
    *,
    target_underlying_1: Optional[float] = None,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
    market_intensity: str = "NORMAL",
    is_expiry_day: bool = False,
    now: Optional[datetime] = None,
    option_metrics_by_instrument: Optional[dict[str, dict[str, float]]] = None,
    oi_velocity_by_strike: Optional[dict[float, dict[str, Any]]] = None,
) -> OptionCandidate:
    """Select a strike using regime routing + strict option VWAP/COI/delta gates."""
    direction = str(direction).upper()
    intensity = str(market_intensity).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Option selection requires BULLISH or BEARISH.")
    if intensity in {"SIDEWAYS", "UNKNOWN"}:
        raise ScannerError(f"Directional option buying blocked for intensity={intensity}.")

    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    atm_distance_steps = abs(atm - spot) / max(step, 1.0)
    if atm_distance_steps > 1.25:
        raise ScannerError(
            f"ATM strike sanity check failed: index spot={spot:.2f}, nearest strike={atm:.0f}, "
            f"step={step:.0f} ({atm_distance_steps:.2f} steps away)."
        )

    permitted_list = [round(float(x), 2) for x in permitted_strikes_for_regime(
        atm, step, direction, intensity, is_expiry_day=is_expiry_day, now=now
    )]
    if not permitted_list:
        raise ScannerError(f"No permitted strikes for {direction}/{intensity} at this time of day.")
    option_type = "CE" if direction == "BULLISH" else "PE"
    metrics = option_metrics_by_instrument if isinstance(option_metrics_by_instrument, dict) else {}
    velocity_map = oi_velocity_by_strike if isinstance(oi_velocity_by_strike, dict) else {}
    flow_map = change_oi_by_strike if isinstance(change_oi_by_strike, dict) else {}
    tod = time_of_day_window(now)
    max_spread = min(MAX_SPREAD_PCT, OPENING_MAX_SPREAD_PCT) if tod == "OPENING" else MAX_SPREAD_PCT

    eligible: list[tuple[float, OptionCandidate, bool]] = []
    rejection_log: list[str] = []
    score_by_strike: dict[float, float] = {}
    for target in permitted_list:
        row_key = min(strikes, key=lambda value: abs(value - target))
        if abs(row_key - target) > 0.01:
            rejection_log.append(f"{option_type} {target:.0f}: strike absent from chain")
            continue
        data = option_side_data(rows[row_key], option_type)
        instrument_key = str(data.get("instrument_key") or "").strip()
        if not instrument_key:
            rejection_log.append(f"{option_type} {row_key:.0f}: no instrument key")
            continue
        ltp = safe_float(data.get("ltp"), 0.0)
        if ltp <= 0:
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid LTP")
            continue
        if safe_float(data.get("oi"), 0.0) < MIN_OI or safe_float(data.get("volume"), 0.0) < MIN_VOLUME:
            rejection_log.append(f"{option_type} {row_key:.0f}: insufficient OI/volume")
            continue

        micro = metrics.get(instrument_key, {}) if isinstance(metrics, dict) else {}
        premium_vwap = safe_float(micro.get("premium_vwap"), float("nan")) if isinstance(micro, dict) else float("nan")
        if not math.isfinite(premium_vwap) or premium_vwap <= 0:
            rejection_log.append(f"{option_type} {row_key:.0f}: own premium VWAP unavailable")
            continue
        if ltp <= premium_vwap:
            rejection_log.append(f"{option_type} {row_key:.0f}: LTP {ltp:.2f} <= premium VWAP {premium_vwap:.2f}")
            continue

        delta = safe_float(data.get("delta"), float("nan"))
        if not math.isfinite(delta) or abs(delta) > 1.0 or abs(delta) <= 0.0:
            rejection_log.append(f"{option_type} {row_key:.0f}: valid live delta unavailable")
            continue
        delta_abs = abs(delta)
        if intensity == "EXHAUSTION":
            delta_floor = 0.75
        elif is_expiry_day or intensity != "STRONG":
            delta_floor = 0.50
        else:
            delta_floor = 0.0
        if delta_abs < delta_floor:
            rejection_log.append(f"{option_type} {row_key:.0f}: delta {delta_abs:.3f} below floor {delta_floor:.2f}")
            continue

        bid = safe_float(data.get("bid"), 0.0)
        ask = safe_float(data.get("ask"), 0.0)
        if bid <= 0 or ask <= 0 or ask < bid:
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid bid/ask")
            continue
        mid = (bid + ask) / 2.0
        spread_pct = (ask - bid) / mid if mid > 0 else 1.0
        if spread_pct > max_spread:
            rejection_log.append(f"{option_type} {row_key:.0f}: spread {spread_pct:.2%} > {max_spread:.2%}")
            continue

        velocity = velocity_map.get(float(row_key), {}) if isinstance(velocity_map, dict) else {}
        if not isinstance(velocity, dict) or not bool(velocity.get("available")):
            rejection_log.append(f"{option_type} {row_key:.0f}: 15-30 minute OI velocity baseline unavailable")
            continue
        call_pct = safe_float(velocity.get("call_oi_change_pct"), float("nan"))
        put_pct = safe_float(velocity.get("put_oi_change_pct"), float("nan"))
        baseline_minutes = safe_float(velocity.get("baseline_minutes"), float("nan"))
        if not (math.isfinite(call_pct) and math.isfinite(put_pct) and
                OPTION_OI_MIN_AGE_MINUTES <= baseline_minutes <= OPTION_OI_MAX_AGE_MINUTES):
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid 15-30 minute OI velocity data")
            continue

        strike_flow = flow_map.get(float(row_key), {})
        call_bias = int(safe_float(strike_flow.get("call_bias"), 0))
        put_bias = int(safe_float(strike_flow.get("put_bias"), 0))
        desired_bias = 1 if direction == "BULLISH" else -1
        selected_bias = call_bias if option_type == "CE" else put_bias
        other_bias = put_bias if option_type == "CE" else call_bias
        normalized_flow_bias = 1 if selected_bias == desired_bias else -1 if selected_bias == -desired_bias else 0
        if normalized_flow_bias == 1:
            flow_score = 1.0
        elif selected_bias == 0 and other_bias == desired_bias:
            flow_score = 0.80
        elif selected_bias == -desired_bias and other_bias == desired_bias:
            flow_score = 0.50
        elif selected_bias == 0 and other_bias == 0:
            flow_score = 0.50
        else:
            # Conflicting flow lowers this component but does not erase the other valid score components.
            flow_score = 0.10

        if direction == "BULLISH":
            unwind_pct, adding_pct = max(-call_pct, 0.0), max(put_pct, 0.0)
        else:
            unwind_pct, adding_pct = max(-put_pct, 0.0), max(call_pct, 0.0)
        coi_score = 0.5 * min(unwind_pct / max(COI_STRONG_CHANGE_PCT, 1e-6), 1.0) + 0.5 * min(
            adding_pct / max(COI_STRONG_CHANGE_PCT, 1e-6), 1.0
        )

        if option_type == "CE":
            moneyness = "ITM" if row_key < atm - 0.01 else "ATM" if abs(row_key - atm) <= 0.01 else "OTM"
        else:
            moneyness = "ITM" if row_key > atm + 0.01 else "ATM" if abs(row_key - atm) <= 0.01 else "OTM"
        moneyness_multiplier = {"ITM": 1.0, "ATM": 0.85, "OTM": 0.65}[moneyness]
        delta_weight = moneyness_multiplier * min(delta_abs / 0.75, 1.0)
        premium_lift_pct = max((ltp - premium_vwap) / premium_vwap, 0.0)
        vwap_score = 0.50 + 0.50 * min(premium_lift_pct / 0.02, 1.0)
        total = flow_score + vwap_score + coi_score + delta_weight

        theta = safe_float(data.get("theta"), 0.0)
        theta_burden = abs(theta) / ltp if ltp > 0 else float("inf")
        meta = {"strike": row_key, "type": option_type,
                "expiry": str(rows[row_key].get("expiry", ""))[:10]}
        data["premium_vwap"] = premium_vwap
        candidate = build_option_candidate(meta, data)
        candidate = replace(
            candidate,
            flow_score=flow_score,
            vwap_score=vwap_score,
            oi_momentum_score=coi_score,
            delta_weight=delta_weight,
            call_oi_change_pct_15m=call_pct * 100.0,
            put_oi_change_pct_15m=put_pct * 100.0,
            oi_velocity_baseline_minutes=baseline_minutes,
            market_intensity=intensity,
        )
        eligible.append((total, candidate, moneyness == "OTM"))
        score_by_strike[row_key] = total
        logger.info(
            "STRIKE RANK: %s %.0f regime=%s moneyness=%s total=%.3f flow=%.3f vwap=%.3f "
            "coi_velocity=%.3f delta_weight=%.3f delta=%.3f premium_ltp=%.2f premium_vwap=%.2f "
            "call_coi15m=%+.2f%% put_coi15m=%+.2f%% baseline=%.1fm flow_bias=%+d spread=%.2f%%",
            option_type, row_key, intensity, moneyness, total, flow_score, vwap_score, coi_score,
            delta_weight, delta, ltp, premium_vwap, call_pct * 100.0, put_pct * 100.0,
            baseline_minutes, normalized_flow_bias, spread_pct * 100.0,
        )

    if not eligible:
        detail = "; ".join(rejection_log[-10:]) or "no valid candidates"
        raise ScannerError(f"No eligible {direction}/{intensity} option. {detail}")

    eligible.sort(key=lambda item: (-item[0], item[1].strike))
    winning_score, selected, winner_is_otm = eligible[0]
    if winner_is_otm and winning_score > 0:
        safer = [item for item in eligible if not item[2] and item[0] >= winning_score * 0.95]
        if safer:
            safer.sort(key=lambda item: (-item[0], item[1].strike))
            safer_score, safer_candidate, _ = safer[0]
            logger.info(
                "THETA SAFETY OVERRIDE: OTM winner %.0f score=%.3f replaced by safer %s %.0f score=%.3f (within 5%%).",
                selected.strike, winning_score, safer_candidate.option_type, safer_candidate.strike, safer_score,
            )
            selected = safer_candidate
            winning_score = safer_score

    permitted = {round(x, 2) for x in permitted_list}
    if round(selected.strike, 2) not in permitted:
        raise ScannerError(
            f"STRICT STRIKE VALIDATION FAILED: direction={direction} intensity={intensity} "
            f"ATM={atm:.2f} step={step:.2f} selected={selected.strike:.2f} permitted={sorted(permitted)}"
        )
    expected_type = "CE" if direction == "BULLISH" else "PE"
    if selected.option_type != expected_type:
        raise ScannerError(f"STRICT STRIKE VALIDATION FAILED: {direction} requires {expected_type}.")
    logger.info(
        "OPTION SELECT: direction=%s intensity=%s tod=%s expiry_day=%s ATM=%.0f permitted=%s "
        "selected=%s %.0f total=%.3f LTP=%.2f option_VWAP=%.2f delta=%.3f flow=%.3f VWAPscore=%.3f "
        "COIscore=%.3f delta_weight=%.3f call_COI15m=%+.2f%% put_COI15m=%+.2f%% baseline=%.1fm",
        direction, intensity, tod, is_expiry_day, atm, sorted(permitted), selected.option_type,
        selected.strike, winning_score, selected.ltp, selected.premium_vwap, selected.delta,
        selected.flow_score, selected.vwap_score, selected.oi_momentum_score, selected.delta_weight,
        selected.call_oi_change_pct_15m, selected.put_oi_change_pct_15m,
        selected.oi_velocity_baseline_minutes,
    )
    return selected


def validate_continuous_option_entry(
    option: OptionCandidate,
    chain: list[dict[str, Any]],
    direction: str,
    market_phase: str,
    spot: float,
    *,
    market_intensity: str = "NORMAL",
    is_expiry_day: bool = False,
    now: Optional[datetime] = None,
) -> None:
    """Final pre-signal invariant for contract type, regime routing and hard risk filters."""
    phase = str(market_phase or "").upper()
    if phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"} and not phase.startswith("EXHAUSTION_"):
        return
    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    permitted = {
        round(float(x), 2) for x in permitted_strikes_for_regime(
            atm, step, direction, market_intensity, is_expiry_day=is_expiry_day, now=now
        )
    }
    selected_strike = round(float(option.strike), 2)
    if selected_strike not in permitted:
        raise ScannerError(
            f"PRE-EMAIL STRIKE VALIDATION FAILED: {direction}/{market_intensity} "
            f"requires {sorted(permitted)} but selected {selected_strike:.2f}."
        )
    expected_type = "CE" if direction == "BULLISH" else "PE"
    if option.option_type != expected_type:
        raise ScannerError(f"PRE-EMAIL OPTION TYPE VALIDATION FAILED: {direction} requires {expected_type}.")
    exact_row = rows.get(selected_strike)
    if exact_row is None:
        raise ScannerError(f"PRE-EMAIL CHAIN VALIDATION FAILED: strike {selected_strike:.2f} absent from live chain.")
    side = option_side_data(exact_row, expected_type)
    live_key = str(side.get("instrument_key") or "")
    if not live_key or live_key != option.instrument_key:
        raise ScannerError("PRE-EMAIL INSTRUMENT VALIDATION FAILED: selected key does not match live chain.")
    live_ltp = safe_float(side.get("ltp"), 0.0)
    if live_ltp <= 0 or not math.isfinite(option.premium_vwap) or live_ltp <= option.premium_vwap:
        raise ScannerError("PRE-EMAIL PREMIUM VWAP VALIDATION FAILED: live LTP must be above valid option VWAP.")
    delta_floor = 0.75 if market_intensity == "EXHAUSTION" else 0.50 if (is_expiry_day or market_intensity != "STRONG") else 0.0
    if abs(option.delta) < delta_floor:
        raise ScannerError(f"PRE-EMAIL DELTA VALIDATION FAILED: |delta|={abs(option.delta):.3f} < {delta_floor:.2f}.")
    logger.info(
        "STRICT STRIKE VALIDATION PASSED: direction=%s phase=%s intensity=%s ATM=%.0f step=%.0f "
        "selected=%s %.0f permitted=%s premium_LTP=%.2f premium_VWAP=%.2f delta=%.3f",
        direction, phase, market_intensity, atm, step, expected_type, selected_strike,
        sorted(permitted), live_ltp, option.premium_vwap, option.delta,
    )


# =============================================================================
# AUTHORITATIVE PA/OI TRADE LEVEL ENGINE
# =============================================================================


def _completed_price_action_frame(
    price_session: Optional[pd.DataFrame],
) -> pd.DataFrame:
    if price_session is None or price_session.empty:
        return pd.DataFrame()
    work = filter_completed_candles(price_session.copy(), 3)
    if work.empty:
        return work
    work = work.sort_values("timestamp").copy()
    for column in ("open", "high", "low", "close"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    return work.dropna(subset=["high", "low", "close"])


def _price_action_swings(
    price_session: Optional[pd.DataFrame],
    *,
    lookback: int = PA_OI_SWING_LOOKBACK,
) -> dict[str, list[float]]:
    """Return recent completed 3m swing levels without ATR-derived targets."""
    work = _completed_price_action_frame(price_session)
    if work.empty:
        return {"highs": [], "lows": []}
    work = work.tail(max(int(lookback), 5)).reset_index(drop=True)

    swing_highs: list[float] = []
    swing_lows: list[float] = []
    for i in range(1, len(work) - 1):
        high_i = safe_float(work.loc[i, "high"], float("nan"))
        low_i = safe_float(work.loc[i, "low"], float("nan"))
        prev_high = safe_float(work.loc[i - 1, "high"], float("nan"))
        next_high = safe_float(work.loc[i + 1, "high"], float("nan"))
        prev_low = safe_float(work.loc[i - 1, "low"], float("nan"))
        next_low = safe_float(work.loc[i + 1, "low"], float("nan"))
        if math.isfinite(high_i) and high_i >= prev_high and high_i >= next_high:
            swing_highs.append(high_i)
        if math.isfinite(low_i) and low_i <= prev_low and low_i <= next_low:
            swing_lows.append(low_i)

    # Include the latest completed extreme as price-action context even when it
    # is not a textbook pivot. This prevents a flat series from returning no PA level.
    if not swing_highs:
        latest_high = safe_float(work["high"].max(), float("nan"))
        if math.isfinite(latest_high):
            swing_highs.append(latest_high)
    if not swing_lows:
        latest_low = safe_float(work["low"].min(), float("nan"))
        if math.isfinite(latest_low):
            swing_lows.append(latest_low)

    return {
        "highs": sorted({round(x, 2) for x in swing_highs if math.isfinite(x)}),
        "lows": sorted({round(x, 2) for x in swing_lows if math.isfinite(x)}),
    }


def _rank_current_oi_walls(
    chain: list[dict[str, Any]],
    spot: float,
    *,
    side: str,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> list[dict[str, Any]]:
    """Return current OI walls with OI as the primary ranking variable.

    This is deliberately not a weighted multi-factor market vote. OI
    concentration determines the wall; distance and Change-OI are tie-breakers.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows)
    if not strikes:
        return []
    step = max(strike_step(strikes), 1.0)
    candidates: list[dict[str, Any]] = []

    for strike, row in rows.items():
        distance_steps = abs(float(strike) - float(spot)) / step
        if distance_steps < PA_OI_TARGET_MIN_STEPS:
            continue
        if side == "support":
            if float(strike) >= float(spot):
                continue
            option_type = "PE"
            option = option_side_data(row, option_type)
            oi = max(safe_float(option.get("oi")), 0.0)
            flow = (change_oi_by_strike or {}).get(float(strike), {})
            flow_change = safe_float(flow.get("put_oi_change"), 0.0)
            flow_bias = int(flow.get("put_bias", 0)) or (1 if flow_change > 0 else -1 if flow_change < 0 else 0)
        else:
            if float(strike) <= float(spot):
                continue
            option_type = "CE"
            option = option_side_data(row, option_type)
            oi = max(safe_float(option.get("oi")), 0.0)
            flow = (change_oi_by_strike or {}).get(float(strike), {})
            flow_change = safe_float(flow.get("call_oi_change"), 0.0)
            flow_bias = int(flow.get("call_bias", 0)) or (1 if flow_change > 0 else -1 if flow_change < 0 else 0)
        if oi <= 0:
            continue
        candidates.append({
            "strike": float(strike),
            "oi": float(oi),
            "flow_bias": int(flow_bias),
            "flow_change": float(flow_change),
            "option_type": option_type,
            "distance_steps": float(distance_steps),
        })

    if not candidates:
        return []
    max_oi = max(x["oi"] for x in candidates)
    median_oi = float(np.median([x["oi"] for x in candidates]))
    for item in candidates:
        item["oi_ratio"] = float(item["oi"] / max(max_oi, 1.0))
        item["meaningful"] = bool(
            item["oi_ratio"] >= PA_OI_SECONDARY_OI_RATIO
            or item["oi"] >= median_oi
        )
        item["strength"] = item["oi_ratio"]

    return sorted(
        candidates,
        key=lambda x: (-float(x["oi"]), float(x["distance_steps"]), -abs(float(x["flow_change"])), float(x["strike"])),
    )


def _initial_structural_stop(
    spot: float,
    direction: str,
    price_action: dict[str, list[float]],
    opposing_walls: list[dict[str, Any]],
    strike_step_value: float,
) -> tuple[float, str]:
    """Set the pre-T1 SL beyond the PA/OI invalidation structures."""
    buffer = max(0.10, strike_step_value * PA_OI_STOP_BUFFER_STEPS)
    if direction == "BEARISH":
        pa = min([x for x in price_action.get("highs", []) if x > spot], default=float("nan"))
        oi = min([float(x["strike"]) for x in opposing_walls if float(x["strike"]) > spot], default=float("nan"))
        if math.isfinite(pa) and math.isfinite(oi):
            return min(pa, oi) + buffer, "PRICE_ACTION_AND_OI_RESISTANCE"
        if math.isfinite(pa):
            return pa + buffer, "PRICE_ACTION_SWING_HIGH"
        if math.isfinite(oi):
            return oi + buffer, "OI_RESISTANCE"
        raise ScannerError("No bearish PA/OI invalidation level available.")

    pa = max([x for x in price_action.get("lows", []) if x < spot], default=float("nan"))
    oi = max([float(x["strike"]) for x in opposing_walls if float(x["strike"]) < spot], default=float("nan"))
    if math.isfinite(pa) and math.isfinite(oi):
        return max(pa, oi) - buffer, "PRICE_ACTION_AND_OI_SUPPORT"
    if math.isfinite(pa):
        return pa - buffer, "PRICE_ACTION_SWING_LOW"
    if math.isfinite(oi):
        return oi - buffer, "OI_SUPPORT"
    raise ScannerError("No bullish PA/OI invalidation level available.")


def determine_structural_trade_levels(
    chain: list[dict[str, Any]],
    spot: float,
    structure: StructureResult,
    price_session: Optional[pd.DataFrame],
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> tuple[float, float, float, dict[str, Any]]:
    """Determine authoritative NIFTY T1/T2/SL strictly from price action + OI."""
    direction = str(structure.direction).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Structural trade levels require BULLISH or BEARISH direction.")

    rows = chain_rows(chain)
    step = strike_step(sorted(rows))
    swings = _price_action_swings(price_session)

    support_walls = _rank_current_oi_walls(
        chain, spot, side="support", change_oi_by_strike=change_oi_by_strike,
    )
    resistance_walls = _rank_current_oi_walls(
        chain, spot, side="resistance", change_oi_by_strike=change_oi_by_strike,
    )

    if direction == "BEARISH":
        target_walls = [x for x in support_walls if bool(x["meaningful"])] or support_walls
        if not target_walls:
            raise ScannerError("No meaningful OI support exists for bearish T1/T2.")

        # T1 is the first usable OI support in the direction of travel. If the
        # scanner's authoritative support_1 has already been broken, it must not
        # become a stale target; move to the next current OI wall below spot.
        t1 = safe_float(structure.support_1, float("nan"))
        if not math.isfinite(t1) or t1 >= spot:
            ahead = sorted(
                [x for x in target_walls if float(x["strike"]) < spot],
                key=lambda x: (float(spot) - float(x["strike"]), -float(x["strength"])),
            )
            if not ahead:
                raise ScannerError("No current OI support below spot for bearish T1.")
            t1 = float(ahead[0]["strike"])
        else:
            # Protect against a malformed structure object that points to a
            # level absent from the current chain. In that case use the nearest
            # current OI support rather than inventing a level.
            matching_t1 = [x for x in target_walls if abs(float(x["strike"]) - t1) <= 0.01]
            if not matching_t1:
                ahead = sorted(
                    [x for x in target_walls if float(x["strike"]) < spot],
                    key=lambda x: (float(spot) - float(x["strike"]), -float(x["strength"])),
                )
                if not ahead:
                    raise ScannerError("No current OI support below spot for bearish T1.")
                t1 = float(ahead[0]["strike"])

        # T2 is the next distinct lower OI wall; PA is a fallback only when no
        # second OI wall exists.
        deeper = [x for x in support_walls if float(x["strike"]) < t1]
        pa_lows = sorted([x for x in swings.get("lows", []) if x < t1 - 0.01], reverse=True)
        oi_t2 = sorted([float(x["strike"]) for x in deeper], reverse=True)
        if oi_t2:
            t2 = oi_t2[0]
        elif pa_lows:
            t2 = pa_lows[0]
        else:
            raise ScannerError("No second price-action/OI downside objective exists for bearish trade.")
        stop_walls = ([{"strike": float(structure.resistance_1)}] if math.isfinite(safe_float(structure.resistance_1, float("nan"))) and structure.resistance_1 > spot else resistance_walls)
        stop_u, stop_source = _initial_structural_stop(
            spot, direction, swings, stop_walls, step,
        )
        meta = {
            "t1_source": "OPTION_OI_SUPPORT",
            "t2_source": "OPTION_OI_SUPPORT" if deeper else "PRICE_ACTION_SWING_LOW",
            "sl_source": stop_source,
            "t1_oi": target_walls[0]["oi"],
            "t2_oi": next((x["oi"] for x in deeper if float(x["strike"]) == t2), 0.0),
            "price_action_swing": swings,
            "t1_oi_wall_count": len(target_walls),
        }
        return float(t1), float(t2), float(stop_u), meta

    target_walls = [x for x in resistance_walls if bool(x["meaningful"])] or resistance_walls
    if not target_walls:
        raise ScannerError("No meaningful OI resistance exists for bullish T1/T2.")

    # T1 is the first usable OI resistance in the direction of travel. If the
    # authoritative resistance_1 has already been broken, use the next current
    # OI wall above spot instead of retaining the stale broken level.
    t1 = safe_float(structure.resistance_1, float("nan"))
    if not math.isfinite(t1) or t1 <= spot:
        ahead = sorted(
            [x for x in target_walls if float(x["strike"]) > spot],
            key=lambda x: (float(x["strike"]) - float(spot), -float(x["strength"])),
        )
        if not ahead:
            raise ScannerError("No current OI resistance above spot for bullish T1.")
        t1 = float(ahead[0]["strike"])
    else:
        matching_t1 = [x for x in target_walls if abs(float(x["strike"]) - t1) <= 0.01]
        if not matching_t1:
            ahead = sorted(
                [x for x in target_walls if float(x["strike"]) > spot],
                key=lambda x: (float(x["strike"]) - float(spot), -float(x["strength"])),
            )
            if not ahead:
                raise ScannerError("No current OI resistance above spot for bullish T1.")
            t1 = float(ahead[0]["strike"])

    # T2 is the next distinct higher OI wall; PA is a fallback only when no
    # second OI wall exists.
    higher = [x for x in resistance_walls if float(x["strike"]) > t1]
    pa_highs = sorted([x for x in swings.get("highs", []) if x > t1 + 0.01])
    oi_t2 = sorted([float(x["strike"]) for x in higher])
    t2 = oi_t2[0] if oi_t2 else (pa_highs[0] if pa_highs else float("nan"))
    if not math.isfinite(t2):
        raise ScannerError("No second price-action/OI upside objective exists for bullish trade.")
    stop_walls = ([{"strike": float(structure.support_1)}] if math.isfinite(safe_float(structure.support_1, float("nan"))) and structure.support_1 < spot else support_walls)
    stop_u, stop_source = _initial_structural_stop(
        spot, direction, swings, stop_walls, step,
    )
    meta = {
        "t1_source": "OPTION_OI_RESISTANCE",
        "t2_source": "OPTION_OI_RESISTANCE" if higher else "PRICE_ACTION_SWING_HIGH",
        "sl_source": stop_source,
        "t1_oi": target_walls[0]["oi"],
        "t2_oi": next((x["oi"] for x in higher if float(x["strike"]) == t2), 0.0),
        "price_action_swing": swings,
        "t1_oi_wall_count": len(target_walls),
    }
    return float(t1), float(t2), float(stop_u), meta


def dynamic_oi_stop_after_t1(
    chain: list[dict[str, Any]],
    spot: float,
    direction: str,
    price_session: Optional[pd.DataFrame],
    entry_underlying: Optional[float] = None,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> tuple[float, str, float]:
    """Use the CURRENT opposing OI wall as the post-T1 structural stop."""
    direction = str(direction).upper()
    rows = chain_rows(chain)
    step = strike_step(sorted(rows))
    swings = _price_action_swings(price_session)

    walls = _rank_current_oi_walls(
        chain, spot,
        side="resistance" if direction == "BEARISH" else "support",
        change_oi_by_strike=change_oi_by_strike,
    )
    meaningful = [x for x in walls if bool(x["meaningful"])] or walls
    if direction == "BEARISH":
        entry_u = safe_float(entry_underlying, float("nan"))
        favorable = [
            x for x in meaningful
            if float(x["strike"]) > spot
            and (not math.isfinite(entry_u) or float(x["strike"]) < entry_u)
        ]
        oi_pool = favorable or [x for x in meaningful if float(x["strike"]) > spot]
        oi_pool = sorted(
            oi_pool,
            key=lambda x: (float(x["strike"]) - float(spot), -float(x["strength"]), -abs(float(x.get("flow_change", 0.0)))),
        )
        oi_stop = float(oi_pool[0]["strike"]) if oi_pool else float("nan")
        pa_stop = min([x for x in swings.get("highs", []) if x > spot], default=float("nan"))
        if math.isfinite(oi_stop):
            return float(oi_stop), "CURRENT_OI_RESISTANCE", float(step)
        if math.isfinite(pa_stop):
            return float(pa_stop), "CURRENT_PRICE_ACTION_SWING_HIGH", float(step)
    else:
        entry_u = safe_float(entry_underlying, float("nan"))
        favorable = [
            x for x in meaningful
            if float(x["strike"]) < spot
            and (not math.isfinite(entry_u) or float(x["strike"]) > entry_u)
        ]
        oi_pool = favorable or [x for x in meaningful if float(x["strike"]) < spot]
        oi_pool = sorted(
            oi_pool,
            key=lambda x: (float(spot) - float(x["strike"]), -float(x["strength"]), -abs(float(x.get("flow_change", 0.0)))),
        )
        oi_stop = float(oi_pool[0]["strike"]) if oi_pool else float("nan")
        pa_stop = max([x for x in swings.get("lows", []) if x < spot], default=float("nan"))
        if math.isfinite(oi_stop):
            return float(oi_stop), "CURRENT_OI_SUPPORT", float(step)
        if math.isfinite(pa_stop):
            return float(pa_stop), "CURRENT_PRICE_ACTION_SWING_LOW", float(step)
    raise ScannerError("Unable to derive a dynamic post-T1 OI/price-action stop.")



def migrate_active_trade_to_v25(
    trade: dict[str, Any],
    *,
    chain: list[dict[str, Any]],
    spot: float,
    structure: StructureResult,
    price_session: Optional[pd.DataFrame],
    change_oi_by_strike: Optional[dict[float, dict[str, float]]],
) -> bool:
    """One-time migration of legacy trades to authoritative NIFTY PA/OI levels.

    Legacy V19/V21/V22/V25 trades may contain option-premium targets or a historical
    ``t1_hit`` flag generated by the old premium-target engine. V26 therefore
    re-derives T1/T2/SL from current NIFTY price action + current option OI and
    then recomputes whether the new structural T1 has actually been reached.
    """
    engine = str(trade.get("target_engine_version", "")).strip()
    if engine == OPTION_TARGET_ENGINE_VERSION:
        return False

    direction = str(trade.get("direction", structure.direction)).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        logger.warning("V26 TRADE MIGRATION FAILED: invalid trade direction=%s", direction)
        return False

    if direction != structure.direction:
        direction_structure = type("TradeStructure", (), {
            "direction": direction,
            "support_1": structure.support_1,
            "support_2": structure.support_2,
            "resistance_1": structure.resistance_1,
            "resistance_2": structure.resistance_2,
            "vwap": structure.vwap,
        })()
    else:
        direction_structure = structure

    try:
        t1, t2, sl, meta = determine_structural_trade_levels(
            chain,
            float(spot),
            direction_structure,
            price_session,
            change_oi_by_strike=change_oi_by_strike,
        )
    except Exception as exc:
        logger.warning(
            "V26 TRADE MIGRATION FAILED: preserving existing trade levels | %s",
            exc,
        )
        return False

    old = (
        trade.get("target_1"),
        trade.get("target_2"),
        trade.get("stop_loss"),
        trade.get("underlying_target_1"),
        trade.get("underlying_target_2"),
        trade.get("underlying_stop"),
        trade.get("t1_hit"),
    )

    trade["target_1"] = round(float(t1), 2)
    trade["target_2"] = round(float(t2), 2)
    trade["stop_loss"] = round(float(sl), 2)
    trade["underlying_target_1"] = round(float(t1), 2)
    trade["underlying_target_2"] = round(float(t2), 2)
    trade["underlying_stop"] = round(float(sl), 2)

    structural_t1_hit = (
        float(spot) <= float(t1)
        if direction == "BEARISH"
        else float(spot) >= float(t1)
    )
    trade["t1_hit"] = bool(structural_t1_hit)
    trade["t1_notified"] = False
    trade["target_engine_version"] = OPTION_TARGET_ENGINE_VERSION
    trade.pop("post_t1_dynamic_stop", None)
    trade.pop("post_t1_dynamic_stop_source", None)
    trade.pop("post_t1_dynamic_stop_updated_at", None)
    trade["t1_hit_at"] = now_ist().isoformat() if structural_t1_hit else ""

    logger.info(
        "V26 TRADE MIGRATION: %s | old T1=%s T2=%s SL=%s old_uT1=%s old_uT2=%s old_uSL=%s old_t1_hit=%s -> "
        "PA/OI T1=%.2f T2=%.2f SL=%.2f t1_hit=%s | spot=%.2f | sources=%s/%s/%s",
        trade.get("trading_symbol", ""),
        old[0], old[1], old[2], old[3], old[4], old[5], old[6],
        t1, t2, sl, structural_t1_hit, spot,
        meta.get("t1_source", ""), meta.get("t2_source", ""), meta.get("sl_source", ""),
    )
    return True


# =============================================================================
# STATE
# =============================================================================

def load_state() -> dict[str, Any]:
    if not STATE_FILE.exists():
        return {}

    try:
        with STATE_FILE.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except Exception as exc:
        logger.warning("State load failed: %s", exc)
        return {}


def save_state(state: dict[str, Any]) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE_FILE.with_suffix(".tmp")

    with tmp.open("w", encoding="utf-8") as fh:
        json.dump(state, fh, indent=2, ensure_ascii=False)

    tmp.replace(STATE_FILE)


def active_trade_from_state(
    state: dict[str, Any],
) -> Optional[dict[str, Any]]:
    trade = state.get("active_trade")
    if not isinstance(trade, dict):
        return None

    if str(trade.get("status", "")).upper() != "ACTIVE":
        return None

    required = {
        "instrument_key",
        "trading_symbol",
        "direction",
        "entry",
        "target_1",
        "target_2",
        "stop_loss",
    }
    return trade if required.issubset(trade) else None


def signal_hash(signal: Signal) -> str:
    key = "|".join(
        [
            signal.direction,
            signal.instrument_key,
            str(signal.strike),
            signal.timestamp[:10],
        ]
    )
    return hashlib.sha256(key.encode("utf-8")).hexdigest()


def format_engine_output(signal: Signal) -> str:
    """Display NIFTY structural levels; option exits use the live option LTP."""
    return (
        f"1. Market State: [{signal.market_state}]\n"
        f"2. Bias: [{signal.bias}]\n"
        f"3. Entry Trigger: [{signal.entry_trigger}]\n"
        f"4. Targets:\n"
        f"   - T1: NIFTY {signal.underlying_target_1:.2f}\n"
        f"   - T2: NIFTY {signal.underlying_target_2:.2f}\n"
        f"5. Stop Loss: NIFTY {signal.underlying_stop:.2f}\n"
        f"   Option exits at the live option LTP when the NIFTY structural level is reached.\n"
        f"6. Invalidation Rule: [{signal.invalidation_rule}]"
    )


# =============================================================================
# EMAIL
# =============================================================================

def send_email(subject: str, body: str) -> None:
    if not all([EMAIL_SENDER, EMAIL_PASSWORD, EMAIL_RECEIVER]):
        logger.info("Email not configured; skipping email.")
        return

    message = MIMEMultipart("alternative")
    message["From"] = EMAIL_SENDER
    message["To"] = EMAIL_RECEIVER
    message["Subject"] = subject
    message.attach(MIMEText(body, "html", "utf-8"))

    with smtplib.SMTP_SSL(
        SMTP_HOST,
        SMTP_PORT,
        timeout=30,
    ) as server:
        server.login(EMAIL_SENDER, EMAIL_PASSWORD)
        server.sendmail(
            EMAIL_SENDER,
            [EMAIL_RECEIVER],
            message.as_string(),
        )


def signal_email_body(signal: Signal) -> str:
    reasons = "".join(
        f"<li>{html.escape(reason)}</li>"
        for reason in signal.reasons
    )

    return f"""
<html>
<body>
<h2>NIFTY Predictive {html.escape(signal.direction)} Signal</h2>
<table border="1" cellpadding="6" cellspacing="0">
<tr><td><b>Time</b></td><td>{html.escape(signal.timestamp)}</td></tr>
<tr><td><b>Market State</b></td><td>{html.escape(signal.market_state)}</td></tr>
<tr><td><b>Regime</b></td><td>{html.escape(signal.regime)}</td></tr>
<tr><td><b>Entry Trigger</b></td><td>{html.escape(signal.entry_trigger)}</td></tr>
<tr><td><b>Invalidation</b></td><td>{html.escape(signal.invalidation_rule)}</td></tr>
<tr><td><b>Confidence</b></td><td>{signal.confidence:.1f}%</td></tr>
<tr><td><b>Spot</b></td><td>{signal.spot:.2f}</td></tr>
<tr><td><b>Futures Regime</b></td><td>{html.escape(signal.futures_state)}</td></tr>
<tr><td><b>Option</b></td><td>{html.escape(signal.trading_symbol)}</td></tr>
<tr><td><b>Strike</b></td><td>{signal.strike:.0f} {signal.option_type}</td></tr>
<tr><td><b>Entry</b></td><td>₹{signal.entry:.2f}</td></tr>
<tr><td><b>NIFTY Target 1</b></td><td>{signal.underlying_target_1:.2f}</td></tr>
<tr><td><b>NIFTY Target 2</b></td><td>{signal.underlying_target_2:.2f}</td></tr>
<tr><td><b>NIFTY Structural SL</b></td><td>{signal.underlying_stop:.2f}</td></tr>
<tr><td><b>Option Exit at T1</b></td><td>Live option LTP when NIFTY T1 is reached</td></tr>
<tr><td><b>Option Exit at T2</b></td><td>Live option LTP when NIFTY T2 is reached</td></tr>
<tr><td><b>Structural Exit</b></td><td>Live option LTP when NIFTY SL is breached</td></tr>
<tr><td><b>Delta</b></td><td>{signal.delta:.4f}</td></tr>
<tr><td><b>Theta</b></td><td>{signal.theta:.4f}</td></tr>
<tr><td><b>Support</b></td><td>{signal.support_1:.0f} / {signal.support_2:.0f}</td></tr>
<tr><td><b>Resistance</b></td><td>{signal.resistance_1:.0f} / {signal.resistance_2:.0f}</td></tr>
</table>

<h3>Decision factors</h3>
<ul>{reasons}</ul>

<p>This is a rule-based market signal, not a guarantee of execution,
profitability, or future price movement. No order is placed by this script.</p>
</body>
</html>
"""


# =============================================================================
# ACTIVE TRADE MONITOR
# =============================================================================

def _trade_entry_bar_utc(trade: dict[str, Any]) -> Optional[pd.Timestamp]:
    """Return the first safe 1m bar boundary after the actual option entry.

    The entry timestamp can fall inside a 1m candle. That candle contains price
    action that happened before the option was purchased, so it must never be
    allowed to trigger a post-entry stop.
    """
    raw = str(trade.get("opened_at") or "").strip()
    if not raw:
        return None
    try:
        ts = pd.Timestamp(raw)
        if ts.tzinfo is None:
            ts = ts.tz_localize(IST)
        else:
            ts = ts.tz_convert(IST)
        return ts.tz_convert("UTC").floor("min") + pd.Timedelta(minutes=1)
    except Exception:
        return None


def _prepare_active_trade_1m_window(
    trade: dict[str, Any],
    option_1m: Optional[pd.DataFrame],
) -> Optional[pd.DataFrame]:
    """Keep only post-entry/new 1m bars and never replay old candles.

    The latest bar is retained on every scan because its OHLC can still evolve.
    Older bars are evaluated only once via ``intrabar_last_checked_at``.
    """
    if option_1m is None or option_1m.empty:
        return None

    work = option_1m.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    for column in ("high", "low"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low"])
    if work.empty:
        return None

    entry_bar = _trade_entry_bar_utc(trade)
    if entry_bar is not None:
        work = work[work["timestamp"] >= entry_bar]

    last_checked_raw = str(trade.get("intrabar_last_checked_at") or "").strip()
    if last_checked_raw:
        try:
            last_checked = pd.Timestamp(last_checked_raw)
            if last_checked.tzinfo is None:
                last_checked = last_checked.tz_localize("UTC")
            else:
                last_checked = last_checked.tz_convert("UTC")
            current_bar_ts = (
                pd.Timestamp(now_ist()).tz_convert("UTC").floor("min")
            )
            # Re-evaluate only the currently-forming 1m bar. A completed bar
            # must never be replayed after the stop has been ratcheted upward,
            # otherwise an old low can falsely trigger the new stop.
            work = work[
                (work["timestamp"] > last_checked)
                | (work["timestamp"] >= current_bar_ts)
            ]
        except Exception:
            pass

    if work.empty:
        return None
    return work.tail(max(ACTIVE_TRADE_INTRABAR_LOOKBACK, 1)).copy()


def apply_dynamic_oi_stop_to_trade(
    trade: dict[str, Any],
    *,
    chain: list[dict[str, Any]],
    spot: float,
    price_session: Optional[pd.DataFrame],
    latest_bar: str = "",
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> tuple[bool, float, str]:
    """Recalculate the post-T1 SL from CURRENT opposing OI.

    The pre-T1 structural SL is deliberately ignored after T1. Once post-T1 is
    active, only the current OI-derived stop is authoritative. A previous
    *post-T1 OI stop* may ratchet favorably so the scanner never gives back a
    previously secured structural level.
    """
    direction = str(trade.get("direction", "")).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Dynamic OI stop requires BULLISH or BEARISH direction.")

    dynamic_stop, dynamic_source, _ = dynamic_oi_stop_after_t1(
        chain,
        float(spot),
        direction,
        price_session,
        entry_underlying=safe_float(trade.get("entry_underlying"), float("nan")),
        change_oi_by_strike=change_oi_by_strike,
    )

    prior_post_t1 = safe_float(trade.get("post_t1_dynamic_stop"), float("nan"))
    if math.isfinite(prior_post_t1):
        effective_stop = (
            min(prior_post_t1, dynamic_stop) if direction == "BEARISH"
            else max(prior_post_t1, dynamic_stop)
        )
    else:
        effective_stop = dynamic_stop

    changed = (not math.isfinite(prior_post_t1)) or abs(effective_stop - prior_post_t1) >= 0.01
    trade["post_t1_dynamic_stop"] = round(float(effective_stop), 2)
    trade["post_t1_dynamic_stop_source"] = dynamic_source
    trade["post_t1_dynamic_stop_updated_at"] = now_ist().isoformat()
    trade["underlying_stop"] = round(float(effective_stop), 2)
    trade["stop_loss"] = round(float(effective_stop), 2)
    if changed and latest_bar:
        trade["underlying_stop_armed_bar"] = str(latest_bar)
    return changed, float(effective_stop), dynamic_source


def _as_ist_timestamp(value: Any) -> Optional[pd.Timestamp]:
    raw = str(value or "").strip()
    if not raw:
        return None
    if raw.upper().endswith(" IST"):
        raw = raw[:-4].strip()
    try:
        stamp = pd.Timestamp(raw)
        if stamp.tzinfo is None:
            stamp = stamp.tz_localize(IST)
        else:
            stamp = stamp.tz_convert(IST)
        return stamp
    except Exception:
        return None


def stagnation_exit_trigger(
    trade: dict[str, Any],
    price_5m: Optional[pd.DataFrame],
) -> tuple[bool, str]:
    """Detect a <0.10% total high-low range across three closed 5m bars after entry."""
    if price_5m is None or price_5m.empty:
        return False, "5-minute candles unavailable"
    opened_at = _as_ist_timestamp(trade.get("opened_at"))
    if opened_at is None:
        return False, "trade opening timestamp unavailable"
    bars = filter_completed_candles(price_5m, 5)
    if bars.empty:
        return False, "no completed 5-minute candles"
    local_start = pd.to_datetime(bars["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST)
    # A bar qualifies only when its close occurs after the trade was opened.
    bars = bars.loc[local_start + pd.to_timedelta(5, unit="m") > opened_at].copy()
    if len(bars) < max(STAGNATION_REQUIRED_BARS, 3):
        return False, f"only {len(bars)} eligible completed 5m bars"
    bars = bars.tail(max(STAGNATION_REQUIRED_BARS, 3))
    high = pd.to_numeric(bars["high"], errors="coerce")
    low = pd.to_numeric(bars["low"], errors="coerce")
    close = pd.to_numeric(bars["close"], errors="coerce")
    if high.isna().any() or low.isna().any() or close.isna().any() or float(close.mean()) <= 0:
        return False, "5-minute OHLC data invalid"
    range_pct = float((high.max() - low.min()) / close.mean())
    timestamps = pd.to_datetime(bars["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST)
    if range_pct < STAGNATION_RANGE_PCT:
        return True, (
            f"3_COMPLETED_5M_BARS_RANGE={range_pct:.4%}<" f"{STAGNATION_RANGE_PCT:.2%}; "
            f"from={timestamps.iloc[0].strftime('%H:%M')} to={(timestamps.iloc[-1] + pd.Timedelta(minutes=5)).strftime('%H:%M')} IST"
        )
    return False, f"three-bar range {range_pct:.4%} is not below {STAGNATION_RANGE_PCT:.2%}"


def force_close_active_trade_at_cutoff(state: dict[str, Any], reason: str = "TIME_CUTOFF_15_15") -> bool:
    """Persist/email an exit decision at cutoff. This scanner does not place broker orders."""
    trade = active_trade_from_state(state)
    if trade is None:
        return True
    try:
        exit_ltp = extract_ltp(get_quote(str(trade["instrument_key"])))
    except ScannerError as exc:
        logger.error("CUTOFF EXIT PENDING: cannot obtain live option LTP; trade retained in state: %s", exc)
        return False
    closed = dict(trade)
    closed.update({
        "status": "CLOSED",
        "outcome": reason,
        "exit_ltp": round(exit_ltp, 2),
        "closed_at": now_ist().isoformat(),
        "exit_reason": reason,
        "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
    })
    state["active_trade"] = None
    state["last_completed_trade"] = closed
    save_state(state)
    send_email(
        f"NIFTY FORCED EXIT - {trade.get('trading_symbol', 'Active position')}",
        f"<p>Intraday cutoff exit signal: {html.escape(reason)}.</p>"
        f"<p>Option: {html.escape(str(trade.get('trading_symbol', '')))}<br>"
        f"Entry: ₹{safe_float(trade.get('entry')):.2f}<br>"
        f"Latest option LTP: ₹{exit_ltp:.2f}<br>"
        f"Time: {html.escape(now_ist().strftime('%Y-%m-%d %H:%M:%S IST'))}</p>"
        "<p>This scanner records exit decisions and sends notifications; it does not submit broker orders.</p>",
    )
    logger.warning("TRADE CLOSED: %s outcome=%s exit_option=%.2f", trade.get("trading_symbol", ""), reason, exit_ltp)
    return True


def monitor_active_trade(
    state: dict[str, Any],
    structure: StructureResult,
    *,
    chain: Optional[list[dict[str, Any]]] = None,
    price_session: Optional[pd.DataFrame] = None,
) -> str:
    trade = active_trade_from_state(state)
    if trade is None:
        return "NO_ACTIVE"

    today = now_ist().date().isoformat()
    trade_date = str(trade.get("trade_date", ""))[:10]

    if trade_date and trade_date != today:
        state["last_completed_trade"] = dict(
            trade,
            status="CLOSED",
            outcome="SESSION_END_CLEANUP",
            closed_at=now_ist().isoformat(),
        )
        state["active_trade"] = None
        save_state(state)
        return "CLOSED"

    try:
        ltp = extract_ltp(get_quote(str(trade["instrument_key"])))
    except ScannerError as exc:
        logger.info("Active trade quote unavailable: %s", exc)
        return "ACTIVE"

    entry = safe_float(trade.get("entry"))
    underlying_t1 = safe_float(trade.get("underlying_target_1"), float("nan"))
    underlying_t2 = safe_float(trade.get("underlying_target_2"), float("nan"))
    underlying_stop = safe_float(trade.get("underlying_stop"), float("nan"))
    t1_hit = bool(trade.get("t1_hit", False))
    intrabar_outcome = None
    intrabar_exit_reference = None
    intrabar_reason = "DISABLED"

    # Current NIFTY spot is the authoritative trigger for structural exits.
    snapshot_for_trade = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    spot_now = safe_float(snapshot_for_trade.get("spot"), float("nan"))
    if not math.isfinite(spot_now) or spot_now <= 0:
        try:
            spot_now = extract_ltp(get_quote(NIFTY_KEY))
        except ScannerError:
            spot_now = float("nan")

    underlying_1m = None
    if ACTIVE_TRADE_INTRABAR_MONITOR:
        try:
            underlying_1m_raw = get_intraday_candles(NIFTY_KEY, 1, strict=False)
            underlying_1m = _prepare_active_trade_1m_window(trade, underlying_1m_raw)
        except Exception as exc:
            intrabar_reason = f"1M_MONITOR_ERROR:{exc}"
            logger.info("Active trade NIFTY 1m monitor unavailable: %s", exc)

    # A three-candle stagnation breaker protects open option buys from prolonged theta decay.
    try:
        candles_5m = get_intraday_candles(NIFTY_KEY, 5, strict=False)
        stagnant, stagnation_reason = stagnation_exit_trigger(trade, candles_5m)
        logger.info("STAGNATION EXIT CHECK: %s trigger=%s reason=%s", trade.get("trading_symbol", ""), stagnant, stagnation_reason)
        if stagnant:
            closed = dict(trade)
            closed.update({
                "status": "CLOSED", "outcome": "STAGNATION_EXIT",
                "exit_ltp": round(ltp, 2), "closed_at": now_ist().isoformat(),
                "exit_reason": stagnation_reason,
                "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            })
            state["active_trade"] = None
            state["last_completed_trade"] = closed
            save_state(state)
            send_email(
                f"NIFTY STAGNATION EXIT - {trade['trading_symbol']}",
                f"<p>Intraday trade closed by the stagnation breaker.</p><p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry if 'entry' in locals() else safe_float(trade.get('entry')):.2f}<br>"
                f"Current option LTP: ₹{ltp:.2f}<br>Reason: {html.escape(stagnation_reason)}</p>"
                "<p>This scanner records exit decisions and sends notifications; it does not submit broker orders.</p>",
            )
            logger.warning("TRADE CLOSED: %s outcome=STAGNATION_EXIT exit_option=%.2f reason=%s", trade.get("trading_symbol", ""), ltp, stagnation_reason)
            return "CLOSED"
    except Exception as exc:
        logger.info("Stagnation exit check unavailable; continuing with structural exits: %s", exc)

    # First detect T1 from the authoritative NIFTY structural level. The current
    # OI stop is recalculated immediately on the same scan after T1 is reached.
    if not t1_hit and math.isfinite(spot_now) and math.isfinite(underlying_t1):
        direction = str(trade.get("direction", "")).upper()
        t1_hit = (
            spot_now <= underlying_t1 if direction == "BEARISH"
            else spot_now >= underlying_t1
        )
        if t1_hit:
            trade["t1_hit_at"] = now_ist().isoformat()
    if not t1_hit and underlying_1m is not None and not underlying_1m.empty:
        probe_trade = dict(trade)
        probe_trade["t1_hit"] = False
        probe_trade["underlying_stop"] = float("nan")
        probe_trade["underlying_target_2"] = float("nan")
        probe_outcome, probe_ref, probe_reason = _active_trade_intrabar_exit(
            probe_trade,
            underlying_1m=underlying_1m,
            underlying_3m=filter_completed_candles(price_session, 3) if price_session is not None else None,
        )
        if probe_outcome == "T1_HIT":
            t1_hit = True
            trade["t1_hit"] = True
            _set_t1_activation_from_intrabar_reason(trade, probe_reason)
            intrabar_exit_reference = probe_ref
            intrabar_reason = probe_reason

    if t1_hit:
        trade["t1_hit"] = True
        trade.setdefault("t1_hit_at", now_ist().isoformat())

    # Once T1 is reached, CURRENT opposing OI becomes the authoritative dynamic SL.
    if t1_hit and chain and price_session is not None and math.isfinite(spot_now):
        try:
            completed_3m = filter_completed_candles(price_session, 3) if price_session is not None else pd.DataFrame()
            latest_bar = str(completed_3m["timestamp"].iloc[-1]) if not completed_3m.empty else ""
            changed, effective_stop, dynamic_source = apply_dynamic_oi_stop_to_trade(
                trade,
                chain=chain,
                spot=spot_now,
                price_session=price_session,
                latest_bar=latest_bar,
                change_oi_by_strike=(state.get("option_flow_by_strike") if isinstance(state.get("option_flow_by_strike"), dict) else None),
            )
            underlying_stop = effective_stop
            logger.info(
                "DYNAMIC T1 SL: option=%s T1_NIFTY=%.2f current_spot=%.2f source=%s "
                "effective_SL_NIFTY=%.2f changed=%s",
                trade["trading_symbol"],
                underlying_t1,
                spot_now,
                dynamic_source,
                effective_stop,
                changed,
            )
        except ScannerError as exc:
            logger.info("Dynamic post-T1 OI stop unavailable: %s", exc)

    # Now evaluate the effective structural stop/T2. Re-run the NIFTY 1m path
    # after the dynamic stop update so a same-cycle adverse move can be caught.
    if ACTIVE_TRADE_INTRABAR_MONITOR and underlying_1m is not None and not underlying_1m.empty:
        try:
            (
                intrabar_outcome,
                intrabar_exit_reference,
                intrabar_reason,
            ) = _active_trade_intrabar_exit(
                trade,
                underlying_1m=underlying_1m,
                underlying_3m=filter_completed_candles(price_session, 3) if price_session is not None else None,
            )
            trade["intrabar_last_checked_at"] = underlying_1m["timestamp"].max().isoformat()
            logger.info(
                "ACTIVE TRADE STRUCTURE MONITOR: %s outcome=%s reference=%s reason=%s",
                trade["trading_symbol"],
                intrabar_outcome or "NONE",
                f"{intrabar_exit_reference:.2f}" if intrabar_exit_reference is not None else "-",
                intrabar_reason,
            )
        except Exception as exc:
            intrabar_reason = f"1M_MONITOR_ERROR:{exc}"
            logger.info("Active trade NIFTY 1m monitor unavailable: %s", exc)

    # Quote-level structural trigger is a backup when the intrabar path had no bar breach.
    completed_3m_for_quote = (
        filter_completed_candles(price_session, 3)
        if price_session is not None else pd.DataFrame()
    )
    if math.isfinite(spot_now):
        if not t1_hit and math.isfinite(underlying_t1):
            direction = str(trade.get("direction", "")).upper()
            t1_hit = (spot_now <= underlying_t1 if direction == "BEARISH" else spot_now >= underlying_t1)
        direction = str(trade.get("direction", "")).upper()
        t2_reached = (
            spot_now <= underlying_t2 if direction == "BEARISH"
            else spot_now >= underlying_t2
        ) if math.isfinite(underlying_t2) else False
        stop_reached = (
            (spot_now >= underlying_stop if direction == "BEARISH" else spot_now <= underlying_stop)
            and _underlying_stop_confirmation_ready(trade, completed_3m_for_quote)
        ) if math.isfinite(underlying_stop) else False
    else:
        t2_reached = False
        stop_reached = False

    if intrabar_outcome == "STOP_LOSS" or stop_reached:
        outcome = "STOP_LOSS"
    elif intrabar_outcome == "TARGET_2" or t2_reached:
        outcome = "TARGET_2"
    else:
        outcome = ""

    if outcome:
        closed = dict(trade)
        closed.update({
            "status": "CLOSED",
            "outcome": outcome,
            "exit_ltp": round(ltp, 2),
            "closed_at": now_ist().isoformat(),
            "exit_reason": intrabar_reason if intrabar_outcome else "NIFTY_STRUCTURAL_LEVEL",
            "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
        })
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"NIFTY TRADE {outcome} - {trade['trading_symbol']}",
            (
                f"<p>{html.escape(str(trade['direction']))} trade closed on the NIFTY structural level.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry:.2f}<br>"
                f"Live option exit: ₹{ltp:.2f}<br>"
                f"NIFTY T1: {underlying_t1:.2f}<br>"
                f"NIFTY T2: {underlying_t2:.2f}<br>"
                f"NIFTY SL: {underlying_stop:.2f}<br>"
                f"Outcome: {outcome}</p>"
            ),
        )
        logger.info(
            "TRADE CLOSED: %s outcome=%s exit_option=%.2f trigger_nifty=%.2f",
            trade["trading_symbol"], outcome, ltp, spot_now,
        )
        return "CLOSED"

    if t1_hit and not bool(trade.get("t1_notified", False)):
        trade["t1_hit"] = True
        trade["t1_notified"] = True
        send_email(
            f"NIFTY T1 HIT - {trade['trading_symbol']}",
            (
                f"<p>NIFTY T1 reached. Trade remains active toward T2.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry option LTP: ₹{entry:.2f}<br>"
                f"Current option LTP: ₹{ltp:.2f}<br>"
                f"NIFTY T1: {underlying_t1:.2f}<br>"
                f"Dynamic OI SL: {safe_float(trade.get('underlying_stop')):.2f}</p>"
            ),
        )
    active_direction = str(trade.get("direction", "")).upper()
    last_opposite = int(trade.get("reversal_confirmations", 0) or 0)

    # Enforce the invalidation rule promised by the signal itself. The structural
    # engine remains the entry-direction authority; this check only protects an
    # already-open position when the confirmed continuous structure is lost.
    expected_phase = (
        "CONTINUOUS_BULLISH" if active_direction == "BULLISH"
        else "CONTINUOUS_BEARISH"
    )
    snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    spot_now = safe_float(snapshot.get("spot"), spot_now if math.isfinite(spot_now) else 0.0)
    vwap_now = safe_float(snapshot.get("vwap"), float("nan"))

    vwap_reclaimed_against_trade = False
    if spot_now > 0 and math.isfinite(vwap_now):
        vwap_reclaimed_against_trade = (
            active_direction == "BEARISH" and spot_now > vwap_now
        ) or (
            active_direction == "BULLISH" and spot_now < vwap_now
        )

    trade_intensity = str(trade.get("market_intensity", "NORMAL")).upper()
    snapshot_intensity = str(snapshot.get("market_intensity", "UNKNOWN")).upper()
    snapshot_regime_direction = str(snapshot.get("regime_direction", "NEUTRAL")).upper()
    if trade_intensity == "EXHAUSTION":
        # VWAP opposition is expected at the start of a counter-trend exhaustion
        # scalp. Do not immediately invalidate it merely because the original
        # trend phase is still present; its structural stop/T2 remains authoritative.
        vwap_reclaimed_against_trade = False
        exhaustion_confirmed = bool(
            snapshot_intensity == "EXHAUSTION"
            and snapshot_regime_direction == active_direction
            and snapshot.get("reversal_price_confirmed", False)
        )
        opposing_trend_reasserted = (
            structure.market_phase == ("CONTINUOUS_BEARISH" if active_direction == "BULLISH" else "CONTINUOUS_BULLISH")
            and structure.entry_confirmed
        )
        market_alignment_failure = bool(opposing_trend_reasserted and not exhaustion_confirmed)
        expected_phase = f"EXHAUSTION_{active_direction}"
        current_phase_for_log = f"{snapshot_intensity}_{snapshot_regime_direction}"
    else:
        same_continuous_phase = structure.market_phase == expected_phase
        market_alignment_failure = not same_continuous_phase or vwap_reclaimed_against_trade
        current_phase_for_log = structure.market_phase

    alignment_failures = int(trade.get("market_alignment_failures", 0) or 0)
    if market_alignment_failure:
        alignment_failures += 1
    else:
        alignment_failures = 0
    trade["market_alignment_failures"] = alignment_failures

    logger.info(
        "MARKET INVALIDATION CHECK: active=%s expected_phase=%s current_phase=%s "
        "vwap_reclaimed=%s failures=%d/%d",
        active_direction,
        expected_phase,
        current_phase_for_log,
        vwap_reclaimed_against_trade,
        alignment_failures,
        max(MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED, 1),
    )

    if alignment_failures >= max(MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED, 1):
        closed = dict(trade)
        closed.update(
            {
                "status": "CLOSED",
                "outcome": "MARKET_ALIGNMENT_INVALIDATION",
                "exit_ltp": round(ltp, 2),
                "closed_at": now_ist().isoformat(),
                "exit_reason": (
                    "continuous market phase lost and/or NIFTY reclaimed VWAP"
                ),
                "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            }
        )
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"NIFTY MARKET INVALIDATION - {trade['trading_symbol']}",
            (
                f"<p>Trade exited because the confirmed market alignment was lost.</p>"
                f"<p>Active direction: {html.escape(active_direction)}<br>"
                f"Current phase: {html.escape(str(structure.market_phase))}<br>"
                f"NIFTY spot: {spot_now:.2f}<br>"
                f"NIFTY VWAP: {vwap_now:.2f}<br>"
                f"Exit: ₹{ltp:.2f}</p>"
            ),
        )
        logger.info(
            "TRADE CLOSED: %s outcome=MARKET_ALIGNMENT_INVALIDATION exit=%.2f",
            trade["trading_symbol"],
            ltp,
        )
        return "CLOSED"

    if structure.direction == active_direction:
        last_opposite = 0
    elif structure.direction in {"BULLISH", "BEARISH"}:
        last_opposite += 1
    else:
        last_opposite = 0

    trade["reversal_confirmations"] = last_opposite
    trade["last_ltp"] = round(ltp, 2)
    trade["last_market_direction"] = structure.direction
    trade["last_market_confidence"] = structure.confidence
    trade["last_monitored_at"] = now_ist().isoformat()

    state["active_trade"] = trade
    save_state(state)

    logger.info(
        "ACTIVE TRADE: %s option_LTP=%.2f NIFTY_T1=%.2f NIFTY_T2=%.2f NIFTY_SL=%.2f "
        "market=%s invalidations=%d/%d",
        trade["trading_symbol"],
        ltp,
        safe_float(trade.get("underlying_target_1"), float("nan")),
        safe_float(trade.get("underlying_target_2"), float("nan")),
        safe_float(trade.get("underlying_stop"), float("nan")),
        structure.direction,
        last_opposite,
        MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED,
    )
    return "ACTIVE"


# =============================================================================
# SCAN
# =============================================================================



def update_continuation_persistence(
    state: dict[str, Any],
    market_phase: str,
    latest_completed_3m_bar: Optional[Any] = None,
    *,
    required_confirmations: Optional[int] = None,
) -> tuple[bool, int]:
    """Track continuous or explicitly confirmed exhaustion setups on distinct 3m bars."""
    phase = str(market_phase or "").upper()
    if phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH", "EXHAUSTION_BULLISH", "EXHAUSTION_BEARISH"}:
        state["continuation_phase"] = ""
        state["continuation_count"] = 0
        state["continuation_last_bar"] = ""
        logger.info(
            "CONTINUATION PERSISTENCE: phase=%s reset=1",
            phase or "NONE",
        )
        return False, 0

    previous_phase = str(state.get("continuation_phase", "")).upper()
    previous_count = int(state.get("continuation_count", 0) or 0)
    current_bar = str(latest_completed_3m_bar or "")

    if previous_phase != phase:
        count = 1
    elif current_bar and current_bar != str(state.get("continuation_last_bar", "")):
        count = previous_count + 1
    elif current_bar:
        # Same completed candle: do not manufacture a second confirmation.
        count = previous_count
    else:
        # When the timestamp is unavailable, remain conservative and do not
        # count the same state repeatedly.
        count = max(previous_count, 1)

    state["continuation_phase"] = phase
    state["continuation_count"] = count
    state["continuation_last_bar"] = current_bar
    required = max(int(required_confirmations or CONTINUATION_CONFIRMATIONS_REQUIRED), 1)
    ready = count >= required

    logger.info(
        "CONTINUATION PERSISTENCE: phase=%s count=%d/%d last_3m_bar=%s ready=%s",
        phase,
        count,
        required,
        current_bar or "UNKNOWN",
        ready,
    )
    return ready, count


def _set_t1_activation_from_intrabar_reason(
    trade: dict[str, Any],
    reason: str,
) -> None:
    """Persist the actual 1m bar timestamp that first reached structural T1."""
    try:
        first_part = str(reason).split(";", 1)[0]
        activation_raw = first_part.rsplit("@", 1)[1].strip() if "@" in first_part else ""
        if activation_raw:
            activation_ts = pd.Timestamp(activation_raw)
            if activation_ts.tzinfo is None:
                activation_ts = activation_ts.tz_localize("UTC")
            else:
                activation_ts = activation_ts.tz_convert("UTC")
            trade["t1_hit_at"] = activation_ts.isoformat()
            return
    except Exception:
        pass
    trade["t1_hit_at"] = now_ist().isoformat()


def _underlying_stop_confirmation_ready(
    trade: dict[str, Any],
    underlying_3m: Optional[pd.DataFrame],
) -> bool:
    """Return whether the configured completed-3m confirmation permits an SL exit."""
    stop = safe_float(trade.get("underlying_stop"), float("nan"))
    if not ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION or not math.isfinite(stop):
        return True
    if underlying_3m is None or underlying_3m.empty:
        return True

    work = underlying_3m.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work["close"] = pd.to_numeric(work["close"], errors="coerce")
    work = work.dropna(subset=["timestamp", "close"])
    required = max(STRUCTURAL_STOP_CONFIRM_BARS, 1)
    recent = work.tail(required)
    armed_raw = str(trade.get("underlying_stop_armed_bar") or "").strip()
    if armed_raw:
        try:
            armed_ts = pd.Timestamp(armed_raw)
            if armed_ts.tzinfo is None:
                armed_ts = armed_ts.tz_localize("UTC")
            else:
                armed_ts = armed_ts.tz_convert("UTC")
            recent = recent[recent["timestamp"] > armed_ts]
        except Exception:
            pass
    if len(recent) < required:
        return False

    closes = recent["close"].to_numpy(dtype=float)
    direction = str(trade.get("direction", "")).upper()
    return bool(
        np.all(closes >= stop) if direction == "BEARISH"
        else np.all(closes <= stop) if direction == "BULLISH"
        else False
    )


def _active_trade_intrabar_exit(
    trade: dict[str, Any],
    *,
    underlying_1m: Optional[pd.DataFrame] = None,
    underlying_3m: Optional[pd.DataFrame] = None,
) -> tuple[Optional[str], Optional[float], str]:
    """Trigger exits from NIFTY structural levels, never from option premium math."""
    underlying = underlying_1m
    if underlying is None or underlying.empty:
        return None, None, "NO_UNDERLYING_1M_DATA"

    work = underlying.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    for column in ("high", "low", "close"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low"])
    if work.empty:
        return None, None, "INVALID_UNDERLYING_1M_DATA"

    t1 = safe_float(trade.get("underlying_target_1"), float("nan"))
    t2 = safe_float(trade.get("underlying_target_2"), float("nan"))
    stop = safe_float(trade.get("underlying_stop"), float("nan"))
    direction = str(trade.get("direction", "")).upper()
    t1_already_hit = bool(trade.get("t1_hit", False))

    if underlying_3m is not None and not underlying_3m.empty:
        u3 = underlying_3m.copy().sort_values("timestamp")
        u3["timestamp"] = pd.to_datetime(u3["timestamp"], utc=True, errors="coerce")
        u3["close"] = pd.to_numeric(u3["close"], errors="coerce")
        u3 = u3.dropna(subset=["timestamp", "close"])
    else:
        u3 = pd.DataFrame()

    t1_activation = pd.Timestamp("1900-01-01", tz="UTC")
    if t1_already_hit:
        raw_activation = str(trade.get("t1_hit_at") or "").strip()
        if raw_activation:
            try:
                t1_activation = pd.Timestamp(raw_activation)
                if t1_activation.tzinfo is None:
                    t1_activation = t1_activation.tz_localize("UTC")
                else:
                    t1_activation = t1_activation.tz_convert("UTC")
            except Exception:
                t1_activation = pd.Timestamp("1900-01-01", tz="UTC")

    for _, bar in work.tail(max(ACTIVE_TRADE_INTRABAR_LOOKBACK, 1)).iterrows():
        high = float(bar["high"])
        low = float(bar["low"])
        ts_obj = pd.Timestamp(bar["timestamp"])
        ts = ts_obj.isoformat()

        # T2 can be detected from the complete 1m window because reaching T2
        # implies the T1 level has also been crossed for this directional trade.
        if math.isfinite(t2):
            if direction == "BEARISH" and low <= t2:
                return "TARGET_2", t2, f"NIFTY_1M_LOW={low:.2f}@{ts};T2_NIFTY={t2:.2f}"
            if direction == "BULLISH" and high >= t2:
                return "TARGET_2", t2, f"NIFTY_1M_HIGH={high:.2f}@{ts};T2_NIFTY={t2:.2f}"

        # Initial SL is active before T1. After T1, only bars after the T1
        # activation timestamp may trigger the dynamically recalculated stop.
        stop_active = math.isfinite(stop)
        if t1_already_hit and ts_obj <= t1_activation:
            stop_active = False

        if stop_active:
            stop_confirmed = _underlying_stop_confirmation_ready(trade, u3)
            stop_reference = ""
            if stop_confirmed and math.isfinite(stop) and not u3.empty:
                closes = u3["close"].tail(max(STRUCTURAL_STOP_CONFIRM_BARS, 1)).to_numpy(dtype=float)
                if len(closes):
                    stop_reference = f"NIFTY_3M_CLOSE={closes[-1]:.2f}"
            if stop_confirmed:
                if direction == "BEARISH" and high >= stop:
                    return "STOP_LOSS", stop, f"NIFTY_1M_HIGH={high:.2f}@{ts};{stop_reference};SL_NIFTY={stop:.2f}"
                if direction == "BULLISH" and low <= stop:
                    return "STOP_LOSS", stop, f"NIFTY_1M_LOW={low:.2f}@{ts};{stop_reference};SL_NIFTY={stop:.2f}"

        if not t1_already_hit and math.isfinite(t1):
            if direction == "BEARISH" and low <= t1:
                return "T1_HIT", t1, f"NIFTY_1M_LOW={low:.2f}@{ts};T1_NIFTY={t1:.2f}"
            if direction == "BULLISH" and high >= t1:
                return "T1_HIT", t1, f"NIFTY_1M_HIGH={high:.2f}@{ts};T1_NIFTY={t1:.2f}"

    return None, None, "NO_NIFTY_STRUCTURAL_LEVEL_BREACH"


def execute_scan(
    state: Optional[dict[str, Any]] = None,
) -> Optional[Signal]:
    state = state if isinstance(state, dict) else load_state()
    current_time = now_ist()
    today_iso = current_time.date().isoformat()
    # The 15:15 cutoff is evaluated before ordinary market-hours returns, so an
    # active intraday trade still receives its exit routine if a scan starts late.
    if current_time.weekday() < 5 and current_time.time() >= NEW_ENTRY_CUTOFF:
        active = active_trade_from_state(state)
        if active:
            if str(active.get("trade_date", ""))[:10] == today_iso:
                force_close_active_trade_at_cutoff(state, "TIME_CUTOFF_15_15")
            else:
                # Do not let an expired prior-session position remain active in
                # scanner state if its old instrument no longer has a live quote.
                closed = dict(active)
                closed.update({
                    "status": "CLOSED", "outcome": "SESSION_END_CLEANUP",
                    "closed_at": current_time.isoformat(),
                    "exit_reason": "stale position state from a prior trading date",
                })
                state["active_trade"] = None
                state["last_completed_trade"] = closed
                save_state(state)
                logger.warning("STALE ACTIVE TRADE STATE CLEARED for prior session: %s", active.get("trading_symbol", ""))
        logger.info("NEW ENTRY CUTOFF: %s IST; no new positions after %s.", current_time.strftime("%H:%M:%S"), NEW_ENTRY_CUTOFF.strftime("%H:%M"))
        return None

    if not market_window_open():
        logger.info("Outside NSE market hours.")
        return None

    status = get_market_status()
    logger.info("NSE status=%s", status)
    if status != "OPEN":
        return None

    # State is intraday. Reset directional memory on a new session/version; an
    # active trade is still carried long enough for the monitor to clean it up.
    snapshot = state.get("market_snapshot")
    snapshot_ts = str(snapshot.get("timestamp", ""))[:10] if isinstance(snapshot, dict) else ""
    stored_version = str(state.get("scanner_version", ""))
    if (snapshot_ts and snapshot_ts != today_iso) or (stored_version and stored_version != SCANNER_VERSION):
        state["market_history"] = []
        state["market_snapshot"] = {}
        state["persistent_direction"] = None
        state["continuation_phase"] = ""
        state["continuation_count"] = 0
        state["continuation_last_bar"] = ""
        state["scanner_version"] = SCANNER_VERSION
        state.pop("option_oi_snapshot", None)
        state.pop("option_oi_history", None)
        state.pop("last_signal", None)
        state.pop("last_signal_hash", None)
        state.pop("last_signal_timestamp", None)
        save_state(state)
    else:
        state["scanner_version"] = SCANNER_VERSION

    now_time = now_ist().time()
    future = get_current_nifty_future(state)

    # -------------------------------------------------------------------------
    # PRIMARY MARKET PRICE FEED = NIFTY INDEX
    # -------------------------------------------------------------------------
    index_session = get_current_session_3m_candles(NIFTY_KEY)
    index_live_quote = get_quote(NIFTY_KEY)
    spot = extract_ltp(index_live_quote)

    # -------------------------------------------------------------------------
    # DERIVATIVES FEED = NIFTY FUTURES PRICE/OI
    # -------------------------------------------------------------------------
    futures_session = get_current_session_3m_candles(future.instrument_key)
    futures_live_quote = get_quote(future.instrument_key)
    futures_ltp_now = extract_ltp(futures_live_quote)

    logger.info(
        "UNDERLYING PRICES: index_spot=%.2f futures_ltp=%.2f basis=%+.2f",
        spot, futures_ltp_now, futures_ltp_now - spot,
    )

    if index_session.empty:
        ltp = spot
        opening_ts = pd.Timestamp(now_ist()).tz_convert("UTC")
        index_session = pd.DataFrame([{
            "timestamp": opening_ts,
            "open": ltp,
            "high": ltp,
            "low": ltp,
            "close": ltp,
            "volume": safe_float(index_live_quote.get("volume"), 0.0),
            "oi": np.nan,
        }])
        logger.warning("INDEX SESSION: using live index quote proxy until candles arrive.")

    if futures_session.empty:
        ltp = futures_ltp_now
        opening_ts = pd.Timestamp(now_ist()).tz_convert("UTC")
        futures_session = pd.DataFrame([{
            "timestamp": opening_ts,
            "open": ltp,
            "high": ltp,
            "low": ltp,
            "close": ltp,
            "volume": safe_float(futures_live_quote.get("volume"), 0.0),
            "oi": _extract_quote_oi(futures_live_quote),
        }])
        logger.warning("FUTURES SESSION: using live futures quote proxy until candles arrive.")

    # NIFTY index is always the price series. If index candles have no usable
    # volume, use timestamp-matched NIFTY futures volume only as the VWAP weight.
    try:
        idx_volume = pd.to_numeric(index_session.get("volume", 0.0), errors="coerce").fillna(0.0)
        if float(idx_volume.sum()) <= 0.0:
            idx = index_session.copy()
            idx["timestamp"] = pd.to_datetime(idx["timestamp"], utc=True, errors="coerce")
            fut = futures_session[["timestamp", "volume"]].copy()
            fut["timestamp"] = pd.to_datetime(fut["timestamp"], utc=True, errors="coerce")
            fut["volume"] = pd.to_numeric(fut["volume"], errors="coerce").fillna(0.0)
            idx = idx.merge(fut, on="timestamp", how="left", suffixes=("", "_fut"))
            idx["volume"] = pd.to_numeric(idx["volume_fut"], errors="coerce").fillna(0.0)
            index_session = idx.drop(columns=["volume_fut"], errors="ignore")
            logger.info("INDEX VWAP: using NIFTY futures volume as weighting proxy; price remains NIFTY index.")
    except Exception as exc:
        logger.warning("VWAP volume-proxy preparation failed: %s", exc)

    completed_index_3m = filter_completed_candles(index_session, 3)

    # Historical futures bars are only for OI warm-up; historical index bars are
    # only used if the live current-session index feed is too short.
    try:
        historical_futures = get_historical_candles(future.instrument_key, 3)
        historical_completed = filter_completed_candles(historical_futures, 3)
    except ScannerError as exc:
        logger.warning("Historical futures 3m fallback unavailable: %s", exc)
        historical_completed = pd.DataFrame()

    if futures_session.empty:
        futures_3m = historical_completed.tail(40).copy()
    else:
        completed_current = filter_completed_candles(futures_session, 3)
        futures_3m = pd.concat(
            [historical_completed.tail(35), completed_current],
            ignore_index=True,
        )
        if not futures_3m.empty:
            futures_3m = (
                futures_3m.sort_values("timestamp")
                .drop_duplicates("timestamp", keep="last")
                .reset_index(drop=True)
            )

    # Build the option-chain structure directly from current OI and Change-OI.
    expiry, chain = get_option_chain(state)
    _, change_oi_score, change_oi_by_strike = get_change_oi_confirmation(expiry)
    previous_snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    previous_option_snapshot = state.get("option_oi_snapshot") if isinstance(state.get("option_oi_snapshot"), dict) else {}
    chain_levels = chain_oi_support_resistance(
        chain,
        spot,
        change_oi_by_strike,
        previous_option_snapshot=previous_option_snapshot,
        expiry=expiry,
        previous_support=safe_float(previous_snapshot.get("support_1"), float("nan")),
        previous_resistance=safe_float(previous_snapshot.get("resistance_1"), float("nan")),
    )
    option_flow_by_strike = chain_levels.get("option_flow_by_strike", {})
    oi_velocity_by_strike = update_option_oi_velocity_history(state, chain, expiry, now=now_ist())
    chain_levels["previous_support_1"] = safe_float(previous_snapshot.get("support_1"), float("nan"))
    chain_levels["previous_resistance_1"] = safe_float(previous_snapshot.get("resistance_1"), float("nan"))
    previous_direction = str(previous_snapshot.get("direction", "")).upper() or None
    persistent_direction = str(
        state.get("persistent_direction")
        or previous_snapshot.get("persistent_direction", "")
    ).upper() or None
    previous_phase = str(previous_snapshot.get("market_phase", "")).upper() or None

    seed_direction = persistent_direction or previous_direction

    structure = build_market_structure(
        spot=spot,
        futures_3m=futures_3m,
        futures_session=futures_session,
        chain_levels=chain_levels,
        change_oi_score=change_oi_score,
        futures_live_quote=futures_live_quote,
        previous_direction=seed_direction,
        previous_phase=previous_phase,
        price_session=index_session,
    )
    market_regime = classify_market_regime(
        index_session, spot, structure.vwap, structure.direction,
        structure.support_1, structure.resistance_1,
    )
    is_expiry_day = parse_date(str(expiry)) == now_ist().date()
    tod_window = time_of_day_window(now_ist())
    logger.info(
        "REGIME MATRIX: direction=%s intensity=%s ADX=%s RSI3m=%s RSI15m=%s TOD=%s expiry_day=%s "
        "volume_confirmed=%s divergence=%s reason=%s",
        market_regime.get("direction"), market_regime.get("intensity"),
        f"{safe_float(market_regime.get('adx'), float('nan')):.2f}" if math.isfinite(safe_float(market_regime.get("adx"), float("nan"))) else "NA",
        f"{safe_float(market_regime.get('rsi_3m'), float('nan')):.2f}" if math.isfinite(safe_float(market_regime.get("rsi_3m"), float("nan"))) else "NA",
        f"{safe_float(market_regime.get('rsi_15m'), float('nan')):.2f}" if math.isfinite(safe_float(market_regime.get("rsi_15m"), float("nan"))) else "NA",
        tod_window, is_expiry_day, market_regime.get("volume_confirmed"),
        market_regime.get("divergence"), market_regime.get("reason"),
    )

    state_history = state.get("market_history")
    if not isinstance(state_history, list):
        state_history = []
    history_item = {
        "timestamp": now_ist().isoformat(),
        "spot": round(spot, 2),
        "direction": structure.direction,
        "phase": structure.market_phase,
        "score": round(structure.score, 3),
        "core": round(structure.components.get("intraday_trend", 0.0) + structure.components.get("vwap_level", 0.0), 3),
        "confidence": round(structure.confidence, 2),
        "confirmation_state": structure.confirmation_state,
        "reversal_confirmations": structure.reversal_confirmations,
    }
    state_history.append(history_item)
    state["market_history"] = state_history[-STATE_HISTORY_LIMIT:]

    state["market_snapshot"] = {
        "timestamp": now_ist().isoformat(),
        "spot": round(spot, 2),
        "futures_ltp": round(futures_ltp_now, 2),
        "basis": round(futures_ltp_now - spot, 2),
        "future": future.trading_symbol,
        "future_expiry": future.expiry,
        "futures_regime": structure.futures_regime,
        "futures_bias": structure.futures_bias,
        "futures_oi_strength": round(structure.futures_oi_strength, 4),
        "futures_oi_persistence": round(structure.futures_oi_persistence, 4),
        "futures_live_oi_change": round(structure.futures_live_oi_change, 2) if math.isfinite(structure.futures_live_oi_change) else None,
        "intraday_bias": structure.intraday_bias,
        "intraday_strength": round(structure.intraday_strength, 4),
        "intraday_score": round(structure.intraday_score, 4),
        "chain_predictive_bias": structure.chain_predictive_bias,
        "chain_predictive_strength": round(structure.chain_predictive_strength, 4),
        "chain_level_bias": structure.chain_level_bias,
        "support_strength": round(structure.support_strength, 4),
        "resistance_strength": round(structure.resistance_strength, 4),
        "support_change_strength": round(structure.support_change_strength, 4),
        "resistance_change_strength": round(structure.resistance_change_strength, 4),
        "vwap": round(structure.vwap, 2),
        "vwap_slope": round(structure.vwap_slope, 4),
        "direction": structure.direction,
        "persistent_direction": (
            structure.direction if structure.direction in {"BULLISH", "BEARISH"}
            else seed_direction
        ),
        "score": round(structure.score, 3),
        "confidence": round(structure.confidence, 2),
        "market_phase": structure.market_phase,
        "entry_confirmed": structure.entry_confirmed,
        "reversal_confirmations": structure.reversal_confirmations,
        "confirmation_state": structure.confirmation_state,
        "pcr": structure.pcr if math.isfinite(structure.pcr) else None,
        "pcr_bias": structure.pcr_bias,
        "false_breakout": structure.false_breakout,
        "trap_level": structure.trap_level,
        "entry_trigger": structure.entry_trigger,
        "invalidation_rule": structure.invalidation_rule,
        "support_1": structure.support_1,
        "support_2": structure.support_2,
        "resistance_1": structure.resistance_1,
        "resistance_2": structure.resistance_2,
        "latest_completed_3m_bar": (
            str(completed_index_3m["timestamp"].iloc[-1])
            if not completed_index_3m.empty else ""
        ),
        "components": structure.components,
        "regime_direction": market_regime.get("direction", "NEUTRAL"),
        "market_intensity": market_regime.get("intensity", "UNKNOWN"),
        "near_structural_level": bool(market_regime.get("near_structural_level", False)),
        "reversal_price_confirmed": bool(market_regime.get("reversal_price_confirmed", False)),
        "adx": market_regime.get("adx") if math.isfinite(safe_float(market_regime.get("adx"), float("nan"))) else None,
        "rsi_3m": market_regime.get("rsi_3m") if math.isfinite(safe_float(market_regime.get("rsi_3m"), float("nan"))) else None,
        "rsi_15m": market_regime.get("rsi_15m") if math.isfinite(safe_float(market_regime.get("rsi_15m"), float("nan"))) else None,
        "regime_reason": market_regime.get("reason", ""),
        "tod_window": tod_window,
        "expiry_day": is_expiry_day,
    }
    state["option_oi_snapshot"] = build_option_oi_snapshot(chain, expiry)
    state["option_flow_by_strike"] = option_flow_by_strike
    state["persistent_direction"] = (
        structure.direction if structure.direction in {"BULLISH", "BEARISH"}
        else (seed_direction or "")
    ) or None
    save_state(state)

    logger.info(
        "PERSISTENT MARKET CONTEXT: persisted=%s immediate_previous=%s",
        state.get("persistent_direction") or "NONE",
        previous_direction or "NONE",
    )
    logger.info(
        "PREDICTION: %s | %s | confidence=%.1f score=%+.2f",
        structure.direction,
        structure.interpretation,
        structure.confidence,
        structure.score,
    )

    active_trade = active_trade_from_state(state)
    if active_trade is not None:
        migrated = migrate_active_trade_to_v25(
            active_trade,
            chain=chain,
            spot=spot,
            structure=structure,
            price_session=index_session,
            change_oi_by_strike=option_flow_by_strike,
        )
        if migrated:
            state["active_trade"] = active_trade
            save_state(state)
        monitor_active_trade(
            state,
            structure,
            chain=chain,
            price_session=index_session,
        )
        return None

    # Prevent stop/exit -> immediate re-entry churn. A fresh 3m candle and a
    # short cooldown are required before another trade can be opened. This is
    # especially important on expiry day when ATM can move by one strike quickly.
    last_completed = state.get("last_completed_trade")
    if isinstance(last_completed, dict):
        closed_at_raw = str(last_completed.get("closed_at", ""))
        try:
            closed_at = pd.Timestamp(closed_at_raw)
            if closed_at.tzinfo is None:
                closed_at = closed_at.tz_localize(IST)
            else:
                closed_at = closed_at.tz_convert(IST)
            elapsed = (pd.Timestamp(now_ist()) - closed_at).total_seconds() / 60.0
            if elapsed < max(REENTRY_COOLDOWN_MINUTES, 0):
                logger.info(
                    "RE-ENTRY COOLDOWN: %.1f/%.1f minutes elapsed after %s; no new trade.",
                    elapsed, max(REENTRY_COOLDOWN_MINUTES, 0), last_completed.get("outcome", "EXIT"),
                )
                return None
        except Exception:
            pass

    completed_session_bars = len(completed_index_3m)
    if REENTRY_REQUIRE_NEW_3M_BAR:
        last_exit_bar = str(last_completed.get("exit_3m_bar", "")) if isinstance(last_completed, dict) else ""
        current_completed_bar = (
            str(completed_index_3m["timestamp"].iloc[-1])
            if completed_session_bars else ""
        )
        if last_exit_bar and current_completed_bar and last_exit_bar == current_completed_bar:
            logger.info("RE-ENTRY WAIT: no new completed 3m bar since the previous exit.")
            return None
    opening_mode = now_time < MIN_ENTRY_TIME or completed_session_bars < 1
    if opening_mode:
        logger.info(
            "OPENING MODE: completed_index_3m_bars=%d time=%s; monitoring structure without forcing a trade.",
            completed_session_bars,
            now_time.strftime("%H:%M:%S"),
        )
        return None

    intensity = str(market_regime.get("intensity", "UNKNOWN")).upper()
    regime_direction = str(market_regime.get("direction", "NEUTRAL")).upper()
    adx_value = safe_float(market_regime.get("adx"), float("nan"))
    if intensity in {"SIDEWAYS", "UNKNOWN"}:
        logger.info("NO TRADE: market intensity=%s; reason=%s", intensity, market_regime.get("reason", ""))
        return None
    if regime_direction not in {"BULLISH", "BEARISH"}:
        logger.info("NO TRADE: market-regime direction is neutral.")
        return None
    if tod_window == "MIDDAY" and (not math.isfinite(adx_value) or adx_value < MIDDAY_MIN_ADX):
        logger.info("NO TRADE: midday momentum gate requires ADX >= %.1f; actual=%s.", MIDDAY_MIN_ADX, adx_value)
        return None

    # Exhaustion is the only controlled counter-trend exception. RSI divergence
    # near the matching structural wall is insufficient by itself: the latest
    # completed 3m bar must break the prior bar's extreme, Change-OI must strongly
    # agree with the reversal, and futures positioning must not strongly oppose it.
    flow_value = safe_float(structure.components.get("structure_change_oi"), 0.0)
    reversal_price_confirmed = bool(market_regime.get("reversal_price_confirmed", False))
    if regime_direction == "BULLISH":
        aligned_oi = flow_value >= STRUCTURE_CHANGE_OI_STRONG
        opposing_futures = bool(
            safe_float(structure.components.get("structure_futures_conflict_bullish"), 0.0) > 0.5
            or (structure.futures_bias < 0 and structure.futures_oi_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH)
        )
    else:
        aligned_oi = flow_value <= -STRUCTURE_CHANGE_OI_STRONG
        opposing_futures = bool(
            safe_float(structure.components.get("structure_futures_conflict_bearish"), 0.0) > 0.5
            or (structure.futures_bias > 0 and structure.futures_oi_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH)
        )
    exhaustion_entry = bool(
        intensity == "EXHAUSTION"
        and market_regime.get("near_structural_level", False)
        and reversal_price_confirmed
        and aligned_oi
        and not opposing_futures
    )
    if intensity == "EXHAUSTION" and not exhaustion_entry:
        logger.info(
            "NO TRADE: exhaustion setup not fully confirmed; near_level=%s price_break=%s "
            "flow=%+.3f flow_aligned=%s futures_conflict=%s.",
            market_regime.get("near_structural_level", False), reversal_price_confirmed,
            flow_value, aligned_oi, opposing_futures,
        )
        return None

    if regime_direction != structure.direction and not exhaustion_entry:
        logger.info(
            "NO TRADE: regime direction=%s disagrees with PA/OI structure direction=%s.",
            regime_direction, structure.direction,
        )
        return None

    entry_structure = structure
    if exhaustion_entry:
        exhaustion_phase = f"EXHAUSTION_{regime_direction}"
        exhaustion_trigger = (
            f"Counter-trend exhaustion scalp: confirmed {regime_direction.lower()} 3m/15m RSI divergence "
            "at an OI structural level, local price reversal through the prior 3m bar extreme, and aligned Change-OI."
        )
        exhaustion_invalidation = (
            "Exit if the underlying breaches the structural stop or the reversal loses its OI/price confirmation; "
            "do not assume an exhaustion signal is a new full-session trend."
        )
        entry_structure = replace(
            structure,
            direction=regime_direction,
            score=2.0 if regime_direction == "BULLISH" else -2.0,
            confidence=min(structure.confidence, 72.0),
            interpretation=f"CONFIRMED EXHAUSTION {regime_direction} — COUNTER-TREND SCALP",
            market_phase=exhaustion_phase,
            entry_confirmed=True,
            confirmation_state="EXHAUSTION_REVERSAL_CONFIRMED",
            entry_trigger=exhaustion_trigger,
            invalidation_rule=exhaustion_invalidation,
            reasons=list(structure.reasons) + [
                f"EXHAUSTION OVERRIDE: divergence={market_regime.get('divergence')}; "
                f"near_level={market_regime.get('near_structural_level')}; "
                f"price_break_confirmed={reversal_price_confirmed}; Change-OI={flow_value:+.3f}; "
                f"futures_conflict={opposing_futures}."
            ],
        )

    allowed_matrix_states = {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}
    matrix_state = (
        structure.market_phase[:-10]
        if structure.market_phase.endswith("_CONFIRMED")
        else structure.market_phase
    )
    if not exhaustion_entry and matrix_state not in allowed_matrix_states:
        logger.info("No entry: PA/OI structure not continuous: %s", structure.market_phase)
        return None
    if not exhaustion_entry and not structure.entry_confirmed:
        logger.info(
            "No entry: confirmation/tactical gate failed. direction=%s phase=%s state=%s invalidations=%d/%d PCR_bias=%+d",
            structure.direction, structure.market_phase, structure.confirmation_state,
            structure.reversal_confirmations, MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED, structure.pcr_bias,
        )
        return None

    volatility_unit = max(safe_float(structure.components.get("volatility_unit"), 50.0), 1.0)
    vwap_distance_atr = abs(float(spot) - float(structure.vwap)) / volatility_unit
    latest_3m_move_atr = abs(float(structure.components.get("recent3_movement_atr", 0.0)))
    latest_completed_bar = (
        completed_index_3m["timestamp"].iloc[-1]
        if not completed_index_3m.empty
        else None
    )
    persistence_phase = entry_structure.market_phase
    required_persistence = (
        MIDDAY_MIN_PERSISTENCE if tod_window == "MIDDAY"
        else max(2, CONTINUATION_CONFIRMATIONS_REQUIRED) if exhaustion_entry
        else CONTINUATION_CONFIRMATIONS_REQUIRED
    )
    persistence_ok, persistence_count = update_continuation_persistence(
        state,
        persistence_phase,
        latest_completed_3m_bar=latest_completed_bar,
        required_confirmations=required_persistence,
    )
    logger.info(
        "STRUCTURAL ENTRY CHECK: phase=%s persistence=%d/%d support=%.2f resistance=%.2f "
        "ChangeOI=%+.3f VWAP=%.2f; regime=%s/%s.",
        persistence_phase,
        persistence_count,
        required_persistence,
        entry_structure.support_1,
        entry_structure.resistance_1,
        flow_value,
        entry_structure.vwap,
        regime_direction,
        intensity,
    )
    if not persistence_ok:
        logger.info(
            "No entry: structural persistence requires %d distinct completed-bar confirmation(s); got %d.",
            max(required_persistence, 1), persistence_count,
        )
        save_state(state)
        return None
    timing_state = "CONFIRMED_EXHAUSTION_REVERSAL" if exhaustion_entry else "STRUCTURAL_CONTINUATION"

    target_u1, target_u2, stop_u, level_meta = determine_structural_trade_levels(
        chain,
        spot,
        entry_structure,
        index_session,
        change_oi_by_strike=option_flow_by_strike,
    )
    logger.info(
        "ENTRY PA/OI LEVELS: T1=%.2f(%s) T2=%.2f(%s) SL=%.2f(%s)",
        target_u1, level_meta.get("t1_source", ""),
        target_u2, level_meta.get("t2_source", ""),
        stop_u, level_meta.get("sl_source", ""),
    )

    option_micro_metrics = collect_option_premium_vwaps(
        chain, spot, regime_direction, intensity,
        is_expiry_day=is_expiry_day, now=now_ist(),
    )
    try:
        option = select_directional_option(
            chain=chain,
            direction=regime_direction,
            spot=spot,
            target_underlying_1=target_u1,
            change_oi_by_strike=option_flow_by_strike,
            market_intensity=intensity,
            is_expiry_day=is_expiry_day,
            now=now_ist(),
            option_metrics_by_instrument=option_micro_metrics,
            oi_velocity_by_strike=oi_velocity_by_strike,
        )
        validate_continuous_option_entry(
            option=option,
            chain=chain,
            direction=regime_direction,
            market_phase=entry_structure.market_phase,
            spot=spot,
            market_intensity=intensity,
            is_expiry_day=is_expiry_day,
            now=now_ist(),
        )
    except ScannerError as exc:
        logger.warning("NO TRADE: option strike selection rejected all candidates: %s", exc)
        save_state(state)
        return None
    target1, target2, stop_loss = target_u1, target_u2, stop_u
    underlying_stop, underlying_target1, underlying_target2 = stop_u, target_u1, target_u2

    setup_label = "CONFIRMED EXHAUSTION COUNTER-TREND SCALP" if exhaustion_entry else "STRUCTURAL CONTINUATION ENTRY"
    reasons = list(entry_structure.reasons)
    reasons.extend([
        f"Setup type: {setup_label}.",
        f"Entry timing: {timing_state}; index VWAP distance={vwap_distance_atr:.2f} ATR; latest 3m move={latest_3m_move_atr:.2f} ATR; completed index 3m bars={completed_session_bars}.",
        f"Regime matrix: {regime_direction}/{intensity}; ADX={adx_value:.2f}; RSI3m={safe_float(market_regime.get('rsi_3m'), float('nan')):.2f}; time window={tod_window}; {market_regime.get('reason', '')}.",
        f"Permitted strikes={permitted_strikes_for_regime(nearest_strike(spot, sorted(chain_rows(chain))), strike_step(sorted(chain_rows(chain))), regime_direction, intensity, is_expiry_day=is_expiry_day, now=now_ist())}.",
        f"Index spot used for option ATM selection={spot:.2f}; futures LTP={futures_ltp_now:.2f}; futures/index basis={futures_ltp_now - spot:+.2f}.",
        f"Selected option metrics: LTP={option.ltp:.2f}, premium VWAP={option.premium_vwap:.2f}, spread={option.spread_pct:.2%}, theta burden={option.theta_burden_pct_day:.2%}/day, volume={option.volume:.0f}, OI={option.oi:.0f}, delta={option.delta:.3f}, flow score={option.flow_score:.3f}, VWAP score={option.vwap_score:.3f}, 15m OI momentum={option.oi_momentum_score:.3f}, delta weight={option.delta_weight:.3f}, call COI15m={option.call_oi_change_pct_15m:+.2f}%, put COI15m={option.put_oi_change_pct_15m:+.2f}% (baseline {option.oi_velocity_baseline_minutes:.1f}m).",
        f"PA/OI structural levels: NIFTY T1={underlying_target1:.2f}, T2={underlying_target2:.2f}, SL={underlying_stop:.2f}; option exit uses live LTP at the structural trigger.",
        "Primary entry alignment: NIFTY price vs VWAP + structural support/resistance + confirming Change-OI.",
        "Futures price/OI and PCR are context only; they do not override the PA/VWAP/Change-OI market structure.",
    ])

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
        direction=entry_structure.direction,
        regime=f"{entry_structure.interpretation} | {regime_direction}/{intensity} | ADX={adx_value:.2f}",
        market_state=entry_structure.market_phase,
        bias="Bullish" if entry_structure.direction == "BULLISH" else "Bearish",
        entry_trigger=entry_structure.entry_trigger,
        invalidation_rule=entry_structure.invalidation_rule,
        confidence=entry_structure.confidence,
        spot=spot,
        futures_state=structure.futures_regime,
        option_type=option.option_type,
        strike=option.strike,
        trading_symbol=option.trading_symbol,
        instrument_key=option.instrument_key,
        entry=option.ltp,
        target_1=target1,
        target_2=target2,
        stop_loss=stop_loss,
        underlying_stop=underlying_stop,
        underlying_target_1=underlying_target1,
        underlying_target_2=underlying_target2,
        delta=option.delta,
        theta=option.theta,
        support_1=entry_structure.support_1,
        support_2=entry_structure.support_2,
        resistance_1=entry_structure.resistance_1,
        resistance_2=entry_structure.resistance_2,
        reasons=reasons,
        market_intensity=intensity,
    )

def _synthetic_structure_chain(
    spot: float,
    support: float,
    resistance: float,
    put_change: float = 1000000.0,
    call_change: float = -1000000.0,
) -> tuple[list[dict[str, Any]], dict[float, dict[str, float]]]:
    strikes = sorted(set([support, spot, resistance, support - 50, resistance + 50]))
    chain: list[dict[str, Any]] = []
    changes: dict[float, dict[str, float]] = {}
    for k in strikes:
        chain.append({
            "strike_price": float(k),
            "expiry": "2026-10-13",
            "call_options": {
                "instrument_key": f"CE{k}",
                "market_data": {
                    "ltp": 110.0 if k < spot else 90.0,
                    "close_price": 100.0,
                    "oi": 1000000.0 if abs(k - resistance) < 1 else 500000.0,
                    "prev_oi": 500000.0,
                    "volume": 10000,
                    "bid_price": 109.5,
                    "ask_price": 110.5,
                    "bid_qty": 100,
                    "ask_qty": 100,
                },
                "option_greeks": {"delta": 0.55, "gamma": 0.01, "theta": -2.0, "iv": 20.0},
            },
            "put_options": {
                "instrument_key": f"PE{k}",
                "market_data": {
                    "ltp": 110.0 if k >= spot else 90.0,
                    "close_price": 100.0,
                    "oi": 1000000.0 if abs(k - support) < 1 else 500000.0,
                    "prev_oi": 500000.0,
                    "volume": 10000,
                    "bid_price": 109.5,
                    "ask_price": 110.5,
                    "bid_qty": 100,
                    "ask_qty": 100,
                },
                "option_greeks": {"delta": -0.55, "gamma": 0.01, "theta": -2.0, "iv": 20.0},
            },
        })
        call_delta = call_change if k >= spot else 0.0
        put_delta = put_change if k <= spot else 0.0
        changes[float(k)] = {
            "call_oi_change": call_delta,
            "put_oi_change": put_delta,
            "call_change": call_delta,
            "put_change": put_delta,
        }
    return chain, changes


def _synthetic_candles(
    values: list[float],
    oi: Optional[list[float]] = None,
    start: str = "2026-09-10 09:15",
) -> pd.DataFrame:
    index = pd.date_range(start, periods=len(values), freq="3min", tz="Asia/Kolkata")
    df = pd.DataFrame(
        {
            "timestamp": index.tz_convert("UTC"),
            "open": values,
            "high": [x + 2 for x in values],
            "low": [x - 2 for x in values],
            "close": values,
            "volume": [1000.0] * len(values),
            "oi": oi if oi is not None else [np.nan] * len(values),
        }
    )
    return df


def self_test() -> None:
    """Deterministic regression tests for V27 regime, strike-routing, VWAP and exit gates."""
    def mk_candles(values: list[float], oi: Optional[list[float]] = None) -> pd.DataFrame:
        return _synthetic_candles(values, oi=oi)

    # Regression: a weak intraday snapshot must not override the clearly bullish
    # session Change-OI score seen around 09:25 IST on 2026-10-09.
    eff, bias, source, conflict = resolve_change_oi_flow(-0.155, +0.760, "INTRADAY_SNAPSHOT")
    assert eff == 0.0 and bias == 0 and conflict and source == "INTRADAY_DAY_CONFLICT"

    # Continuation requires two distinct completed 3m bars, not repeated scans of
    # the same bar and not a single early-market classification.
    persistence_state: dict[str, Any] = {}
    ready1, count1 = update_continuation_persistence(
        persistence_state, "CONTINUOUS_BULLISH", "2026-10-09T03:30:00+00:00"
    )
    ready_same, count_same = update_continuation_persistence(
        persistence_state, "CONTINUOUS_BULLISH", "2026-10-09T03:30:00+00:00"
    )
    ready2, count2 = update_continuation_persistence(
        persistence_state, "CONTINUOUS_BULLISH", "2026-10-09T03:33:00+00:00"
    )
    assert not ready1 and count1 == 1
    assert not ready_same and count_same == 1
    assert ready2 and count2 == 2

    # Exhaustion reversal setups also require distinct completed-bar persistence.
    exhaustion_state: dict[str, Any] = {}
    exhaustion_ready1, exhaustion_count1 = update_continuation_persistence(
        exhaustion_state, "EXHAUSTION_BULLISH", "2026-10-09T03:45:00+00:00", required_confirmations=2
    )
    exhaustion_ready2, exhaustion_count2 = update_continuation_persistence(
        exhaustion_state, "EXHAUSTION_BULLISH", "2026-10-09T03:48:00+00:00", required_confirmations=2
    )
    assert not exhaustion_ready1 and exhaustion_count1 == 1
    assert exhaustion_ready2 and exhaustion_count2 == 2

    # Basic price-action volatility and completed-bar behavior.
    down = mk_candles([100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85])
    up = mk_candles([85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100])
    assert calculate_atr(down, ATR_PERIOD).iloc[-1] > 0
    assert calculate_atr(up, ATR_PERIOD).iloc[-1] > 0

    fut_bear = mk_candles([100, 99.5, 99, 98.5, 98, 97.5, 97, 96.5, 96], [1000, 1020, 1045, 1070, 1100, 1130, 1160, 1190, 1220])
    fut_info = futures_oi_structure(fut_bear)
    assert fut_info["regime"] == "SHORT_BUILDUP"
    assert fut_info["bias"] == -1

    bearish_levels = _synthetic_structure_chain(96.5, 95.0, 105.0, 1000000.0, -900000.0)
    bearish_chain, bearish_flow = bearish_levels
    chain_map = chain_oi_support_resistance(
        bearish_chain, 96.5, bearish_flow, expiry="2026-10-13"
    )
    assert math.isfinite(chain_map["support_1"]) and math.isfinite(chain_map["resistance_1"])

    conflict_levels = dict(chain_map)
    conflict_levels.update({
        "support_1": 80.0, "support_2": 70.0,
        "resistance_1": 90.0, "resistance_2": 100.0,
        "support_source": "OPTION_OI", "resistance_source": "OPTION_OI",
        "flow_mode": "INTRADAY_SNAPSHOT", "change_flow_score": -0.155,
    })
    conflicted_structure = build_market_structure(
        85.0, up, up, conflict_levels, +0.760,
        previous_direction=None, previous_phase=None, price_session=down,
    )
    assert not conflicted_structure.entry_confirmed
    assert conflicted_structure.confirmation_state == "FLOW_CONFLICT"

    # Continuous bearish: below VWAP + sustained bearish PA + bearish Change-OI.
    structure = build_market_structure(
        85.0, fut_bear, fut_bear, chain_map, -0.40,
        previous_direction=None, previous_phase=None, price_session=down
    )
    assert structure.direction == "BEARISH"
    assert structure.market_phase == "CONTINUOUS_BEARISH"
    assert structure.entry_confirmed

    # Pullback regression: a small bounce must not erase an established bearish trend.
    pullback = mk_candles([120, 118, 116, 114, 111, 109, 110, 111])
    pull_levels = dict(chain_map)
    pull_levels.update({"support_1": 105.0, "support_2": 100.0, "resistance_1": 125.0, "resistance_2": 130.0, "flow_mode": "INTRADAY_SNAPSHOT", "change_flow_score": -0.70, "change_flow_bias": -1})
    pull = build_market_structure(
        111.0, fut_bear, fut_bear, pull_levels, -0.40,
        previous_direction="BEARISH", previous_phase="CONTINUOUS_BEARISH", price_session=pullback
    )
    assert pull.direction == "BEARISH" and pull.market_phase == "CONTINUOUS_BEARISH" and pull.entry_confirmed

    # The trend may remain continuous above support; support break is not mandatory.
    above_support = mk_candles([120, 118, 116, 114, 111, 109, 110, 112])
    above_levels = dict(pull_levels)
    above_levels.update({"support_1": 105.0, "support_2": 100.0})
    cont = build_market_structure(
        112.0, fut_bear, fut_bear, above_levels, -0.35,
        previous_direction="BEARISH", previous_phase="CONTINUOUS_BEARISH", price_session=above_support
    )
    assert cont.market_phase == "CONTINUOUS_BEARISH" and cont.entry_confirmed

    # V16 regression: structural support/resistance must remain distinct.
    v16 = dict(pull_levels)
    v16.update({"support_1": 92.0, "resistance_1": 100.0, "flow_mode": "INTRADAY_SNAPSHOT", "change_flow_score": -0.45, "change_flow_bias": -1})
    v16r = build_market_structure(96.0, fut_bear, fut_bear, v16, -0.45, price_session=mk_candles([104,102,100,99,98,97,96]))
    assert v16r.support_1 < v16r.resistance_1

    # Regression: a previous resistance that price has broken must never be
    # returned as the current resistance below price (the 09-Oct 09:40 defect).
    broken_resistance_levels = dict(pull_levels)
    broken_resistance_levels.update({
        "support_1": 22400.0, "support_2": 22350.0,
        "resistance_1": 22450.0, "resistance_2": 22500.0,
        "previous_support_1": 22350.0, "previous_resistance_1": 22400.0,
        "support_source": "OPTION_OI", "resistance_source": "OPTION_OI",
        "flow_mode": "INTRADAY_SNAPSHOT", "change_flow_score": 0.75,
    })
    rising_levels_candles = mk_candles([22320, 22340, 22360, 22380, 22400, 22417])
    broken_resistance_result = build_market_structure(
        22417.0, up, up, broken_resistance_levels, 0.75,
        previous_direction="BULLISH", previous_phase="CONTINUOUS_BULLISH",
        price_session=rising_levels_candles,
    )
    assert broken_resistance_result.support_1 < 22417.0
    assert broken_resistance_result.resistance_1 > 22417.0
    assert broken_resistance_result.support_1 < broken_resistance_result.resistance_1

    # Regression: strong opposing futures OI blocks an otherwise-bullish entry.
    future_conflict_result = build_market_structure(
        22417.0, fut_bear, fut_bear, broken_resistance_levels, 0.75,
        previous_direction="BULLISH", previous_phase="CONTINUOUS_BULLISH",
        price_session=rising_levels_candles,
    )
    assert not future_conflict_result.entry_confirmed
    assert future_conflict_result.confirmation_state == "FUTURES_CONFLICT"

    # Regime routing regression: expiry override, time-of-day and intensity arrays.
    test_now = datetime(2026, 10, 9, 14, 0, tzinfo=IST)
    assert permitted_strikes_for_regime(74100, 50, "BULLISH", "NORMAL", now=test_now) == [74050, 74100]
    assert permitted_strikes_for_regime(74100, 50, "BEARISH", "NORMAL", now=test_now) == [74100, 74150]
    assert permitted_strikes_for_regime(74100, 50, "BULLISH", "STRONG", now=test_now) == [74100, 74150, 74200]
    assert permitted_strikes_for_regime(74100, 50, "BEARISH", "STRONG", now=test_now) == [74000, 74050, 74100]
    assert permitted_strikes_for_regime(74100, 50, "BULLISH", "STRONG", is_expiry_day=True, now=test_now) == [74050, 74100]
    assert permitted_strikes_for_regime(74100, 50, "BEARISH", "SIDEWAYS", now=test_now) == []
    midday_now = datetime(2026, 10, 9, 11, 0, tzinfo=IST)
    assert permitted_strikes_for_regime(74100, 50, "BULLISH", "STRONG", now=midday_now) == [74050, 74100]
    assert permitted_strikes_for_regime(74100, 50, "BULLISH", "EXHAUSTION", now=test_now) == [74000, 73950]

    # Option direction, strict option VWAP/COI velocity, delta and strike-universe regression.
    simple_chain = []
    flow = {}
    for strike in [73950, 74000, 74050, 74100, 74150, 74200, 74250]:
        simple_chain.append({
            "strike_price": strike, "expiry": "2026-10-13",
            "call_options": {"instrument_key": f"CE{strike}", "market_data": {"ltp": 100.0, "oi": 50000, "prev_oi": 49000, "volume": 10000, "bid_price": 99.5, "ask_price": 100.5, "bid_qty": 100, "ask_qty": 100}, "option_greeks": {"delta": 0.75 if strike <= 74000 else 0.55, "theta": -2.0}},
            "put_options": {"instrument_key": f"PE{strike}", "market_data": {"ltp": 100.0, "oi": 50000, "prev_oi": 49000, "volume": 10000, "bid_price": 99.5, "ask_price": 100.5, "bid_qty": 100, "ask_qty": 100}, "option_greeks": {"delta": -0.75 if strike >= 74200 else -0.55, "theta": -2.0}},
        })
        flow[strike] = {
            "call_bias": 1,
            "put_bias": -1,
            "call_oi_change": -1000,
            "put_oi_change": 1000,
        }
    option_vwaps = {
        f"{side}{strike}": {"premium_vwap": 90.0}
        for strike in [73950, 74000, 74050, 74100, 74150, 74200, 74250]
        for side in ("CE", "PE")
    }
    bull_velocity = {
        float(strike): {"available": True, "call_oi_change_pct": -0.02, "put_oi_change_pct": 0.02, "baseline_minutes": 20.0}
        for strike in [73950, 74000, 74050, 74100, 74150, 74200, 74250]
    }
    bear_velocity = {
        float(strike): {"available": True, "call_oi_change_pct": 0.02, "put_oi_change_pct": -0.02, "baseline_minutes": 20.0}
        for strike in [73950, 74000, 74050, 74100, 74150, 74200, 74250]
    }
    ce = select_directional_option(
        simple_chain, "BULLISH", 74100.0, target_underlying_1=74200.0,
        change_oi_by_strike=flow, market_intensity="NORMAL", now=test_now,
        option_metrics_by_instrument=option_vwaps, oi_velocity_by_strike=bull_velocity,
    )
    pe = select_directional_option(
        simple_chain, "BEARISH", 74100.0, target_underlying_1=73950.0,
        change_oi_by_strike=flow, market_intensity="NORMAL", now=test_now,
        option_metrics_by_instrument=option_vwaps, oi_velocity_by_strike=bear_velocity,
    )
    assert ce.option_type == "CE" and ce.strike in {74050.0, 74100.0}
    assert pe.option_type == "PE" and pe.strike in {74100.0, 74150.0}
    assert ce.premium_vwap < ce.ltp and ce.oi_momentum_score > 0.9
    validate_continuous_option_entry(
        ce, simple_chain, "BULLISH", "CONTINUOUS_BULLISH", 74100.0,
        market_intensity="NORMAL", now=test_now,
    )
    validate_continuous_option_entry(
        pe, simple_chain, "BEARISH", "CONTINUOUS_BEARISH", 74100.0,
        market_intensity="NORMAL", now=test_now,
    )

    # Strict option premium VWAP filter must reject a candidate with LTP below VWAP.
    bad_vwap_map = {key: {"premium_vwap": 101.0} for key in option_vwaps}
    try:
        select_directional_option(
            simple_chain, "BULLISH", 74100.0, change_oi_by_strike=flow,
            market_intensity="NORMAL", now=test_now, option_metrics_by_instrument=bad_vwap_map,
            oi_velocity_by_strike=bull_velocity,
        )
        raise AssertionError("LTP <= premium VWAP should be rejected")
    except ScannerError as exc:
        assert "premium VWAP" in str(exc) or "VWAP" in str(exc)

    # Normal regimes enforce the live delta floor rather than fabricating a delta.
    low_delta_chain = json.loads(json.dumps(simple_chain))
    for row in low_delta_chain:
        row["call_options"]["option_greeks"]["delta"] = 0.45
    try:
        select_directional_option(
            low_delta_chain, "BULLISH", 74100.0, change_oi_by_strike=flow,
            market_intensity="NORMAL", now=test_now, option_metrics_by_instrument=option_vwaps,
            oi_velocity_by_strike=bull_velocity,
        )
        raise AssertionError("Delta below 0.50 should be rejected in NORMAL regime")
    except ScannerError as exc:
        assert "delta" in str(exc).lower()

    # 15-30 minute OI velocity is measured against a persisted snapshot, not daily prev_oi.
    oi_state = {"option_oi_history": [{
        "date": "2026-10-09", "expiry": "2026-10-13",
        "timestamp": "2026-10-09T09:40:00+05:30",
        "oi_by_instrument": {
            **{f"CE{k}": {"strike": float(k), "side": "CE", "oi": 50000.0} for k in [73950, 74000, 74050, 74100, 74150, 74200, 74250]},
            **{f"PE{k}": {"strike": float(k), "side": "PE", "oi": 50000.0} for k in [73950, 74000, 74050, 74100, 74150, 74200, 74250]},
        },
    }]}
    oi_velocity = update_option_oi_velocity_history(
        oi_state, simple_chain, "2026-10-13", now=datetime(2026, 10, 9, 10, 0, tzinfo=IST)
    )
    assert oi_velocity[74100.0]["available"] is True
    assert oi_velocity[74100.0]["baseline_minutes"] == 20.0

    # Stagnation breaker requires 3 completed 5-minute candles after entry.
    flat5 = pd.DataFrame({
        "timestamp": pd.date_range("2026-09-10 09:20", periods=3, freq="5min", tz="Asia/Kolkata").tz_convert("UTC"),
        "open": [100.0, 100.0, 100.0], "high": [100.04, 100.03, 100.04],
        "low": [99.96, 99.97, 99.96], "close": [100.0, 100.0, 100.0], "volume": [1000, 1000, 1000],
    })
    stagnant, _ = stagnation_exit_trigger({"opened_at": "2026-09-10 09:15:00 IST"}, flat5)
    assert stagnant

    # PA/OI T1/T2/SL must be underlying structural levels, not option-premium targets.
    trade_chain, trade_flow = _synthetic_structure_chain(22250.0, 22000.0, 22500.0, 3000000.0, -2000000.0)
    # Add a distinct second OI wall below T1.
    for row in trade_chain:
        if abs(float(row["strike_price"]) - 21900.0) < 0.01:
            row["put_options"]["market_data"]["oi"] = 2500000
            break
    target_structure = type("S", (), {"direction":"BEARISH", "support_1":22000.0, "support_2":21900.0, "resistance_1":22500.0, "resistance_2":22600.0, "vwap":22350.0})()
    t1, t2, sl, meta = determine_structural_trade_levels(trade_chain, 22250.0, target_structure, down, change_oi_by_strike=trade_flow)
    assert t1 == 22000.0 and t2 < t1 and sl > 22250.0
    assert meta["t1_source"] == "OPTION_OI_SUPPORT"

    # Post-T1 dynamic OI stop must be recalculated from current opposing OI and ratchet favorably.
    dyn_chain, dyn_flow = _synthetic_structure_chain(22050.0, 21900.0, 22200.0, 3000000.0, -1500000.0)
    dynamic, source, _ = dynamic_oi_stop_after_t1(dyn_chain, 22050.0, "BEARISH", down, entry_underlying=22250.0, change_oi_by_strike=dyn_flow)
    assert dynamic == 22100.0 or dynamic == 22200.0
    assert source.startswith("CURRENT_OI_")

    # Symmetric bullish PA/OI target structure: T1/T2 above spot and SL below spot.
    bull_chain, bull_flow = _synthetic_structure_chain(22250.0, 22000.0, 22500.0, -2000000.0, 3000000.0)
    bullish_structure = type("S", (), {"direction":"BULLISH", "support_1":22000.0, "support_2":21950.0, "resistance_1":22500.0, "resistance_2":22550.0, "vwap":22150.0})()
    bt1, bt2, bsl, bmeta = determine_structural_trade_levels(
        bull_chain, 22250.0, bullish_structure, up, change_oi_by_strike=bull_flow
    )
    assert bt1 == 22500.0 and bt2 > bt1 and bsl < 22250.0
    assert bmeta["t1_source"] == "OPTION_OI_RESISTANCE"

    # Post-T1 bullish dynamic stop must use current OI and ratchet upward only.
    dyn_bull_chain_1, dyn_bull_flow_1 = _synthetic_structure_chain(22050.0, 22000.0, 22200.0, 3000000.0, -1500000.0)
    dyn_trade = {"direction":"BULLISH", "entry_underlying":21900.0, "post_t1_dynamic_stop":None}
    changed_1, dyn_stop_1, dyn_source_1 = apply_dynamic_oi_stop_to_trade(
        dyn_trade, chain=dyn_bull_chain_1, spot=22050.0, price_session=up,
        latest_bar="2026-10-08T10:00:00+00:00", change_oi_by_strike=dyn_bull_flow_1
    )
    assert changed_1 and dyn_stop_1 == 22000.0 and dyn_source_1 == "CURRENT_OI_SUPPORT"
    dyn_bull_chain_2, dyn_bull_flow_2 = _synthetic_structure_chain(22050.0, 21950.0, 22200.0, 3000000.0, -1500000.0)
    changed_2, dyn_stop_2, dyn_source_2 = apply_dynamic_oi_stop_to_trade(
        dyn_trade, chain=dyn_bull_chain_2, spot=22050.0, price_session=up,
        latest_bar="2026-10-08T10:03:00+00:00", change_oi_by_strike=dyn_bull_flow_2
    )
    assert changed_2 is False and dyn_stop_2 == 22000.0 and dyn_source_2 == "CURRENT_OI_SUPPORT"

    # Migration must ignore stale legacy option-premium T1 flags and recompute from NIFTY PA/OI.
    legacy = {"direction":"BEARISH", "target_engine_version":"V22", "target_1":307.45, "target_2":314.31, "stop_loss":137.73, "underlying_target_1":22200.0, "underlying_target_2":22000.0, "underlying_stop":22385.0, "t1_hit":True, "entry_underlying":22250.0, "trading_symbol":"NIFTY PE", "entry":160.0}
    migrated = migrate_active_trade_to_v25(legacy, chain=trade_chain, spot=22250.0, structure=target_structure, price_session=down, change_oi_by_strike=trade_flow)
    assert migrated and legacy["target_engine_version"] == OPTION_TARGET_ENGINE_VERSION
    assert legacy["underlying_target_1"] == 22000.0 and legacy["t1_hit"] is False

    print("SELF-TEST PASSED.")


def main() -> int:
    logger.info("NIFTY SCANNER VERSION: %s", SCANNER_VERSION)

    if "--self-test" in sys.argv:
        self_test()
        return 0

    try:
        state = load_state()
        signal = execute_scan(state)

        if signal is None:
            logger.info("No actionable setup on this scan.")
            return 0

        active_trade = {
            "status": "ACTIVE",
            "trade_date": now_ist().date().isoformat(),
            "opened_at": signal.timestamp,
            "direction": signal.direction,
            "regime": signal.regime,
            "market_intensity": signal.market_intensity,
            "confidence": signal.confidence,
            "instrument_key": signal.instrument_key,
            "trading_symbol": signal.trading_symbol,
            "option_type": signal.option_type,
            "strike": signal.strike,
            "entry": signal.entry,
            "entry_underlying": signal.spot,
            "t1_hit": False,
            "t1_hit_at": "",
            "post_t1_dynamic_stop": None,
            "post_t1_dynamic_stop_source": "",
            "post_t1_dynamic_stop_updated_at": "",
            "target_1": signal.target_1,
            "target_2": signal.target_2,
            "stop_loss": signal.stop_loss,
            "underlying_stop": signal.underlying_stop,
            "underlying_target_1": signal.underlying_target_1,
            "underlying_target_2": signal.underlying_target_2,
            "delta": signal.delta,
            "theta": signal.theta,
            "target_engine_version": OPTION_TARGET_ENGINE_VERSION,
            "reversal_confirmations": 0,
            "market_alignment_failures": 0,
            "last_market_direction": signal.direction,
            "last_market_confidence": signal.confidence,
            "last_ltp": signal.entry,
            "entry_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            "underlying_stop_armed_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            "intrabar_last_checked_at": signal.timestamp,
        }

        state["active_trade"] = active_trade
        state["last_signal"] = asdict(signal)
        state["last_signal_hash"] = signal_hash(signal)
        state["last_signal_timestamp"] = signal.timestamp
        save_state(state)

        print(format_engine_output(signal))

        send_email(
            f"NIFTY {signal.direction} {signal.trading_symbol}",
            signal_email_body(signal),
        )

        logger.info(
            "NEW SIGNAL LOCKED: %s | entry_option=%.2f NIFTY_T1=%.2f NIFTY_T2=%.2f NIFTY_SL=%.2f",
            signal.trading_symbol,
            signal.entry,
            signal.underlying_target_1,
            signal.underlying_target_2,
            signal.underlying_stop,
        )
        return 0

    except ScannerError as exc:
        logger.error("Scanner error: %s", exc)
        return 1
    except Exception:
        logger.error("Fatal scanner failure:\n%s", traceback.format_exc())
        return 1


if __name__ == "__main__":
    sys.exit(main())
