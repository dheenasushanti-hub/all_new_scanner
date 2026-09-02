"""
SENSEX Predictive Options Market Scanner

Strategy:
- SENSEX 3-minute and 15-minute Supertrend: (10, 3)
- Full current-session VWAP + price structure
- Dynamic current-month SENSEX futures discovery
- Futures price/OI regime
- Current-week option-chain OI / previous OI
- Strike-level CE/PE OI differential with proximity weighting
- Option price/OI confirmation for the selected contract
- Pre-breakout prediction instead of waiting for an option breakout
- Reversal detection
- Directional ITM option selection:
      bullish -> ATM-1 CE, fallback ATM-2 CE
      bearish -> ATM+1 PE, fallback ATM+2 PE
- No option-extension rejection for predictive entries
- T1 based on projected 3-minute breakout level
- T2 based on projected 15-minute resistance/support
- Option premium targets translated using live option Delta/Gamma
- Stop loss = 15% below entry premium
- Duplicate signal suppression via persisted state
- Email notifications only for new actionable signals

No order placement is performed.
"""

from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import smtplib
import sys
import traceback
import urllib.parse
import time as time_module
from dataclasses import dataclass, asdict
from datetime import datetime, time
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Optional
from zoneinfo import ZoneInfo


import numpy as np
import pandas as pd
import requests


# =============================================================================
# CONFIGURATION
# =============================================================================

IST = ZoneInfo("Asia/Kolkata")

BASE_URL = "https://api.upstox.com"

SENSEX_KEY = os.getenv(
    "SENSEX_INSTRUMENT_KEY",
    "BSE_INDEX|SENSEX",
).strip()

UPSTOX_TOKEN = os.getenv(
    "UPSTOX_ANALYTICS_TOKEN",
    "",
).strip()

EMAIL_SENDER = os.getenv(
    "EMAIL_SENDER",
    "",
).strip()

EMAIL_PASSWORD = os.getenv(
    "EMAIL_PASSWORD",
    "",
).strip()

EMAIL_RECEIVER = os.getenv(
    "EMAIL_RECEIVER",
    "",
).strip()

SMTP_HOST = os.getenv(
    "SMTP_HOST",
    "smtp.gmail.com",
).strip()

SMTP_PORT = int(
    os.getenv(
        "SMTP_PORT",
        "465",
    )
)

REQUEST_TIMEOUT = int(
    os.getenv(
        "REQUEST_TIMEOUT",
        "20",
    )
)

STATE_FILE = Path(
    os.getenv(
        "STATE_FILE",
        "state/sensex_market_state.json",
    )
)

SIGNAL_THRESHOLD = float(
    os.getenv(
        "SIGNAL_THRESHOLD",
        "60",
    )
)

PREDICTION_MIN_CONFLUENCE = 2
LOCK_SETUP_MINUTES = 45

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)

SUPERTREND_PERIOD = 10
SUPERTREND_FACTOR = 3.0

STRUCTURE_LOOKBACK_3M = 8
STRUCTURE_LOOKBACK_15M = 6

OPTION_MIN_DELTA = 0.35
OPTION_MAX_DELTA = 0.85

# BUY-ONLY option momentum guardrails. A strike must show positive premium
# momentum before it can be selected or locked.
BUY_OPTION_LOOKBACK = 6
BUY_OPTION_MIN_CANDLES = 5
BUY_OPTION_MIN_RETURN_PCT = 0.10

# Noise controls for a 5-minute workflow.
VWAP_FLAT_SLOPE_EPSILON = 0.10
FUTURES_BASIS_EPSILON_POINTS = 1.00
FUTURES_REGIME_MIN_PRICE_MOVE = 0.50
FUTURES_REGIME_MIN_OI_CHANGE = 1.0

MAX_SIGNAL_AGE_MINUTES = 15

# =============================================================================
# SIDEWAYS / RANGE MARKET FILTER
# =============================================================================

SIDEWAYS_LOOKBACK_3M = 12
SIDEWAYS_LOOKBACK_15M = 6

# Total high-low range relative to ATR.
SIDEWAYS_MAX_RANGE_ATR_3M = 3.0
SIDEWAYS_MAX_RANGE_ATR_15M = 2.5

# Net movement from first close to latest close relative to ATR.
SIDEWAYS_MAX_NET_MOVE_ATR_3M = 0.75
SIDEWAYS_MAX_NET_MOVE_ATR_15M = 0.75

# Number of directional Supertrend flips allowed inside the lookback.
SIDEWAYS_MAX_SUPERTREND_FLIPS = 2

# OI score near zero means positioning is balanced.
SIDEWAYS_CHAIN_OI_SCORE = 0.05
SIDEWAYS_CHANGE_OI_SCORE = 0.10

# =============================================================================
# ENDPOINTS
# =============================================================================

INSTRUMENT_SEARCH_URL = (
    f"{BASE_URL}/v2/instruments/search"
)

OPTION_CHAIN_URL = (
    f"{BASE_URL}/v2/option/chain"
)

OPTION_CONTRACT_URL = (
    f"{BASE_URL}/v2/option/contract"
)

CHANGE_OI_URL = (
    f"{BASE_URL}/v2/market/change-oi"
)

MARKET_STATUS_URL = (
    f"{BASE_URL}/v2/market/status/BSE"
)

QUOTE_URL = (
    f"{BASE_URL}/v2/market-quote/quotes"
)
HISTORICAL_CANDLE_URL = (
    f"{BASE_URL}/v3/historical-candle"
)

# =============================================================================
# LOGGING
# =============================================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)

logger = logging.getLogger("sensex_scanner")


# =============================================================================
# DATA CLASSES
# =============================================================================

@dataclass
class FuturesContract:
    instrument_key: str
    trading_symbol: str
    expiry: str


@dataclass
class OptionCandidate:
    instrument_key: str
    trading_symbol: str
    option_type: str
    strike: float
    expiry: str
    ltp: float
    oi: float
    prev_oi: float
    delta: float
    gamma: float
    iv: float


@dataclass
class Signal:
    timestamp: str
    direction: str
    regime: str
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
    underlying_trigger_3m: float
    underlying_target_15m: float
    delta: float
    gamma: float
    reasons: list[str]


# =============================================================================
# EXCEPTIONS
# =============================================================================

class ScannerError(Exception):
    pass


# =============================================================================
# TIME HELPERS
# =============================================================================

def now_ist() -> datetime:
    return datetime.now(IST)


def market_window_open() -> bool:

    current = now_ist()

    if current.weekday() >= 5:
        return False

    if is_bse_holiday(current):
        logger.info(
            "BSE holiday: %s. Scanner will not run.",
            current.strftime("%Y-%m-%d"),
        )
        return False

    return (
        MARKET_START
        <= current.time()
        <= MARKET_END
    )


# =============================================================================
# API HELPERS
# =============================================================================

def api_headers() -> dict[str, str]:
    if not UPSTOX_TOKEN:
        raise ScannerError(
            "UPSTOX_ANALYTICS_TOKEN is missing."
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

    last_error = None

    for attempt in range(1, retries + 1):

        try:
            response = requests.get(
                url,
                params=params,
                headers=api_headers(),
                timeout=REQUEST_TIMEOUT,
            )

        except requests.RequestException as exc:

            last_error = f"Network request failed: {exc}"

            if attempt < retries:
                wait_seconds = attempt * 2

                logger.warning(
                    "Request failed. Retry %d/%d in %d seconds: %s",
                    attempt,
                    retries,
                    wait_seconds,
                    last_error,
                )

                time_module.sleep(wait_seconds)
                continue

            raise ScannerError(last_error) from exc

        if response.status_code == 200:

            try:
                payload = response.json()

            except ValueError as exc:
                raise ScannerError(
                    "Upstox returned invalid JSON."
                ) from exc

            if not isinstance(payload, dict):
                raise ScannerError(
                    "Unexpected Upstox response structure."
                )

            if payload.get("status") == "error":
                raise ScannerError(
                    json.dumps(payload)[:1500]
                )

            return payload

        last_error = (
            f"Upstox HTTP {response.status_code}: "
            f"{response.text[:1000]}"
        )

        transient_error = response.status_code in {
            500,
            502,
            503,
            504,
        }

        logger.warning(
            "Upstox request failed | attempt=%d/%d | "
            "status=%s | url=%s | params=%s | response=%s",
            attempt,
            retries,
            response.status_code,
            url,
            params,
            response.text[:1000],
        )

        if transient_error and attempt < retries:

            wait_seconds = attempt * 2

            logger.info(
                "Transient Upstox server error. Retrying in %d seconds...",
                wait_seconds,
            )

            time_module.sleep(wait_seconds)
            continue

        raise ScannerError(last_error)

    raise ScannerError(
        last_error or "Unknown Upstox API error."
    )

# =============================================================================
# MARKET HOLIDAY
# =============================================================================

def is_bse_holiday(
    current_date: datetime,
) -> bool:
    """
    Uses Upstox's market-holiday API to determine whether
    BSE is closed on the current IST date.
    """

    date_string = current_date.strftime(
        "%Y-%m-%d"
    )

    url = (
        f"{BASE_URL}/v2/market/holidays/{date_string}"
    )

    try:
        payload = api_get(url)

        data = payload.get(
            "data"
        )

        # Upstox returns holiday information when the
        # requested date is a holiday.
        if isinstance(data, dict):
            return bool(data)

        if isinstance(data, list):
            return len(data) > 0

        return False

    except ScannerError as exc:
        logger.warning(
            "Holiday API unavailable: %s",
            exc,
        )

        # Do not silently assume a trading holiday when
        # the holiday service itself is unavailable.
        return False

# =============================================================================
# MARKET STATUS
# =============================================================================

def get_market_status() -> str:

    payload = api_get(
        MARKET_STATUS_URL
    )

    serialized = json.dumps(
        payload,
        default=str,
    ).lower()

    if '"open"' in serialized or "open" in serialized:
        return "OPEN"

    if "closed" in serialized:
        return "CLOSED"

    return "UNKNOWN"


# =============================================================================
# SENSEX QUOTE
# =============================================================================

def get_quote(
    instrument_key: str,
) -> dict[str, Any]:

    payload = api_get(
        QUOTE_URL,
        {
            "instrument_key": instrument_key,
        },
    )

    data = payload.get(
        "data",
        {},
    )

    if not isinstance(data, dict):
        raise ScannerError(
            "Quote response data is not an object."
        )

    if instrument_key in data:
        return data[instrument_key]

    if len(data) == 1:
        return next(iter(data.values()))

    raise ScannerError(
        f"Quote not found for {instrument_key}."
    )


def extract_ltp(
    quote: dict[str, Any],
) -> float:

    for field in (
        "last_price",
        "ltp",
        "lastPrice",
    ):
        value = quote.get(field)

        if value is not None:
            price = float(value)

            if price > 0:
                return price

    raise ScannerError(
        "LTP not present in quote."
    )


# =============================================================================
# INSTRUMENT DISCOVERY
# =============================================================================
def get_current_sensex_future() -> FuturesContract:

    all_contracts = []

    # Try current month first, then next month.
    for expiry_filter in ("current_month", "next_month"):

        payload = api_get(
            INSTRUMENT_SEARCH_URL,
            {
                "query": "SENSEX",
                "exchanges": "BSE",
                "segments": "FO",
                "instrument_types": "FUT",
                "expiry": expiry_filter,
                "page_number": 1,
                "records": 30,
            },
        )

        contracts = payload.get("data", [])

        if isinstance(contracts, list):
            all_contracts.extend(contracts)

    if not all_contracts:
        raise ScannerError(
            "No active SENSEX futures returned by Upstox."
        )

    valid = []

    for contract in all_contracts:

        if not (
            contract.get("instrument_key")
            and contract.get("trading_symbol")
            and contract.get("expiry")
        ):
            continue

        underlying = str(
            contract.get(
                "underlying_symbol",
                ""
            )
        ).upper()

        symbol = str(
            contract.get(
                "trading_symbol",
                ""
            )
        ).upper()

        if (
            "SENSEX" in underlying
            or "SENSEX" in symbol
        ):
            valid.append(contract)

    if not valid:
        logger.error(
            "Upstox futures response: %s",
            json.dumps(
                all_contracts,
                default=str,
            ),
        )

        raise ScannerError(
            "No valid SENSEX future found."
        )

    # Sort by expiry and select nearest available future.
    valid.sort(
        key=lambda x: str(
            x.get("expiry")
        )
    )

    selected = valid[0]

    logger.info(
        "Selected SENSEX future: %s | Expiry: %s | Key: %s",
        selected["trading_symbol"],
        selected["expiry"],
        selected["instrument_key"],
    )

    return FuturesContract(
        instrument_key=selected["instrument_key"],
        trading_symbol=selected["trading_symbol"],
        expiry=str(selected["expiry"]),
    )

def get_current_week_contracts() -> list[dict[str, Any]]:
    """
    Load SENSEX option contracts for the exact weekly Thursday expiry.
    """
    exact_expiry = get_active_sensex_expiry()

    logger.info(
        "Using exact dynamically selected SENSEX weekly expiry for option contracts: %s",
        exact_expiry,
    )

    payload = api_get(
        OPTION_CONTRACT_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": exact_expiry,
        },
    )

    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError(
            "No SENSEX option contracts returned for selected expiry "
            f"{exact_expiry}."
        )

    return contracts


# =============================================================================
# CANDLE DATA
# =============================================================================

def get_intraday_candles(
    instrument_key: str,
    interval_minutes: int,
    max_candles: Optional[int] = None,
    min_candles: int = 2,
) -> pd.DataFrame:

    encoded_key = urllib.parse.quote(
        instrument_key,
        safe="",
    )

    # Use Upstox V3 intraday candles for the current trading session.
    # This is the correct V3 endpoint for current-day data and supports
    # custom minute intervals such as 3 and 15 minutes.
    url = (
        f"{HISTORICAL_CANDLE_URL}/intraday/"
        f"{encoded_key}/minutes/{interval_minutes}"
    )

    payload = api_get(url)

    data = payload.get(
        "data",
        {},
    )

    candles = data.get(
        "candles",
        [],
    )

    if not isinstance(candles, list) or not candles:
        raise ScannerError(
            f"No {interval_minutes}-minute candles returned for {instrument_key}."
        )

    records = []

    for row in candles:
        if not isinstance(row, (list, tuple)) or len(row) < 6:
            continue

        try:
            records.append(
                {
                    "timestamp": row[0],
                    "open": float(row[1]),
                    "high": float(row[2]),
                    "low": float(row[3]),
                    "close": float(row[4]),
                    "volume": float(row[5]),
                    "oi": (
                        float(row[6])
                        if len(row) > 6 and row[6] is not None
                        else np.nan
                    ),
                }
            )
        except (TypeError, ValueError):
            continue

    df = pd.DataFrame(records)

    if df.empty:
        raise ScannerError(
            f"No valid {interval_minutes}-minute candles after parsing."
        )

    df["timestamp"] = pd.to_datetime(
        df["timestamp"],
        utc=True,
        errors="coerce",
    )

    df = (
        df
        .dropna(subset=["timestamp"])
        .sort_values("timestamp")
        .drop_duplicates(subset=["timestamp"])
        .reset_index(drop=True)
    )

    # Keep only current-session records. The V3 intraday endpoint is current-day
    # data, but this explicit filter protects the VWAP calculation.
    session_date = now_ist().date()
    session_dates = df["timestamp"].dt.tz_convert(IST).dt.date
    df = df.loc[session_dates == session_date].reset_index(drop=True)

    if len(df) < min_candles:
        raise ScannerError(
            f"Insufficient current-session {interval_minutes}-minute candles: "
            f"got {len(df)}, need at least {min_candles}."
        )

    if max_candles is not None and len(df) > max_candles:
        df = df.tail(max_candles).reset_index(drop=True)

    logger.info(
        "Loaded %d current-session %d-minute candles for %s",
        len(df),
        interval_minutes,
        instrument_key,
    )

    return df


def get_session_candles_for_vwap(
    instrument_key: str,
    interval_minutes: int = 3,
    min_candles: int = 20,
) -> pd.DataFrame:
    """Fetch and return the complete current-session candle set for VWAP.

    This function intentionally does not accept max_candles. It prevents the
    short Futures regime window (2-3 candles) from ever being reused as the
    VWAP source.
    """
    df = get_intraday_candles(
        instrument_key,
        interval_minutes,
        max_candles=None,
        min_candles=min_candles,
    )

    usable_volume = pd.to_numeric(
        df["volume"], errors="coerce"
    ).fillna(0.0).clip(lower=0.0)

    if len(df) < min_candles or float(usable_volume.sum()) <= 0.0:
        raise ScannerError(
            f"Insufficient usable Futures session data for VWAP: "
            f"candles={len(df)}, volume={float(usable_volume.sum()):.0f}."
        )

    logger.info(
        "VWAP source: SENSEX Futures | current-session candles=%d | volume=%0.f",
        len(df),
        float(usable_volume.sum()),
    )
    return df


# =============================================================================
# INDICATORS
# =============================================================================

def calculate_atr(
    df: pd.DataFrame,
    period: int,
) -> pd.Series:

    previous_close = df["close"].shift(1)

    true_range = pd.concat(
        [
            df["high"] - df["low"],
            (
                df["high"]
                - previous_close
            ).abs(),
            (
                df["low"]
                - previous_close
            ).abs(),
        ],
        axis=1,
    ).max(axis=1)

    return true_range.ewm(
        alpha=1 / period,
        adjust=False,
        min_periods=1,
    ).mean()


def calculate_supertrend(
    df: pd.DataFrame,
    period: int = SUPERTREND_PERIOD,
    factor: float = SUPERTREND_FACTOR,
) -> pd.DataFrame:

    result = df.copy()

    result["atr"] = calculate_atr(
        result,
        period,
    )

    hl2 = (
        result["high"]
        + result["low"]
    ) / 2.0

    basic_upper = (
        hl2
        + factor * result["atr"]
    )

    basic_lower = (
        hl2
        - factor * result["atr"]
    )

    final_upper = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    final_lower = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    direction = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    supertrend = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    if result.empty:
        raise ScannerError(
            "Unable to calculate Supertrend: no candles available."
        )

    first_valid = result["atr"].first_valid_index()

    if first_valid is None:
        raise ScannerError(
            f"Unable to calculate Supertrend: ATR contains no valid values "
            f"(candles={len(result)}, period={period})."
        )

    start = result.index.get_loc(
        first_valid
    )

    final_upper.iloc[start] = (
        basic_upper.iloc[start]
    )

    final_lower.iloc[start] = (
        basic_lower.iloc[start]
    )

    direction.iloc[start] = 1

    supertrend.iloc[start] = (
        final_lower.iloc[start]
    )

    for i in range(
        start + 1,
        len(result),
    ):

        prev = i - 1

        if (
            basic_upper.iloc[i]
            < final_upper.iloc[prev]
            or result["close"].iloc[prev]
            > final_upper.iloc[prev]
        ):
            final_upper.iloc[i] = (
                basic_upper.iloc[i]
            )
        else:
            final_upper.iloc[i] = (
                final_upper.iloc[prev]
            )

        if (
            basic_lower.iloc[i]
            > final_lower.iloc[prev]
            or result["close"].iloc[prev]
            < final_lower.iloc[prev]
        ):
            final_lower.iloc[i] = (
                basic_lower.iloc[i]
            )
        else:
            final_lower.iloc[i] = (
                final_lower.iloc[prev]
            )

        if (
            result["close"].iloc[i]
            > final_upper.iloc[prev]
        ):
            direction.iloc[i] = 1

        elif (
            result["close"].iloc[i]
            < final_lower.iloc[prev]
        ):
            direction.iloc[i] = -1

        else:
            direction.iloc[i] = (
                direction.iloc[prev]
            )

        supertrend.iloc[i] = (
            final_lower.iloc[i]
            if direction.iloc[i] == 1
            else final_upper.iloc[i]
        )

    result["supertrend"] = supertrend
    result["direction"] = direction

    return result


def calculate_vwap(
    df: pd.DataFrame,
) -> pd.Series:
    """Calculate session VWAP and fail explicitly when usable volume is absent."""
    if df.empty:
        return pd.Series(np.nan, index=df.index, dtype=float)

    typical = (
        df["high"]
        + df["low"]
        + df["close"]
    ) / 3.0

    volume = pd.to_numeric(df["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    session = pd.to_datetime(
        df["timestamp"], utc=True, errors="coerce"
    ).dt.tz_convert(IST).dt.date

    cumulative_volume = volume.groupby(session).cumsum()
    cumulative_pv = (typical * volume).groupby(session).cumsum()

    vwap = cumulative_pv / cumulative_volume.replace(0, np.nan)

    # Index candles can legitimately have zero volume. In that case this is
    # not a real VWAP. The scanner uses SENSEX futures candles for VWAP instead.
    return vwap


# =============================================================================
# MARKET STRUCTURE
# =============================================================================

def structure_state(
    df: pd.DataFrame,
    lookback: int,
) -> str:

    if len(df) < lookback:
        return "NEUTRAL"

    recent = df.tail(
        lookback
    )

    highs = recent[
        "high"
    ].to_numpy()

    lows = recent[
        "low"
    ].to_numpy()

    bullish = (
        highs[-1] > highs[0]
        and lows[-1] > lows[0]
    )

    bearish = (
        highs[-1] < highs[0]
        and lows[-1] < lows[0]
    )

    if bullish:
        return "BULLISH"

    if bearish:
        return "BEARISH"

    return "NEUTRAL"

def market_regime(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    chain_bias: str,
    chain_bias_score: float,
    change_oi_bias_value: str,
    change_oi_score: float,
) -> tuple[str, list[str]]:

    """
    Classify the current market as TRENDING or SIDEWAYS.

    The goal is to prevent a single Futures regime + VWAP position
    from manufacturing a directional prediction while price action
    is actually compressed inside a range.
    """

    reasons: list[str] = []

    if (
        len(spot_3m) < SIDEWAYS_LOOKBACK_3M
        or len(spot_15m) < SIDEWAYS_LOOKBACK_15M
    ):
        return (
            "UNKNOWN",
            ["Insufficient candles for sideways/range classification."]
        )

    recent_3m = spot_3m.tail(
        SIDEWAYS_LOOKBACK_3M
    ).copy()

    recent_15m = spot_15m.tail(
        SIDEWAYS_LOOKBACK_15M
    ).copy()

    latest_3m = recent_3m.iloc[-1]
    latest_15m = recent_15m.iloc[-1]

    atr_3m = float(latest_3m.get("atr", np.nan))
    atr_15m = float(latest_15m.get("atr", np.nan))

    if (
        not math.isfinite(atr_3m)
        or not math.isfinite(atr_15m)
        or atr_3m <= 0
        or atr_15m <= 0
    ):
        return (
            "UNKNOWN",
            ["ATR unavailable for sideways/range classification."]
        )

    # -------------------------------------------------------------
    # 3-minute range measurements
    # -------------------------------------------------------------

    range_3m = float(
        recent_3m["high"].max()
        - recent_3m["low"].min()
    )

    net_move_3m = abs(
        float(recent_3m["close"].iloc[-1])
        - float(recent_3m["close"].iloc[0])
    )

    range_atr_3m = range_3m / atr_3m
    net_move_atr_3m = net_move_3m / atr_3m

    # -------------------------------------------------------------
    # 15-minute range measurements
    # -------------------------------------------------------------

    range_15m = float(
        recent_15m["high"].max()
        - recent_15m["low"].min()
    )

    net_move_15m = abs(
        float(recent_15m["close"].iloc[-1])
        - float(recent_15m["close"].iloc[0])
    )

    range_atr_15m = range_15m / atr_15m
    net_move_atr_15m = net_move_15m / atr_15m

    # -------------------------------------------------------------
    # Supertrend flip count
    # -------------------------------------------------------------

    direction_3m = (
        pd.to_numeric(
            recent_3m["direction"],
            errors="coerce"
        )
        .dropna()
        .astype(int)
    )

    direction_15m = (
        pd.to_numeric(
            recent_15m["direction"],
            errors="coerce"
        )
        .dropna()
        .astype(int)
    )

    flips_3m = int(
        direction_3m.ne(
            direction_3m.shift()
        ).sum() - 1
    ) if len(direction_3m) > 1 else 0

    flips_15m = int(
        direction_15m.ne(
            direction_15m.shift()
        ).sum() - 1
    ) if len(direction_15m) > 1 else 0

    # -------------------------------------------------------------
    # Price structure
    # -------------------------------------------------------------

    structure_3m = structure_state(
        recent_3m,
        min(
            STRUCTURE_LOOKBACK_3M,
            len(recent_3m)
        ),
    )

    structure_15m = structure_state(
        recent_15m,
        min(
            STRUCTURE_LOOKBACK_15M,
            len(recent_15m)
        ),
    )

    # -------------------------------------------------------------
    # Sideways conditions
    # -------------------------------------------------------------

    compressed_3m = (
        range_atr_3m <= SIDEWAYS_MAX_RANGE_ATR_3M
    )

    compressed_15m = (
        range_atr_15m <= SIDEWAYS_MAX_RANGE_ATR_15M
    )

    low_net_move_3m = (
        net_move_atr_3m <= SIDEWAYS_MAX_NET_MOVE_ATR_3M
    )

    low_net_move_15m = (
        net_move_atr_15m <= SIDEWAYS_MAX_NET_MOVE_ATR_15M
    )

    unstable_3m = (
        flips_3m >= SIDEWAYS_MAX_SUPERTREND_FLIPS
    )

    unstable_15m = (
        flips_15m >= SIDEWAYS_MAX_SUPERTREND_FLIPS
    )

    oi_balanced = (
        abs(float(chain_bias_score))
        <= SIDEWAYS_CHAIN_OI_SCORE
        and abs(float(change_oi_score))
        <= SIDEWAYS_CHANGE_OI_SCORE
    )

    neutral_structure = (
        structure_3m == "NEUTRAL"
        or structure_15m == "NEUTRAL"
        or structure_3m != structure_15m
    )

    sideways_score = 0

    if compressed_3m:
        sideways_score += 1

    if low_net_move_3m:
        sideways_score += 1

    if compressed_15m:
        sideways_score += 1

    if low_net_move_15m:
        sideways_score += 1

    if unstable_3m:
        sideways_score += 1

    if unstable_15m:
        sideways_score += 1

    if oi_balanced:
        sideways_score += 2

    if neutral_structure:
        sideways_score += 1

    logger.info(
        "Market regime check: "
        "3m_range_ATR=%.2f "
        "3m_net_ATR=%.2f "
        "15m_range_ATR=%.2f "
        "15m_net_ATR=%.2f "
        "3m_flips=%d "
        "15m_flips=%d "
        "structure_3m=%s "
        "structure_15m=%s "
        "chain_OI=%.3f "
        "change_OI=%.3f "
        "sideways_score=%d",
        range_atr_3m,
        net_move_atr_3m,
        range_atr_15m,
        net_move_atr_15m,
        flips_3m,
        flips_15m,
        structure_3m,
        structure_15m,
        float(chain_bias_score),
        float(change_oi_score),
        sideways_score,
    )

    # -----------------------------------------------------------------
    # STRONG SIDEWAYS / RANGE DETECTION
    # -----------------------------------------------------------------

    # The market can be sideways even if the 3-minute candles show
    # temporary directional movement. Give greater importance to the
    # 15-minute net movement because it represents the broader intraday
    # structure.
    strong_15m_compression = (
        compressed_15m
        and low_net_move_15m
    )

    timeframe_conflict = (
        structure_3m in {"BULLISH", "BEARISH"}
        and structure_15m in {"BULLISH", "BEARISH"}
        and structure_3m != structure_15m
    )

    # Strong sideways condition:
    # 1. 15-minute market remains compressed.
    # 2. Net movement is small.
    # 3. 3m and 15m structures disagree.
    if strong_15m_compression and timeframe_conflict:
        sideways_score = max(sideways_score, 5)
        reasons.append(
            "Strong sideways condition: compressed 15-minute range "
            "with minimal net movement and conflicting 3m/15m structure."
        )

    # -----------------------------------------------------------------
    # NORMAL SIDEWAYS CLASSIFICATION
    # -----------------------------------------------------------------
    if sideways_score >= 5:
        reasons.extend([
            "Market classified as SIDEWAYS/RANGE.",
            (
                f"3m range={range_atr_3m:.2f} ATR, "
                f"net move={net_move_atr_3m:.2f} ATR."
            ),
            (
                f"15m range={range_atr_15m:.2f} ATR, "
                f"net move={net_move_atr_15m:.2f} ATR."
            ),
            (
                f"3m structure={structure_3m}, "
                f"15m structure={structure_15m}."
            ),
            (
                f"Supertrend flips: "
                f"3m={flips_3m}, 15m={flips_15m}."
            ),
            (
                f"OI positioning: localized={chain_bias}, "
                f"Change-OI={change_oi_bias_value}."
            ),
        ])
        return "SIDEWAYS", reasons

    reasons.extend([
        "Market classified as TRENDING/EXPANDING.",
        (
            f"3m range={range_atr_3m:.2f} ATR, "
            f"net move={net_move_atr_3m:.2f} ATR."
        ),
        (
            f"15m range={range_atr_15m:.2f} ATR, "
            f"net move={net_move_atr_15m:.2f} ATR."
        ),
        (
            f"3m structure={structure_3m}, "
            f"15m structure={structure_15m}."
        ),
    ])

    return "TRENDING", reasons

def recent_swing_high(
    df: pd.DataFrame,
    lookback: int,
) -> float:

    if len(df) < lookback:
        raise ScannerError(
            "Insufficient data for swing high."
        )

    return float(
        df["high"]
        .iloc[
            -lookback:
            -1
        ]
        .max()
    )


def recent_swing_low(
    df: pd.DataFrame,
    lookback: int,
) -> float:

    if len(df) < lookback:
        raise ScannerError(
            "Insufficient data for swing low."
        )

    return float(
        df["low"]
        .iloc[
            -lookback:
            -1
        ]
        .min()
    )


# =============================================================================
# OPTION CHAIN ANALYSIS
# =============================================================================

def get_active_sensex_expiry() -> str:
    """
    Dynamically select the nearest non-expired SENSEX option expiry.

    The option-contract endpoint is queried without a relative expiry filter,
    then all valid expiry dates returned by Upstox are parsed and the nearest
    active date is selected.
    """
    payload = api_get(
        OPTION_CONTRACT_URL,
        {"instrument_key": SENSEX_KEY},
    )

    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError(
            "No SENSEX option contracts returned for dynamic expiry discovery."
        )

    today = now_ist().date()
    weekly_expiries = set()

    for contract in contracts:
        if not isinstance(contract, dict):
            continue

        raw_expiry = str(contract.get("expiry", "")).strip()

        try:
            expiry_date = datetime.strptime(
                raw_expiry[:10],
                "%Y-%m-%d",
            ).date()
        except (TypeError, ValueError):
            continue

        if expiry_date < today:
            continue

        if bool(contract.get("weekly")):
            weekly_expiries.add(expiry_date)

    if not weekly_expiries:
        raise ScannerError(
            "No valid non-expired SENSEX weekly option expiry was found."
        )

    expiries = weekly_expiries

    selected_expiry = min(expiries).isoformat()

    logger.info(
        "Dynamically selected active SENSEX expiry: %s",
        selected_expiry,
    )

    return selected_expiry


def get_chain() -> list[dict[str, Any]]:
    """
    Load the SENSEX option chain using a dynamically discovered
    active expiry.
    """

    exact_expiry = get_active_sensex_expiry()

    logger.info(
        "Using dynamically selected SENSEX expiry for option chain: %s",
        exact_expiry,
    )

    # Verify the selected expiry through the option contracts endpoint
    # before requesting the option chain.
    contracts_payload = api_get(
        OPTION_CONTRACT_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": exact_expiry,
        },
    )

    contracts = contracts_payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:

        raise ScannerError(
            "Selected SENSEX expiry was discovered but no active option "
            f"contracts were returned for expiry {exact_expiry}."
        )

    returned_expiries = sorted(
        {
            str(contract.get("expiry", "")).strip()[:10]
            for contract in contracts
            if isinstance(contract, dict)
            and contract.get("expiry")
        }
    )

    logger.info(
        "Verified SENSEX option contracts: expiry=%s | contracts=%d",
        exact_expiry,
        len(contracts),
    )

    if exact_expiry not in returned_expiries:

        raise ScannerError(
            f"Expiry validation failed. Requested={exact_expiry}, "
            f"returned={returned_expiries}"
        )

    payload = api_get(
        OPTION_CHAIN_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": exact_expiry,
        },
        retries=4,
    )

    data = payload.get("data", [])

    if not isinstance(data, list) or not data:

        raise ScannerError(
            "SENSEX option chain is empty for expiry "
            f"{exact_expiry}."
        )

    logger.info(
        "Loaded SENSEX option chain: expiry=%s | rows=%d",
        exact_expiry,
        len(data),
    )

    return data


def chain_spot(
    chain: list[dict[str, Any]],
) -> float:

    values = []

    for row in chain:

        value = row.get(
            "underlying_spot_price"
        )

        if value is not None:
            try:
                values.append(
                    float(value)
                )
            except (
                TypeError,
                ValueError,
            ):
                continue

    if not values:
        raise ScannerError(
            "Underlying spot unavailable in option chain."
        )

    return float(
        np.median(values)
    )


def chain_rows(
    chain: list[dict[str, Any]],
) -> dict[float, dict[str, Any]]:

    result = {}

    for row in chain:

        strike = row.get(
            "strike_price"
        )

        if strike is None:
            continue

        try:
            result[
                float(strike)
            ] = row
        except (
            TypeError,
            ValueError,
        ):
            continue

    if not result:
        raise ScannerError(
            "No valid option strikes in chain."
        )

    return result


def nearest_atm_strike(
    spot: float,
    strikes: list[float],
) -> float:

    return min(
        strikes,
        key=lambda x: abs(
            x - spot
        ),
    )


def strike_interval(
    strikes: list[float],
) -> float:

    unique = sorted(
        set(strikes)
    )

    differences = [
        unique[i + 1] - unique[i]
        for i in range(
            len(unique) - 1
        )
        if unique[i + 1] > unique[i]
    ]

    if not differences:
        raise ScannerError(
            "Unable to determine option strike interval."
        )

    return min(
        differences
    )


def option_market_data(
    row: dict[str, Any],
    option_type: str,
) -> dict[str, Any]:

    key = (
        "call_options"
        if option_type == "CE"
        else "put_options"
    )

    data = row.get(
        key,
        {},
    )

    market = data.get(
        "market_data",
        {},
    )

    greeks = data.get(
        "option_greeks",
        {},
    )

    return {
        "instrument_key": data.get(
            "instrument_key"
        ),
        "ltp": market.get(
            "ltp"
        ),
        "oi": market.get(
            "oi"
        ),
        "prev_oi": market.get(
            "prev_oi"
        ),
        "delta": greeks.get(
            "delta"
        ),
        "gamma": greeks.get(
            "gamma"
        ),
        "iv": greeks.get(
            "iv"
        ),
    }


def oi_structure(
    chain: list[dict[str, Any]],
    spot: float,
) -> tuple[str, float, dict[float, dict[str, float]]]:
    """
    Build a localized option-positioning bias around ATM.

    Bullish pressure:
      - PE OI increasing
      - CE OI decreasing (unwinding)

    Bearish pressure:
      - CE OI increasing
      - PE OI decreasing (unwinding)

    The calculation is proximity-weighted so strikes nearest ATM have
    more influence than distant strikes. This is intentionally different
    from a simple aggregate CE-minus-PE total.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows.keys())

    atm = nearest_atm_strike(spot, strikes)
    step = strike_interval(strikes)

    relevant = [
        strike
        for strike in strikes
        if abs(strike - atm) <= step * 3
    ]

    strike_data: dict[float, dict[str, float]] = {}

    bullish_pressure = 0.0
    bearish_pressure = 0.0

    for strike in relevant:
        row = rows[strike]

        call = option_market_data(row, "CE")
        put = option_market_data(row, "PE")

        call_oi = float(call["oi"] or 0)
        call_prev = float(call["prev_oi"] or 0)
        put_oi = float(put["oi"] or 0)
        put_prev = float(put["prev_oi"] or 0)

        call_change = call_oi - call_prev
        put_change = put_oi - put_prev

        # Near-ATM strikes matter more than distant strikes.
        distance_steps = abs(strike - atm) / step if step > 0 else 0.0
        weight = 1.0 / (1.0 + distance_steps)

        # Bullish = put buildup + call unwinding.
        bullish_pressure += weight * (
            max(put_change, 0.0) + max(-call_change, 0.0)
        )

        # Bearish = call buildup + put unwinding.
        bearish_pressure += weight * (
            max(call_change, 0.0) + max(-put_change, 0.0)
        )

        strike_data[strike] = {
            "call_oi": call_oi,
            "put_oi": put_oi,
            "call_change": call_change,
            "put_change": put_change,
            "weight": weight,
        }

    denominator = bullish_pressure + bearish_pressure

    if denominator <= 0:
        score = 0.0
    else:
        score = (bullish_pressure - bearish_pressure) / denominator

    # Keep the threshold modest because this is a localized pressure
    # measurement, while Futures and VWAP provide the primary directional filter.
    if score >= 0.08:
        bias = "BULLISH"
    elif score <= -0.08:
        bias = "BEARISH"
    else:
        bias = "NEUTRAL"

    logger.info(
        "Localized OI: ATM=%.0f bullish_pressure=%.0f bearish_pressure=%.0f score=%.3f bias=%s",
        atm,
        bullish_pressure,
        bearish_pressure,
        score,
        bias,
    )

    return bias, float(score), strike_data


# =============================================================================
# OI CHANGE FROM LIVE OPTION CHAIN
# =============================================================================

def get_change_oi_from_chain(
    chain: list[dict[str, Any]],
) -> dict[str, Any]:
    """
    Calculate current-session Change-in-OI directly from the live option-chain
    market_data. Upstox exposes both `oi` and `prev_oi` on each option, so this
    avoids relying on a separate aggregate endpoint during every scan.
    """
    total_call_change = 0.0
    total_put_change = 0.0
    strike_changes: list[dict[str, float]] = []
    valid_rows = 0

    for row in chain:
        if not isinstance(row, dict):
            continue

        try:
            strike_value = float(row.get("strike_price"))
        except (TypeError, ValueError):
            continue

        call = option_market_data(row, "CE")
        put = option_market_data(row, "PE")

        try:
            call_oi = float(call.get("oi") or 0.0)
            call_prev_oi = float(call.get("prev_oi") or 0.0)
            put_oi = float(put.get("oi") or 0.0)
            put_prev_oi = float(put.get("prev_oi") or 0.0)
        except (TypeError, ValueError):
            continue

        call_change = call_oi - call_prev_oi
        put_change = put_oi - put_prev_oi
        total_call_change += call_change
        total_put_change += put_change
        strike_changes.append({
            "strike_price": strike_value,
            "call_change_oi": call_change,
            "put_change_oi": put_change,
        })
        valid_rows += 1

    if valid_rows == 0:
        raise ScannerError(
            "No valid current/previous OI values were found in the option chain."
        )

    logger.info(
        "Chain Change-OI: rows=%d total_call_change=%+.0f total_put_change=%+.0f",
        valid_rows,
        total_call_change,
        total_put_change,
    )

    return {
        "total_call_change_oi": total_call_change,
        "total_put_change_oi": total_put_change,
        "call_put_oi_data_list": strike_changes,
    }



def change_oi_bias(
    data: dict[str, Any],
) -> tuple[str, float]:

    if not data:
        return (
            "UNAVAILABLE",
            0.0,
        )

    call_change = float(
        data.get(
            "total_call_change_oi",
            0,
        )
    )

    put_change = float(
        data.get(
            "total_put_change_oi",
            0,
        )
    )

    denominator = (
        abs(call_change)
        + abs(put_change)
    )

    if denominator == 0:
        return (
            "NEUTRAL",
            0.0,
        )

    score = (
        put_change
        - call_change
    ) / denominator

    if score >= 0.15:
        return (
            "BULLISH",
            float(score),
        )

    if score <= -0.15:
        return (
            "BEARISH",
            float(score),
        )

    return (
        "NEUTRAL",
        float(score),
    )


# =============================================================================
# FUTURES ANALYSIS
# =============================================================================

def futures_regime(
    future: FuturesContract,
    candles: Optional[pd.DataFrame] = None,
) -> str:
    """Classify Futures positioning with a small noise filter.

    The latest move and the aggregate move across the supplied recent candles
    must agree. A mixed/tiny move is NEUTRAL instead of being forced into a
    regime, which reduces one-candle OI whipsaws.
    """
    if candles is None:
        candles = get_intraday_candles(
            future.instrument_key,
            3,
            max_candles=3,
            min_candles=3,
        )

    if len(candles) < 3:
        return "UNAVAILABLE"

    recent = candles.tail(3).copy()
    closes = pd.to_numeric(recent["close"], errors="coerce")
    ois = pd.to_numeric(recent["oi"], errors="coerce")
    if closes.isna().any() or ois.isna().any():
        return "UNAVAILABLE"

    latest_price_delta = float(closes.iloc[-1] - closes.iloc[-2])
    latest_oi_delta = float(ois.iloc[-1] - ois.iloc[-2])
    aggregate_price_delta = float(closes.iloc[-1] - closes.iloc[0])
    aggregate_oi_delta = float(ois.iloc[-1] - ois.iloc[0])

    if (
        abs(latest_price_delta) < FUTURES_REGIME_MIN_PRICE_MOVE
        or abs(aggregate_price_delta) < FUTURES_REGIME_MIN_PRICE_MOVE
        or abs(latest_oi_delta) < FUTURES_REGIME_MIN_OI_CHANGE
        or abs(aggregate_oi_delta) < FUTURES_REGIME_MIN_OI_CHANGE
    ):
        return "NEUTRAL"

    price_sign = (
        latest_price_delta > 0 and aggregate_price_delta > 0
    ) or (
        latest_price_delta < 0 and aggregate_price_delta < 0
    )
    oi_sign = (
        latest_oi_delta > 0 and aggregate_oi_delta > 0
    ) or (
        latest_oi_delta < 0 and aggregate_oi_delta < 0
    )

    if not (price_sign and oi_sign):
        logger.info(
            "Futures regime noise/mixed: latest_price=%.2f aggregate_price=%.2f latest_oi=%.0f aggregate_oi=%.0f",
            latest_price_delta,
            aggregate_price_delta,
            latest_oi_delta,
            aggregate_oi_delta,
        )
        return "NEUTRAL"

    if latest_price_delta > 0 and latest_oi_delta > 0:
        return "LONG_BUILDUP"
    if latest_price_delta < 0 and latest_oi_delta > 0:
        return "SHORT_BUILDUP"
    if latest_price_delta > 0 and latest_oi_delta < 0:
        return "SHORT_COVERING"
    if latest_price_delta < 0 and latest_oi_delta < 0:
        return "LONG_UNWINDING"

    return "NEUTRAL"


# =============================================================================
# OPTION CONTRACT SELECTION
# =============================================================================

def option_buying_momentum(
    option: OptionCandidate,
) -> tuple[bool, dict[str, Any]]:
    """Hard buying-side filter for the selected option premium.

    The scanner only recommends option buying. A correct SENSEX direction is
    therefore insufficient if the selected option premium is already falling.
    The option must show positive recent price momentum and a positive short
    EMA trend. Long buildup or short covering in the option is acceptable.
    """
    try:
        candles = get_intraday_candles(
            option.instrument_key,
            3,
            max_candles=BUY_OPTION_LOOKBACK,
            min_candles=BUY_OPTION_MIN_CANDLES,
        )
    except ScannerError as exc:
        return False, {
            "reason": f"option candles unavailable: {exc}",
            "regime": "UNAVAILABLE",
        }

    closes = pd.to_numeric(candles["close"], errors="coerce")
    if closes.isna().any():
        closes = closes.dropna()

    if len(closes) < BUY_OPTION_MIN_CANDLES:
        return False, {
            "reason": f"only {len(closes)} usable option candles",
            "regime": "UNAVAILABLE",
        }

    latest = float(closes.iloc[-1])
    previous = float(closes.iloc[-2])
    lookback_close = float(closes.iloc[-BUY_OPTION_MIN_CANDLES])

    ema5_series = closes.ewm(span=5, adjust=False).mean()
    ema5 = float(ema5_series.iloc[-1])
    ema5_prev = float(ema5_series.iloc[-2])

    oi_latest = candles["oi"].iloc[-1]
    oi_previous = candles["oi"].iloc[-2]
    price_delta = latest - previous
    oi_delta = (
        float(oi_latest) - float(oi_previous)
        if pd.notna(oi_latest) and pd.notna(oi_previous)
        else 0.0
    )

    if price_delta > 0 and oi_delta > 0:
        regime = "LONG_BUILDUP"
    elif price_delta > 0 and oi_delta < 0:
        regime = "SHORT_COVERING"
    elif price_delta < 0 and oi_delta > 0:
        regime = "SHORT_BUILDUP"
    elif price_delta < 0 and oi_delta < 0:
        regime = "LONG_UNWINDING"
    else:
        regime = "NEUTRAL"

    multi_return_pct = (
        (latest - lookback_close) / lookback_close * 100.0
        if lookback_close > 0
        else 0.0
    )
    ltp_vs_last_pct = (
        (option.ltp - latest) / latest * 100.0
        if latest > 0
        else -100.0
    )

    premium_rising = price_delta > 0 and option.ltp >= latest
    trend_positive = latest > lookback_close
    ema_positive = latest >= ema5 and ema5 >= ema5_prev
    regime_positive = regime in {"LONG_BUILDUP", "SHORT_COVERING"}

    valid = (
        premium_rising
        and trend_positive
        and ema_positive
        and regime_positive
        and multi_return_pct >= BUY_OPTION_MIN_RETURN_PCT
        and ltp_vs_last_pct >= -0.50
    )

    reason = (
        "buying-side option premium momentum confirmed"
        if valid
        else "option premium momentum/price action is not suitable for buying"
    )

    metrics = {
        "reason": reason,
        "regime": regime,
        "latest_close": latest,
        "previous_close": previous,
        "ema5": ema5,
        "ema5_prev": ema5_prev,
        "multi_return_pct": multi_return_pct,
        "ltp_vs_last_pct": ltp_vs_last_pct,
    }

    logger.info(
        "Buy-side option check: %s regime=%s LTP=%.2f last3m=%.2f 5-bar=%.2f%% EMA5=%.2f EMA5_prev=%.2f valid=%s",
        option.trading_symbol,
        regime,
        option.ltp,
        latest,
        multi_return_pct,
        ema5,
        ema5_prev,
        valid,
    )

    return valid, metrics


def select_directional_option(
    contracts: list[dict[str, Any]],
    chain: list[dict[str, Any]],
    direction: str,
    spot: float,
    preferred_strike: Optional[float] = None,
) -> OptionCandidate:

    rows = chain_rows(chain)
    chain_strikes = sorted(rows.keys())

    atm = nearest_atm_strike(spot, chain_strikes)
    step = strike_interval(chain_strikes)

    # BUY-ONLY ITM selection.
    # Bullish -> ATM-1 CE, then ATM-2 CE.
    # Bearish -> ATM+1 PE, then ATM+2 PE.
    if direction == "BULLISH":
        candidates = [atm - step, atm - 2 * step]
        option_type = "CE"
    else:
        candidates = [atm + step, atm + 2 * step]
        option_type = "PE"

    # A locked strike must remain the exact strike; if its premium is no longer
    # suitable for buying, do not silently switch to another strike.
    if preferred_strike is not None:
        candidates = [float(preferred_strike)]

    last_rejection = "No valid buy-side option candidate."

    for target_strike in candidates:
        if target_strike not in rows:
            last_rejection = f"Strike {target_strike:.0f} not present in option chain."
            continue

        matches = [
            contract
            for contract in contracts
            if (
                str(contract.get("instrument_type", "")).upper() == option_type
                and float(contract.get("strike_price", -1)) == float(target_strike)
            )
        ]

        if not matches:
            last_rejection = f"No {option_type} contract found at {target_strike:.0f}."
            continue

        contract = matches[0]
        market = option_market_data(rows[target_strike], option_type)
        ltp = float(market["ltp"] or 0)
        delta = market["delta"]

        if ltp <= 0 or delta is None:
            last_rejection = f"Invalid LTP/delta at {target_strike:.0f}."
            continue

        candidate = OptionCandidate(
            instrument_key=contract["instrument_key"],
            trading_symbol=contract["trading_symbol"],
            option_type=option_type,
            strike=float(target_strike),
            expiry=str(contract["expiry"]),
            ltp=ltp,
            oi=float(market["oi"] or 0),
            prev_oi=float(market["prev_oi"] or 0),
            delta=float(delta),
            gamma=float(market["gamma"] or 0),
            iv=float(market["iv"] or 0),
        )

        valid_buy, buy_metrics = option_buying_momentum(candidate)
        if not valid_buy:
            last_rejection = (
                f"{candidate.trading_symbol} rejected for BUY-ONLY momentum: {buy_metrics.get('reason', 'unsuitable premium action')}"
            )
            logger.info(last_rejection)
            continue

        logger.info(
            "ITM BUY option selected: direction=%s ATM=%.0f strike=%.0f type=%s LTP=%.2f Delta=%.3f",
            direction,
            atm,
            target_strike,
            option_type,
            ltp,
            float(delta),
        )

        return candidate

    raise ScannerError(last_rejection)


# =============================================================================
# OPTION EXTENSION FILTER
# =============================================================================

def option_is_extended(
    option: OptionCandidate,
) -> bool:
    # Disabled deliberately: the scanner must not reject an otherwise
    # valid predictive setup because the option has already started moving.
    return False


def option_price_oi_regime(option: OptionCandidate) -> str:
    """Return the selected option's latest 3-minute price/OI regime.

    This is a confirmation field only. It never becomes the primary
    prediction trigger because the goal is to identify the move before
    the option premium is already extended.
    """
    try:
        candles = get_intraday_candles(option.instrument_key, 3, max_candles=3, min_candles=2)

        if len(candles) < 3:
            return "UNAVAILABLE"

        latest = candles.iloc[-1]
        previous = candles.iloc[-2]

        if pd.isna(latest["oi"]) or pd.isna(previous["oi"]):
            return "UNAVAILABLE"

        price_delta = float(latest["close"] - previous["close"])
        oi_delta = float(latest["oi"] - previous["oi"])

        if price_delta > 0 and oi_delta > 0:
            return "LONG_BUILDUP"

        if price_delta > 0 and oi_delta < 0:
            return "SHORT_COVERING"

        if price_delta < 0 and oi_delta > 0:
            return "SHORT_BUILDUP"

        if price_delta < 0 and oi_delta < 0:
            return "LONG_UNWINDING"

        return "NEUTRAL"

    except ScannerError as exc:
        logger.info(
            "Option price/OI confirmation unavailable for %s: %s",
            option.trading_symbol,
            exc,
        )
        return "UNAVAILABLE"


def final_entry_direction_confirmation(
    direction: str,
    futures_state: str,
    chain_bias: str,
    change_oi_bias_value: str,
    live_spot: float,
    futures_vwap_candles: pd.DataFrame,
    spot_3m: Optional[pd.DataFrame] = None,
) -> tuple[bool, list[str]]:
    """Hard BUY-side entry gate.

    Before any CE/PE strike is selected, Futures + OI + VWAP must agree.
    Futures premium/discount is an additional matrix confirmation; it does not
    replace the three-factor hard gate.
    """
    valid_vwap = calculate_vwap(futures_vwap_candles).dropna()
    if len(valid_vwap) < 2:
        return False, ["Session VWAP unavailable for final entry confirmation."]

    session_vwap = float(valid_vwap.iloc[-1])
    previous_vwap = float(valid_vwap.iloc[-2])
    vwap_slope = session_vwap - previous_vwap
    above_vwap = float(live_spot) > session_vwap

    if futures_state == "LONG_BUILDUP":
        futures_direction = "BULLISH"
    elif futures_state == "SHORT_BUILDUP":
        futures_direction = "BEARISH"
    elif futures_state == "SHORT_COVERING":
        futures_direction = "BULLISH" if above_vwap else "BEARISH"
    elif futures_state == "LONG_UNWINDING":
        futures_direction = "BEARISH" if not above_vwap else "BULLISH"
    else:
        futures_direction = "NEUTRAL"

    # OI sources must not contradict each other at entry time. A bullish
    # localized OI signal plus bearish Change-OI (or vice versa) is treated as
    # conflict/NEUTRAL rather than allowing the first matching condition to win.
    oi_values = {str(chain_bias).upper(), str(change_oi_bias_value).upper()}
    if "BULLISH" in oi_values and "BEARISH" in oi_values:
        oi_direction = "NEUTRAL"
    elif "BULLISH" in oi_values:
        oi_direction = "BULLISH"
    elif "BEARISH" in oi_values:
        oi_direction = "BEARISH"
    else:
        oi_direction = "NEUTRAL"
    vwap_direction = "BULLISH" if above_vwap else "BEARISH"

    futures_ok = futures_direction == direction
    oi_ok = oi_direction == direction
    vwap_ok = vwap_direction == direction

    basis_state = "UNAVAILABLE"
    # Strong regimes require basis confirmation when data exists. Missing basis
    # data does not manufacture a signal; weak regimes are rejected without it.
    basis_ok = futures_state in {"LONG_BUILDUP", "SHORT_BUILDUP"}
    if spot_3m is not None:
        basis_state, _, _ = futures_premium_discount_state(
            futures_vwap_candles,
            spot_3m,
            live_spot,
        )
        if basis_state != "UNAVAILABLE":
            if futures_state == "LONG_BUILDUP":
                basis_ok = basis_state == "WIDENING_PREMIUM"
            elif futures_state == "SHORT_BUILDUP":
                basis_ok = basis_state == "DEEPENING_DISCOUNT"
            elif futures_state == "SHORT_COVERING":
                basis_ok = direction == "BULLISH" and basis_state in {"SHRINKING_PREMIUM", "NARROWING_DISCOUNT"}
            elif futures_state == "LONG_UNWINDING":
                basis_ok = direction == "BEARISH" and basis_state in {"SHRINKING_PREMIUM", "NARROWING_DISCOUNT", "FLAT_PREMIUM", "FLAT_DISCOUNT"}

    logger.info(
        "FINAL ENTRY CONFIRMATION: direction=%s futures=%s OI=%s VWAP=%s basis=%s | FUT_OK=%s OI_OK=%s VWAP_OK=%s BASIS_OK=%s | VWAP=%.2f slope=%.4f",
        direction,
        futures_direction,
        oi_direction,
        vwap_direction,
        basis_state,
        futures_ok,
        oi_ok,
        vwap_ok,
        basis_ok,
        session_vwap,
        vwap_slope,
    )

    reasons = [
        f"Futures={futures_state} interpreted as {futures_direction}: {'OK' if futures_ok else 'FAIL'}",
        f"OI=localized:{chain_bias}/changeOI:{change_oi_bias_value} interpreted as {oi_direction}: {'OK' if oi_ok else 'FAIL'}",
        f"SENSEX={live_spot:.2f} vs VWAP={session_vwap:.2f} interpreted as {vwap_direction}: {'OK' if vwap_ok else 'FAIL'}",
        f"Futures premium/discount state={basis_state}: {'OK' if basis_ok else 'FAIL'}",
    ]

    # The chart-aligned three-factor confirmation remains the mandatory gate.
    # Premium/discount must be supportive when the data is available for a
    # non-neutral Futures regime.
    return futures_ok and oi_ok and vwap_ok and basis_ok, reasons


def futures_premium_discount_state(
    futures_candles: pd.DataFrame,
    spot_3m: pd.DataFrame,
    live_spot: float,
    epsilon_points: float = FUTURES_BASIS_EPSILON_POINTS,
) -> tuple[str, float, float]:
    """Classify Futures premium/discount behavior for the sentiment matrix.

    Matrix mapping:
      LONG_BUILDUP   -> widening premium is supportive.
      SHORT_BUILDUP  -> deepening discount is supportive.
      SHORT_COVERING -> shrinking premium / narrowing discount is supportive.
      LONG_UNWINDING -> shrinking premium / narrowing discount is supportive.
    """
    if futures_candles is None or spot_3m is None or futures_candles.empty or spot_3m.empty:
        return "UNAVAILABLE", float("nan"), float("nan")
    if len(futures_candles) < 2 or len(spot_3m) < 2:
        return "UNAVAILABLE", float("nan"), float("nan")

    try:
        fut_latest = float(futures_candles["close"].iloc[-1])
        fut_previous = float(futures_candles["close"].iloc[-2])
        spot_previous = float(spot_3m["close"].iloc[-2])
        current_basis = fut_latest - float(live_spot)
        previous_basis = fut_previous - spot_previous
        basis_change = current_basis - previous_basis
    except (TypeError, ValueError, KeyError, IndexError):
        return "UNAVAILABLE", float("nan"), float("nan")

    if not all(math.isfinite(v) for v in (current_basis, previous_basis, basis_change)):
        return "UNAVAILABLE", float("nan"), float("nan")

    if current_basis >= 0:
        if basis_change > epsilon_points:
            state = "WIDENING_PREMIUM"
        elif basis_change < -epsilon_points:
            state = "SHRINKING_PREMIUM"
        else:
            state = "FLAT_PREMIUM"
    else:
        if basis_change < -epsilon_points:
            state = "DEEPENING_DISCOUNT"
        elif basis_change > epsilon_points:
            state = "NARROWING_DISCOUNT"
        else:
            state = "FLAT_DISCOUNT"

    logger.info(
        "Futures premium/discount: current_basis=%.2f previous_basis=%.2f change=%.2f state=%s",
        current_basis,
        previous_basis,
        basis_change,
        state,
    )
    return state, current_basis, basis_change


# =============================================================================
# PRE-BREAKOUT ENGINE
# =============================================================================

def predictive_direction(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    chain_bias: str,
    chain_bias_score: float,
    change_oi_bias_value: str,
    change_oi_score: float,
    futures_state: str,
    live_spot: float,
    futures_3m: Optional[pd.DataFrame] = None,
    previous_snapshot: Optional[dict[str, Any]] = None,
) -> tuple[str, str, float, list[str]]:
    """Predict the next directional move before the breakout.

    Sentiment matrix implemented here:
      LONG_BUILDUP       -> STRONG BULLISH
      SHORT_BUILDUP      -> STRONG BEARISH
      SHORT_COVERING     -> WEAK BULLISH (context dependent)
      LONG_UNWINDING     -> WEAK BEARISH (context dependent)

    Inputs are weighted by importance:
      Futures regime        = strongest
      VWAP position         = primary price confirmation
      Futures basis behavior= confirmation from premium/discount
      Localized option OI   = confirmation
      Change-OI             = confirmation
      15m Supertrend        = context only

    A fresh Futures regime transition receives extra weight. Supertrend is not
    required for the predictive trigger.
    """
    # -------------------------------------------------------------------------
    # 0. MARKET REGIME FILTER
    #
    # A predictive signal must not be created merely because Futures and VWAP
    # temporarily point in one direction while the underlying remains trapped
    # inside a balanced intraday range.
    # -------------------------------------------------------------------------

    current_market_regime, regime_reasons = market_regime(
        spot_3m=spot_3m,
        spot_15m=spot_15m,
        chain_bias=chain_bias,
        chain_bias_score=chain_bias_score,
        change_oi_bias_value=change_oi_bias_value,
        change_oi_score=change_oi_score,
    )

    if current_market_regime == "SIDEWAYS":

        logger.info(
            "Prediction suppressed: SIDEWAYS/RANGE market. "
            "Futures=%s | localized_OI=%s | Change_OI=%s",
            futures_state,
            chain_bias,
            change_oi_bias_value,
        )

        return (
            "NEUTRAL",
            "SIDEWAYS",
            0.0,
            regime_reasons,
        )        
    latest_15 = spot_15m.iloc[-1]

    bullish_score = 0.0
    bearish_score = 0.0
    bullish_reasons: list[str] = []
    bearish_reasons: list[str] = []

    strong_bullish_futures = futures_state == "LONG_BUILDUP"
    strong_bearish_futures = futures_state == "SHORT_BUILDUP"
    weak_bullish_futures = futures_state == "SHORT_COVERING"
    weak_bearish_futures = futures_state == "LONG_UNWINDING"
    bullish_futures = strong_bullish_futures or weak_bullish_futures
    bearish_futures = strong_bearish_futures or weak_bearish_futures

    previous_futures_state = str(
        (previous_snapshot or {}).get("futures_state") or ""
    )
    previous_direction = str(
        (previous_snapshot or {}).get("prediction_direction") or ""
    )

    futures_transition = (
        previous_futures_state
        and previous_futures_state != futures_state
        and previous_futures_state != "UNAVAILABLE"
        and futures_state != "UNAVAILABLE"
    )

    # -------------------------------------------------------------------------
    # 1. FUTURES REGIME — strongest input, with chart-aligned strength.
    # -------------------------------------------------------------------------
    if strong_bullish_futures:
        bullish_score += 45
        bullish_reasons.append("Futures = LONG_BUILDUP (strong bullish sentiment)")
    elif weak_bullish_futures:
        bullish_score += 20
        bullish_reasons.append("Futures = SHORT_COVERING (weak bullish sentiment)")
    elif strong_bearish_futures:
        bearish_score += 45
        bearish_reasons.append("Futures = SHORT_BUILDUP (strong bearish sentiment)")
    elif weak_bearish_futures:
        bearish_score += 20
        bearish_reasons.append("Futures = LONG_UNWINDING (weak bearish sentiment)")

    if futures_transition:
        transition_bonus = 10 if futures_state in {"LONG_BUILDUP", "SHORT_BUILDUP"} else 5
        logger.info(
            "Futures regime transition: %s -> %s | bonus=%d",
            previous_futures_state,
            futures_state,
            transition_bonus,
        )
        if bullish_futures:
            bullish_score += transition_bonus
            bullish_reasons.append(
                f"Fresh Futures transition: {previous_futures_state} -> {futures_state}"
            )
        elif bearish_futures:
            bearish_score += transition_bonus
            bearish_reasons.append(
                f"Fresh Futures transition: {previous_futures_state} -> {futures_state}"
            )

    # -------------------------------------------------------------------------
    # 2. OPTION OI — confirmation, with explicit opposing penalties.
    # -------------------------------------------------------------------------
    if chain_bias == "BULLISH":
        bullish_score += 15
        bullish_reasons.append("Localized option OI pressure is bullish")
        if bearish_futures:
            bearish_score -= 8
            bearish_reasons.append("Localized OI conflicts with current bearish Futures regime (-8)")
    elif chain_bias == "BEARISH":
        bearish_score += 15
        bearish_reasons.append("Localized option OI pressure is bearish")
        if bullish_futures:
            bullish_score -= 8
            bullish_reasons.append("Localized OI conflicts with current bullish Futures regime (-8)")

    if change_oi_bias_value == "BULLISH":
        bullish_score += 10
        bullish_reasons.append("Upstox Change-OI confirms bullish direction")
        if bearish_futures:
            bearish_score -= 5
            bearish_reasons.append("Change-OI conflicts with current bearish Futures regime (-5)")
    elif change_oi_bias_value == "BEARISH":
        bearish_score += 10
        bearish_reasons.append("Upstox Change-OI confirms bearish direction")
        if bullish_futures:
            bullish_score -= 5
            bullish_reasons.append("Change-OI conflicts with current bullish Futures regime (-5)")

    # -------------------------------------------------------------------------
    # 3. VWAP — price position is primary; slope is only context.
    # -------------------------------------------------------------------------
    if futures_3m is None or futures_3m.empty:
        raise ScannerError("SENSEX futures candle data unavailable for VWAP.")

    vwap_series = calculate_vwap(futures_3m)
    valid_vwap = vwap_series.dropna()
    if len(valid_vwap) < 2:
        raise ScannerError("Session VWAP unavailable: SENSEX futures volume is zero/missing.")

    session_vwap = float(valid_vwap.iloc[-1])
    previous_vwap = float(valid_vwap.iloc[-2])
    vwap_slope = session_vwap - previous_vwap
    above_vwap = float(live_spot) > session_vwap

    logger.info(
        "VWAP check: SENSEX=%.2f VWAP=%.2f slope=%.4f position=%s",
        live_spot,
        session_vwap,
        vwap_slope,
        "ABOVE" if above_vwap else "BELOW",
    )

    if above_vwap:
        bullish_score += 25
        bullish_reasons.append(f"SENSEX {live_spot:.2f} is above session VWAP {session_vwap:.2f}")
        if vwap_slope > VWAP_FLAT_SLOPE_EPSILON:
            bullish_score += 5
            bullish_reasons.append("VWAP slope is meaningfully rising (+5)")
        elif vwap_slope < -VWAP_FLAT_SLOPE_EPSILON:
            bullish_score -= 3
            bullish_reasons.append("VWAP slope is meaningfully falling against bullish position (-3)")
        else:
            bullish_reasons.append("VWAP slope is flat: no slope points awarded")
    else:
        bearish_score += 25
        bearish_reasons.append(f"SENSEX {live_spot:.2f} is below session VWAP {session_vwap:.2f}")
        if vwap_slope < -VWAP_FLAT_SLOPE_EPSILON:
            bearish_score += 5
            bearish_reasons.append("VWAP slope is meaningfully falling (+5)")
        elif vwap_slope > VWAP_FLAT_SLOPE_EPSILON:
            bearish_score -= 3
            bearish_reasons.append("VWAP slope is meaningfully rising against bearish position (-3)")
        else:
            bearish_reasons.append("VWAP slope is flat: no slope points awarded")

    # -------------------------------------------------------------------------
    # 4. FUTURES PREMIUM / DISCOUNT — explicit chart-aligned confirmation.
    # -------------------------------------------------------------------------
    basis_state, basis_points, basis_change = futures_premium_discount_state(
        futures_3m,
        spot_3m,
        live_spot,
    )

    supportive_basis = False
    if basis_state != "UNAVAILABLE":
        if strong_bullish_futures:
            supportive_basis = basis_state == "WIDENING_PREMIUM"
            if supportive_basis:
                bullish_score += 10
                bullish_reasons.append("Futures premium is widening (+10)")
            else:
                bullish_score -= 5
                bullish_reasons.append(f"LONG_BUILDUP lacks widening premium support ({basis_state}) (-5)")
        elif strong_bearish_futures:
            supportive_basis = basis_state == "DEEPENING_DISCOUNT"
            if supportive_basis:
                bearish_score += 10
                bearish_reasons.append("Futures discount is deepening (+10)")
            else:
                bearish_score -= 5
                bearish_reasons.append(f"SHORT_BUILDUP lacks deepening discount support ({basis_state}) (-5)")
        elif weak_bullish_futures:
            supportive_basis = basis_state in {"SHRINKING_PREMIUM", "NARROWING_DISCOUNT"}
            if supportive_basis:
                bullish_score += 5
                bullish_reasons.append(f"SHORT_COVERING basis behavior supportive: {basis_state} (+5)")
            else:
                bullish_score -= 3
                bullish_reasons.append(f"SHORT_COVERING basis behavior weak/not supportive: {basis_state} (-3)")
        elif weak_bearish_futures:
            supportive_basis = basis_state in {"SHRINKING_PREMIUM", "NARROWING_DISCOUNT", "FLAT_PREMIUM", "FLAT_DISCOUNT"}
            if supportive_basis:
                bearish_score += 5
                bearish_reasons.append(f"LONG_UNWINDING basis behavior supportive: {basis_state} (+5)")
            else:
                bearish_score -= 3
                bearish_reasons.append(f"LONG_UNWINDING basis behavior weak/not supportive: {basis_state} (-3)")

    # -------------------------------------------------------------------------
    # 5. 15M SUPERTREND — confirmation/context only.
    # -------------------------------------------------------------------------
    if latest_15["direction"] == 1:
        bullish_score += 5
        bullish_reasons.append("15-minute Supertrend supports bullish continuation (+5)")
    elif latest_15["direction"] == -1:
        bearish_score += 5
        bearish_reasons.append("15-minute Supertrend supports bearish continuation (+5)")

    # -------------------------------------------------------------------------
    # Direction decision. Strong/weak Futures hierarchy is retained.
    # -------------------------------------------------------------------------
    minimum_score = SIGNAL_THRESHOLD
    score_gap = abs(bullish_score - bearish_score)

    if bullish_futures and bullish_score >= minimum_score and bullish_score > bearish_score:
        if previous_direction != "BULLISH" and previous_direction in {"BEARISH", "NEUTRAL", ""}:
            bullish_reasons.append(
                f"Directional state is newly bullish versus previous run: {previous_direction or 'NONE'} -> BULLISH"
            )
        return (
            "BULLISH",
            "BULLISH_PREDICTIVE",
            min(100.0, bullish_score),
            bullish_reasons,
        )

    if bearish_futures and bearish_score >= minimum_score and bearish_score > bullish_score:
        if previous_direction != "BEARISH" and previous_direction in {"BULLISH", "NEUTRAL", ""}:
            bearish_reasons.append(
                f"Directional state is newly bearish versus previous run: {previous_direction or 'NONE'} -> BEARISH"
            )
        return (
            "BEARISH",
            "BEARISH_PREDICTIVE",
            min(100.0, bearish_score),
            bearish_reasons,
        )

    logger.info(
        "Prediction scores: bullish=%.1f bearish=%.1f gap=%.1f | previous_futures=%s previous_direction=%s | basis_state=%s basis=%.2f change=%.2f",
        bullish_score,
        bearish_score,
        score_gap,
        previous_futures_state or "NONE",
        previous_direction or "NONE",
        basis_state,
        basis_points if math.isfinite(basis_points) else float("nan"),
        basis_change if math.isfinite(basis_change) else float("nan"),
    )

    return (
        "NEUTRAL",
        "NEUTRAL",
        0.0,
        ["Current Futures/VWAP/OI/premium-discount evidence did not cross the predictive threshold."],
    )


# =============================================================================
# PRE-BREAKOUT VALIDATION
# =============================================================================

def validate_prebreakout(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    direction: str,
    option: OptionCandidate,
) -> tuple[bool, float, float, list[str]]:

    latest_3 = spot_3m.iloc[-1]
    latest_15 = spot_15m.iloc[-1]
    spot = float(latest_3["close"])

    atr_3 = float(latest_3["atr"])
    atr_15 = float(latest_15["atr"])
    if not (math.isfinite(atr_3) and math.isfinite(atr_15) and atr_3 > 0 and atr_15 > 0):
        return False, 0.0, 0.0, ["ATR unavailable."]

    if direction == "BULLISH":
        recent_trigger = recent_swing_high(spot_3m, STRUCTURE_LOOKBACK_3M)
        trigger_3m = max(
            recent_trigger,
            spot + max(atr_3 * 0.25, 1.0),
        )

        recent_15 = recent_swing_high(spot_15m, STRUCTURE_LOOKBACK_15M)
        target_15m = max(
            recent_15,
            float(latest_15["supertrend"]),
            trigger_3m + max(atr_15 * 0.50, atr_3 * 0.50),
        )
    else:
        recent_trigger = recent_swing_low(spot_3m, STRUCTURE_LOOKBACK_3M)
        trigger_3m = min(
            recent_trigger,
            spot - max(atr_3 * 0.25, 1.0),
        )

        recent_15 = recent_swing_low(spot_15m, STRUCTURE_LOOKBACK_15M)
        target_15m = min(
            recent_15,
            float(latest_15["supertrend"]),
            trigger_3m - max(atr_15 * 0.50, atr_3 * 0.50),
        )

    if not (OPTION_MIN_DELTA <= abs(option.delta) <= OPTION_MAX_DELTA):
        return (
            False,
            trigger_3m,
            target_15m,
            [f"Rejected: selected option Delta={option.delta:.3f} is outside the trading range."],
        )

    return (
        True,
        trigger_3m,
        target_15m,
        [
            "Prediction is based on Futures + OI difference + VWAP.",
            "3-minute Supertrend is used for target/confirmation, not as the entry trigger.",
            f"ITM option selected at {option.strike:.0f} ({option.option_type}).",
            f"Option Delta={option.delta:.3f}.",
        ],
    )

# =============================================================================
# PREMIUM TARGET ENGINE
# =============================================================================

def premium_target_from_underlying_move(
    entry: float,
    current_underlying: float,
    target_underlying: float,
    delta: float,
    gamma: float,
    direction: str,
) -> float:

    if direction == "BULLISH":
        move = (
            target_underlying
            - current_underlying
        )
    else:
        move = (
            current_underlying
            - target_underlying
        )

    if move <= 0:
        raise ScannerError(
            "Underlying target is not beyond current price."
        )

    absolute_delta = abs(delta)

    first_order = (
        absolute_delta
        * move
    )

    second_order = (
        0.5
        * abs(gamma)
        * move
        * move
    )

    premium_change = (
        first_order
        + second_order
    )

    # Prevent a pathological Greek-derived projection
    # from creating a mathematically extreme alert.
    premium_change = min(
        premium_change,
        entry * 2.0,
    )

    return round(
        entry + premium_change,
        2,
    )


def create_targets(
    option: OptionCandidate,
    spot: float,
    trigger_3m: float,
    target_15m: float,
    direction: str,
) -> tuple[float, float, float]:

    entry = option.ltp

    target_1 = premium_target_from_underlying_move(
        entry=entry,
        current_underlying=spot,
        target_underlying=trigger_3m,
        delta=option.delta,
        gamma=option.gamma,
        direction=direction,
    )

    target_2 = premium_target_from_underlying_move(
        entry=entry,
        current_underlying=spot,
        target_underlying=target_15m,
        delta=option.delta,
        gamma=option.gamma,
        direction=direction,
    )

    if target_2 <= target_1:
        raise ScannerError(
            "Target 2 must exceed Target 1."
        )

    stop_loss = round(
        entry * 0.85,
        2,
    )

    return (
        target_1,
        target_2,
        stop_loss,
    )


# =============================================================================
# STATE
# =============================================================================

def load_state() -> dict[str, Any]:

    if not STATE_FILE.exists():
        return {}

    try:

        with STATE_FILE.open(
            "r",
            encoding="utf-8",
        ) as file:

            data = json.load(
                file
            )

        return (
            data
            if isinstance(data, dict)
            else {}
        )

    except Exception as exc:

        logger.warning(
            "State read failed: %s",
            exc,
        )

        return {}


def save_state(
    state: dict[str, Any],
) -> None:

    STATE_FILE.parent.mkdir(
        parents=True,
        exist_ok=True,
    )

    temp_file = STATE_FILE.with_suffix(
        ".tmp"
    )

    with temp_file.open(
        "w",
        encoding="utf-8",
    ) as file:

        json.dump(
            state,
            file,
            indent=2,
            ensure_ascii=False,
        )

    temp_file.replace(
        STATE_FILE
    )


def signal_hash(
    signal: Signal,
) -> str:

    key = "|".join(
        [
            signal.direction,
            signal.instrument_key,
            str(
                signal.strike
            ),
            signal.regime,
        ]
    )

    return hashlib.sha256(
        key.encode(
            "utf-8"
        )
    ).hexdigest()


# =============================================================================
# EMAIL
# =============================================================================

def send_email(
    subject: str,
    body: str,
) -> None:

    required = {
        "EMAIL_SENDER": EMAIL_SENDER,
        "EMAIL_PASSWORD": EMAIL_PASSWORD,
        "EMAIL_RECEIVER": EMAIL_RECEIVER,
    }

    missing = [
        name
        for name, value in required.items()
        if not value
    ]

    if missing:
        raise ScannerError(
            "Missing email configuration: "
            + ", ".join(missing)
        )

    message = MIMEMultipart(
        "alternative"
    )

    message["From"] = EMAIL_SENDER
    message["To"] = EMAIL_RECEIVER
    message["Subject"] = subject

    message.attach(
        MIMEText(
            body,
            "html",
            "utf-8",
        )
    )

    with smtplib.SMTP_SSL(
        SMTP_HOST,
        SMTP_PORT,
        timeout=30,
    ) as server:

        server.login(
            EMAIL_SENDER,
            EMAIL_PASSWORD,
        )

        server.sendmail(
            EMAIL_SENDER,
            [EMAIL_RECEIVER],
            message.as_string(),
        )


def email_body(
    signal: Signal,
) -> str:

    reason_html = "".join(
        f"<li>{reason}</li>"
        for reason in signal.reasons
    )

    return f"""
<html>
<body>

<h2>
SENSEX Predictive {signal.direction} Signal
</h2>

<table border="1"
       cellpadding="7"
       cellspacing="0">

<tr>
<td><b>Time</b></td>
<td>{signal.timestamp}</td>
</tr>

<tr>
<td><b>Regime</b></td>
<td>{signal.regime}</td>
</tr>

<tr>
<td><b>Confidence</b></td>
<td>{signal.confidence:.1f}%</td>
</tr>

<tr>
<td><b>SENSEX Spot</b></td>
<td>{signal.spot:.2f}</td>
</tr>

<tr>
<td><b>Futures Regime</b></td>
<td>{signal.futures_state}</td>
</tr>

<tr>
<td><b>Option</b></td>
<td>{signal.trading_symbol}</td>
</tr>

<tr>
<td><b>Option Type</b></td>
<td>{signal.option_type}</td>
</tr>

<tr>
<td><b>Strike</b></td>
<td>{signal.strike:.0f}</td>
</tr>

<tr>
<td><b>Entry</b></td>
<td>₹{signal.entry:.2f}</td>
</tr>

<tr>
<td><b>Target 1</b></td>
<td>₹{signal.target_1:.2f}</td>
</tr>

<tr>
<td><b>Target 2</b></td>
<td>₹{signal.target_2:.2f}</td>
</tr>

<tr>
<td><b>Stop Loss</b></td>
<td>₹{signal.stop_loss:.2f}</td>
</tr>

<tr>
<td><b>3m Breakout Trigger</b></td>
<td>{signal.underlying_trigger_3m:.2f}</td>
</tr>

<tr>
<td><b>15m Target Level</b></td>
<td>{signal.underlying_target_15m:.2f}</td>
</tr>

<tr>
<td><b>Delta</b></td>
<td>{signal.delta:.4f}</td>
</tr>

<tr>
<td><b>Gamma</b></td>
<td>{signal.gamma:.6f}</td>
</tr>

</table>

<h3>Prediction Factors</h3>

<ul>
{reason_html}
</ul>

<p>
This is a rule-based market signal. It does not guarantee
future price movement or profitability.
</p>

</body>
</html>
"""


# =============================================================================
# MAIN SCANNER
# =============================================================================

def execute_scan(state: Optional[dict[str, Any]] = None) -> Optional[Signal]:
    if not market_window_open():
        logger.info("Outside BSE market hours.")
        return None

    status = get_market_status()
    logger.info("BSE status: %s", status)

    if status != "OPEN":
        logger.info("BSE is not OPEN. No signal generated.")
        return None

    state = state if isinstance(state, dict) else {}
    previous_snapshot = state.get("market_snapshot")
    if not isinstance(previous_snapshot, dict):
        previous_snapshot = {}

    future = get_current_sensex_future()

    # -------------------------------------------------------------------------
    # Underlying market data
    # -------------------------------------------------------------------------
    # Separate datasets by purpose. The latest 3 candles are used only for
    # Futures price/OI regime. A complete current-session Futures dataset is
    # fetched separately for the session VWAP and is never truncated.
    futures_recent = get_intraday_candles(
        future.instrument_key,
        3,
        max_candles=3,
        min_candles=3,
    )
    futures_state = futures_regime(future, candles=futures_recent)

    futures_vwap_candles = get_session_candles_for_vwap(
        future.instrument_key,
        interval_minutes=3,
        min_candles=20,
    )

    logger.info(
        "Futures regime: %s | regime candles=%d | VWAP candles=%d",
        futures_state,
        len(futures_recent),
        len(futures_vwap_candles),
    )

    spot_3m = get_intraday_candles(
        SENSEX_KEY,
        3,
        min_candles=3,
    )

    spot_3m = calculate_supertrend(
        spot_3m,
        SUPERTREND_PERIOD,
        SUPERTREND_FACTOR,
    )

    spot_15m = get_intraday_candles(
        SENSEX_KEY,
        15,
        min_candles=2,
    )

    spot_15m = calculate_supertrend(
        spot_15m,
        SUPERTREND_PERIOD,
        SUPERTREND_FACTOR,
    )

    spot_quote = get_quote(SENSEX_KEY)
    spot = extract_ltp(spot_quote)

    # -------------------------------------------------------------------------
    # Option chain / OI
    # -------------------------------------------------------------------------
    chain = get_chain()
    chain_spot_value = chain_spot(chain)

    if abs(chain_spot_value - spot) > 100:
        raise ScannerError(
            "Option-chain spot differs materially from current quote."
        )

    contracts = get_current_week_contracts()

    chain_bias, chain_bias_score, strike_data = oi_structure(
        chain,
        spot,
    )

    change_data = get_change_oi_from_chain(chain)
    change_bias, change_bias_score = change_oi_bias(change_data)

    direction, regime, confidence, reasons = predictive_direction(
    spot_3m,
    spot_15m,
    chain_bias,
    chain_bias_score,
    change_bias,
    change_bias_score,
    futures_state,
    live_spot=spot,
    futures_3m=futures_vwap_candles,
    previous_snapshot=previous_snapshot,
      )


    # Persist every market snapshot, including neutral runs. This allows the
    # next scheduled run to detect and use regime transitions.
    basis_state_snapshot, basis_points_snapshot, basis_change_snapshot = futures_premium_discount_state(
        futures_vwap_candles,
        spot_3m,
        spot,
    )
    current_snapshot = {
        "timestamp": now_ist().isoformat(),
        "sensex_spot": round(float(spot), 2),
        "futures_state": futures_state,
        "futures_basis_state": basis_state_snapshot,
        "futures_basis_points": round(float(basis_points_snapshot), 4) if math.isfinite(basis_points_snapshot) else None,
        "futures_basis_change": round(float(basis_change_snapshot), 4) if math.isfinite(basis_change_snapshot) else None,
        "chain_bias": chain_bias,
        "chain_bias_score": round(float(chain_bias_score), 6),
        "change_oi_bias": change_bias,
        "change_oi_score": round(float(change_bias_score), 6),
        "vwap": round(float(calculate_vwap(futures_vwap_candles).dropna().iloc[-1]), 4),
        "prediction_direction": direction,
        "prediction_regime": regime,
        "prediction_confidence": round(float(confidence), 2),
    }
    state["market_snapshot"] = current_snapshot
    state["previous_market_snapshot"] = previous_snapshot
    save_state(state)

    if previous_snapshot:
        logger.info(
            "Previous market state: time=%s futures=%s OI=%s changeOI=%s prediction=%s",
            previous_snapshot.get("timestamp", ""),
            previous_snapshot.get("futures_state", ""),
            previous_snapshot.get("chain_bias", ""),
            previous_snapshot.get("change_oi_bias", ""),
            previous_snapshot.get("prediction_direction", ""),
        )

    logger.info(
        "Prediction: direction=%s regime=%s confidence=%.2f",
        direction,
        regime,
        confidence,
    )

    if direction == "NEUTRAL":
        return None

    if confidence < SIGNAL_THRESHOLD:
        logger.info(
            "Rejected: confidence %.2f < %.2f",
            confidence,
            SIGNAL_THRESHOLD,
        )
        return None

    # -------------------------------------------------------------------------
    # Futures must never contradict the predictive direction.
    # -------------------------------------------------------------------------
    bullish_future = futures_state in (
        "LONG_BUILDUP",
        "SHORT_COVERING",
    )
    bearish_future = futures_state in (
        "SHORT_BUILDUP",
        "LONG_UNWINDING",
    )

    if direction == "BULLISH" and bearish_future:
        logger.info(
            "Rejected: futures explicitly bearish (%s).",
            futures_state,
        )
        return None

    if direction == "BEARISH" and bullish_future:
        logger.info(
            "Rejected: futures explicitly bullish (%s).",
            futures_state,
        )
        return None

    final_confirmed, confirmation_reasons = final_entry_direction_confirmation(
        direction,
        futures_state,
        chain_bias,
        change_bias,
        spot,
        futures_vwap_candles,
        spot_3m=spot_3m,
    )

    if not final_confirmed:
        logger.info("No strike selected: final Futures + OI + VWAP confirmation failed.")
        return None

    # -------------------------------------------------------------------------
    # Strike lock
    #
    # Once a predictive setup first produces an ITM strike, keep that strike
    # for LOCK_SETUP_MINUTES. This prevents chasing a later ATM shift.
    # -------------------------------------------------------------------------
    locked_direction = state.get("locked_direction")
    locked_strike = state.get("locked_strike")
    locked_timestamp = state.get("locked_timestamp")

    preferred_strike: Optional[float] = None

    if (
        locked_direction == direction
        and locked_strike is not None
        and locked_timestamp
    ):
        try:
            locked_at = datetime.fromisoformat(locked_timestamp)
            locked_age = (
                now_ist() - locked_at
            ).total_seconds() / 60.0

            if 0 <= locked_age <= LOCK_SETUP_MINUTES:
                preferred_strike = float(locked_strike)
                logger.info(
                    "Using locked predictive strike: %s %.0f (age %.1f min).",
                    direction,
                    preferred_strike,
                    locked_age,
                )
            else:
                logger.info(
                    "Previous %s strike lock expired (age %.1f min).",
                    locked_direction,
                    locked_age,
                )
        except (TypeError, ValueError):
            preferred_strike = None

    option = select_directional_option(
        contracts,
        chain,
        direction,
        spot,
        preferred_strike=preferred_strike,
    )

    logger.info(
        "Candidate option: %s | strike=%.0f | LTP=%.2f | OI=%.0f | prev_OI=%.0f",
        option.trading_symbol,
        option.strike,
        option.ltp,
        option.oi,
        option.prev_oi,
    )

    option_regime = option_price_oi_regime(option)
    logger.info(
        "Selected option price/OI confirmation: %s = %s",
        option.trading_symbol,
        option_regime,
    )

    valid, trigger_3m, target_15m, validation_reasons = validate_prebreakout(
        spot_3m,
        spot_15m,
        direction,
        option,
    )

    if not valid:
        logger.info("Pre-breakout validation rejected.")
        return None

    option_buy_valid, option_buy_metrics = option_buying_momentum(option)
    if not option_buy_valid:
        logger.info(
            "BUY-ONLY strike rejected before lock: %s",
            option_buy_metrics.get("reason", "unsuitable option premium"),
        )
        return None

    # Lock only after all directional and option-premium checks pass.
    if preferred_strike is None:
        state["locked_direction"] = direction
        state["locked_strike"] = option.strike
        state["locked_option_type"] = option.option_type
        state["locked_timestamp"] = now_ist().isoformat()
        save_state(state)

        logger.info(
            "NEW predictive BUY strike locked: %s %.0f %s.",
            direction,
            option.strike,
            option.option_type,
        )

    target_1, target_2, stop_loss = create_targets(
        option,
        spot,
        trigger_3m,
        target_15m,
        direction,
    )

    all_reasons = (
        reasons
        + validation_reasons
        + [
            f"Localized option OI score={chain_bias_score:.3f}.",
            f"Upstox Change-OI score={change_bias_score:.3f}.",
            f"Selected option price/OI confirmation={option_regime}.",
            f"Final entry confirmation: {'; '.join(confirmation_reasons)}",
            f"Buy-side premium momentum: {option_buy_metrics.get('reason', '')}; regime={option_buy_metrics.get('regime', '')}.",
            "Prediction trigger = Futures + localized OI/Change-OI + VWAP.",
            "BUY-ONLY rule: option must show positive premium momentum before selection/lock.",
            "3-minute Supertrend is confirmation/target framework, not entry trigger.",
            "ITM strike is locked at first predictive detection to avoid chasing ATM.",
        ]
    )

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
        direction=direction,
        regime=regime,
        confidence=confidence,
        spot=spot,
        futures_state=futures_state,
        option_type=option.option_type,
        strike=option.strike,
        trading_symbol=option.trading_symbol,
        instrument_key=option.instrument_key,
        entry=option.ltp,
        target_1=target_1,
        target_2=target_2,
        stop_loss=stop_loss,
        underlying_trigger_3m=trigger_3m,
        underlying_target_15m=target_15m,
        delta=option.delta,
        gamma=option.gamma,
        reasons=all_reasons,
    )


# =============================================================================
# PROGRAM ENTRY
# =============================================================================

def main() -> int:

    try:

        state = load_state()

        signal = execute_scan(state)

        if signal is None:
            logger.info(
                "No actionable predictive setup."
            )
            return 0

        current_hash = signal_hash(
            signal
        )

        previous_hash = state.get(
            "last_signal_hash"
        )

        if current_hash == previous_hash:

            logger.info(
                "Duplicate signal suppressed."
            )

            return 0

        send_email(
            (
                f"SENSEX {signal.direction} "
                f"{signal.trading_symbol}"
            ),
            email_body(
                signal
            ),
        )

        state[
            "last_signal_hash"
        ] = current_hash

        state[
            "locked_direction"
        ] = signal.direction

        state[
            "locked_strike"
        ] = signal.strike

        state[
            "locked_option_type"
        ] = signal.option_type

        state[
            "locked_timestamp"
        ] = now_ist().isoformat()

        state[
            "last_signal"
        ] = asdict(
            signal
        )

        state[
            "last_signal_timestamp"
        ] = signal.timestamp

        save_state(
            state
        )

        logger.info(
            "NEW SIGNAL EMAILED: %s",
            signal.trading_symbol,
        )

        return 0

    except ScannerError as exc:

        logger.error(
            "Scanner error: %s",
            exc,
        )

        return 1

    except Exception:

        logger.error(
            "Unexpected scanner failure:\n%s",
            traceback.format_exc(),
        )

        return 1


if __name__ == "__main__":
    sys.exit(
        main()
    )
