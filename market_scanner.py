"""
NIFTY Predictive Options Market Scanner — Market Structure Engine

What this version fixes:
- Uses the NIFTY INDEX as the primary market-price/VWAP/intraday structure feed.
- Uses NIFTY futures price/OI as a separate derivatives confirmation, not the price proxy.
- Uses completed/currently-available multi-timeframe NIFTY structure:
  3m, 15m, 30m, 60m, 120m, 180m Supertrend.
- Uses NIFTY futures price/OI regime as a confirmation and positioning factor.
- Uses INDEX VWAP level + VWAP slope/position.
- Uses both option-chain OI concentration and Change-in-OI to derive
  dynamic support/resistance and directional pressure.
- Separates market-state detection from trade-entry readiness.
- Detects continuous bullish/bearish states, weakening, sideways, and both reversal directions.
- Uses strict continuation confirmation plus an adaptive reversal gate so genuine turns are not suppressed by lagging cumulative positioning.
- Selects Bullish ATM-1/ATM-2 CE or Bearish ATM+1/ATM+2 PE, but ranks
  candidates by liquidity, delta, theta burden, spread, and structure.
- Builds T1/T2/SL dynamically from underlying ATR, Supertrend,
  option-chain support/resistance, and option Greeks.
- No order placement. The script only creates a signal, persists state,
  and sends email.
- Uses current Upstox endpoints: v2 for option chain/contracts/status/
  instrument search/OI/change-OI/PCR; v3 for Full Market Quotes and candle data because the
  older v2 intraday candle API is deprecated.

Run:
    python final_scanner_oct8_final.py --self-test
    python final_scanner_oct8_final.py

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
    SIGNAL_THRESHOLD (default 60)
    MAX_HISTORY_DAYS (default 45)
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
from dataclasses import asdict, dataclass
from datetime import date, datetime, time, timedelta
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
API_RETRIES = int(os.getenv("API_RETRIES", "2"))
MAX_HISTORY_DAYS = int(os.getenv("MAX_HISTORY_DAYS", "45"))
SIGNAL_THRESHOLD = float(os.getenv("SIGNAL_THRESHOLD", "55"))

# Regime-matrix safety thresholds. These deliberately prevent cumulative
# derivatives from overpowering deteriorating NIFTY price action.
REGIME_CHANGE_OI_DEADZONE = float(os.getenv("REGIME_CHANGE_OI_DEADZONE", "0.03"))
REGIME_CHANGE_OI_FULL_SCALE = float(os.getenv("REGIME_CHANGE_OI_FULL_SCALE", "0.20"))
REGIME_PCR_NEUTRAL_LOW = float(os.getenv("REGIME_PCR_NEUTRAL_LOW", "0.95"))
REGIME_PCR_NEUTRAL_HIGH = float(os.getenv("REGIME_PCR_NEUTRAL_HIGH", "1.05"))
REGIME_PCR_FULL_SCALE = float(os.getenv("REGIME_PCR_FULL_SCALE", "0.25"))
REGIME_CONTINUOUS_MIN_SCORE = float(os.getenv("REGIME_CONTINUOUS_MIN_SCORE", "0.38"))
REGIME_DIRECTIONAL_MIN_SCORE = float(os.getenv("REGIME_DIRECTIONAL_MIN_SCORE", "0.16"))
REGIME_MIN_BULL_BEAR_VOTES = int(os.getenv("REGIME_MIN_BULL_BEAR_VOTES", "3"))
REGIME_MAX_OPPOSING_FUTURES = float(os.getenv("REGIME_MAX_OPPOSING_FUTURES", "0.30"))
REGIME_MAX_OPPOSING_CHAIN = float(os.getenv("REGIME_MAX_OPPOSING_CHAIN", "0.25"))
REGIME_PRICE_MIN_MOVE_ATR = float(os.getenv("REGIME_PRICE_MIN_MOVE_ATR", "0.20"))
REGIME_PRICE_STRONG_MOVE_ATR = float(os.getenv("REGIME_PRICE_STRONG_MOVE_ATR", "0.35"))
REGIME_SIDEWAYS_RANGE_ATR = float(os.getenv("REGIME_SIDEWAYS_RANGE_ATR", "2.40"))
REGIME_SIDEWAYS_NET_ATR = float(os.getenv("REGIME_SIDEWAYS_NET_ATR", "0.45"))
REGIME_SIDEWAYS_VWAP_DISTANCE_ATR = float(os.getenv("REGIME_SIDEWAYS_VWAP_DISTANCE_ATR", "0.90"))
REGIME_SIDEWAYS_ALTERNATION = float(os.getenv("REGIME_SIDEWAYS_ALTERNATION", "0.35"))
REGIME_ENTRY_MAX_VWAP_DISTANCE_ATR = float(os.getenv("REGIME_ENTRY_MAX_VWAP_DISTANCE_ATR", "1.55"))
REGIME_LIVE_OPTION_MIN_ALIGNED_ATR = float(os.getenv("REGIME_LIVE_OPTION_MIN_ALIGNED_ATR", "0.15"))
REGIME_LIVE_OPTION_MAX_ADVERSE_ATR = float(os.getenv("REGIME_LIVE_OPTION_MAX_ADVERSE_ATR", "0.15"))
REGIME_OPTION_MAX_ADVERSE_NET_ATR = float(os.getenv("REGIME_OPTION_MAX_ADVERSE_NET_ATR", "0.35"))
REGIME_REQUIRE_OPTION_DIRECTIONAL_BARS = int(os.getenv("REGIME_REQUIRE_OPTION_DIRECTIONAL_BARS", "2"))
MIN_ENTRY_TIME = time(9, 18)
OPENING_RANGE_MINUTES = 3
OVEREXTENSION_ATR = float(os.getenv("OVEREXTENSION_ATR", "2.25"))
# Entry timing controls: confirmation is necessary but not sufficient. These
# prevent chasing a move that is already materially displaced from VWAP.
ENTRY_FUTURES_MIN_PERSISTENCE = float(os.getenv("ENTRY_FUTURES_MIN_PERSISTENCE", "0.30"))
ENTRY_FUTURES_MIN_STRENGTH = float(os.getenv("ENTRY_FUTURES_MIN_STRENGTH", "0.35"))
ENTRY_PCR_BULL_THRESHOLD = float(os.getenv("ENTRY_PCR_BULL_THRESHOLD", "1.10"))
ENTRY_PCR_BEAR_THRESHOLD = float(os.getenv("ENTRY_PCR_BEAR_THRESHOLD", "0.90"))
ENTRY_CHANGE_OI_MIN_SCORE = float(os.getenv("ENTRY_CHANGE_OI_MIN_SCORE", "0.15"))
ENTRY_MAX_3M_MOVE_ATR = float(os.getenv("ENTRY_MAX_3M_MOVE_ATR", "1.35"))
ENTRY_BREAKOUT_LOOKBACK_BARS = int(os.getenv("ENTRY_BREAKOUT_LOOKBACK_BARS", "6"))
ENTRY_BREAKOUT_BUFFER_ATR = float(os.getenv("ENTRY_BREAKOUT_BUFFER_ATR", "0.10"))

# Adaptive reversal-entry controls. Continuation entries remain strict; reversal
# entries recognize that cumulative PCR and futures-OI positioning can lag a true
# intraday turn. They still require VWAP + Change-OI + non-hostile PCR + a
# non-strongly-opposed futures state, plus independent price-structure evidence.
REVERSAL_CHANGE_OI_MIN_SCORE = float(os.getenv("REVERSAL_CHANGE_OI_MIN_SCORE", "0.10"))
REVERSAL_PCR_NEUTRAL_FLOOR = float(os.getenv("REVERSAL_PCR_NEUTRAL_FLOOR", "0.90"))
REVERSAL_PCR_NEUTRAL_CEILING = float(os.getenv("REVERSAL_PCR_NEUTRAL_CEILING", "1.10"))
REVERSAL_FUTURES_MAX_OPPOSING_STRENGTH = float(os.getenv("REVERSAL_FUTURES_MAX_OPPOSING_STRENGTH", "0.30"))
REVERSAL_CHAIN_MAX_OPPOSING_STRENGTH = float(os.getenv("REVERSAL_CHAIN_MAX_OPPOSING_STRENGTH", "0.25"))
REVERSAL_MIN_INTRADAY_STRENGTH = float(os.getenv("REVERSAL_MIN_INTRADAY_STRENGTH", "0.45"))
REVERSAL_MIN_CORE_SCORE = float(os.getenv("REVERSAL_MIN_CORE_SCORE", "2.50"))
REVERSAL_MIN_RECENT_MOVE_ATR = float(os.getenv("REVERSAL_MIN_RECENT_MOVE_ATR", "0.20"))
EXPIRY_DAY_FORCE_ATM = os.getenv("EXPIRY_DAY_FORCE_ATM", "1").strip().lower() not in {"0", "false", "no"}

# Market-state memory. This prevents a neutral scan from erasing the last
# decisive directional regime.
STATE_HISTORY_LIMIT = int(os.getenv("STATE_HISTORY_LIMIT", "60"))

# Reversal detection is independent from option-entry confirmation. It uses
# completed 3m price history so a bullish/bearish turn can still be recognized
# when the immediately previous scan was NEUTRAL or there was a long scan gap.
REVERSAL_LOOKBACK_BARS = int(os.getenv("REVERSAL_LOOKBACK_BARS", "9"))
REVERSAL_RECENT_BARS = int(os.getenv("REVERSAL_RECENT_BARS", "3"))
REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED = int(os.getenv("REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED", "2"))
REVERSAL_STRIKE_MAX_DISTANCE_STEPS = float(os.getenv("REVERSAL_STRIKE_MAX_DISTANCE_STEPS", "1.25"))
REVERSAL_STRIKE_PREFERRED_DISTANCE_STEPS = float(os.getenv("REVERSAL_STRIKE_PREFERRED_DISTANCE_STEPS", "0.0"))

STATE_FILE = Path(os.getenv("STATE_FILE", "state/market_state.json"))

SCANNER_VERSION = "2026-10-08-STRUCTURE-V22-FINAL"
OPTION_TARGET_ENGINE_VERSION = "V21_DELTA_FIRST_GAMMA_CAPPED_10PCT"

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)

SUPERTREND_PERIOD = 10
SUPERTREND_FACTOR = 2.0
TIMEFRAMES = (3, 15, 30, 60, 120, 180)

ATR_PERIOD = 14
ATR_BUFFER_MULTIPLIER = 0.30

# Structure weights. Short/intermediate timeframes are most responsive;
# higher timeframes are stabilizers, not vetoes.
TF_WEIGHTS = {
    3: 1.40,
    15: 1.35,
    30: 1.15,
    60: 1.00,
    120: 0.85,
    180: 0.75,
}

# Directional score components.
W_VWAP_LEVEL = 2.0
W_VWAP_SLOPE = 1.25
W_FUTURES = 2.50
W_PRICE_STRUCTURE_3 = 1.20
W_PRICE_STRUCTURE_15 = 1.50
W_OPTION_OI = 1.70
W_OPTION_OI_CHANGE = 1.50
W_CHAIN_LEVELS = 1.30

# Predictive hard-confirmation thresholds. These are intentionally separate
# from the weighted score so Futures OI and option-chain structure cannot be
# drowned out by six Supertrend votes.
FUTURES_OI_MIN_PERSISTENCE = 0.50
FUTURES_OI_STRENGTH_THRESHOLD = 0.25
CHAIN_PREDICTIVE_STRENGTH_THRESHOLD = 0.15
CHAIN_WALL_PROXIMITY_ATR = 1.00
CHAIN_CHANGE_CONFIRM_THRESHOLD = 0.08
FUTURES_LIVE_OI_WEIGHT = 0.35

STATE_PCR_BULL_THRESHOLD = float(os.getenv("STATE_PCR_BULL_THRESHOLD", "1.20"))
STATE_PCR_BEAR_THRESHOLD = float(os.getenv("STATE_PCR_BEAR_THRESHOLD", "0.80"))
PCR_BUCKET_MINUTES = int(os.getenv("PCR_BUCKET_MINUTES", "15"))
PCR_PATTERN_MIN_MOVE = float(os.getenv("PCR_PATTERN_MIN_MOVE", "0.02"))
WALL_HEAVY_CHANGE_OI_RATIO = float(os.getenv("WALL_HEAVY_CHANGE_OI_RATIO", "0.08"))
WALL_HEAVY_CHANGE_MULTIPLIER = float(os.getenv("WALL_HEAVY_CHANGE_MULTIPLIER", "1.50"))
REVERSAL_WALL_PROXIMITY_ATR = float(os.getenv("REVERSAL_WALL_PROXIMITY_ATR", "0.75"))
REVERSAL_ACCEPTANCE_BARS = int(os.getenv("REVERSAL_ACCEPTANCE_BARS", "2"))
REVERSAL_VWAP_SLOPE_CHANGE_ATR = float(os.getenv("REVERSAL_VWAP_SLOPE_CHANGE_ATR", "0.05"))

MIN_DIRECTIONAL_COMPONENTS = 4
ENTRY_SCORE = 4.50

# Strict entry confirmation. A signal is emitted only when price structure
# agrees with the live derivatives/positioning picture. Missing/neutral
# confirmations are treated as WAIT rather than silently bypassed.
STRICT_ENTRY_CONFIRMATIONS = True
PCR_BULL_THRESHOLD = 1.05
PCR_BEAR_THRESHOLD = 0.95
MIN_ENTRY_CONFIRMATIONS = 4

# Trend-first decision engine.
# The scanner must not let a slowly changing option-chain wall or a higher
# timeframe Supertrend veto a clear intraday reversal.
INTRADAY_LOOKBACK_BARS = 8
INTRADAY_RECENT_BARS = 3
INTRADAY_TREND_TRIGGER = 0.75
CORE_BULL_TRIGGER = 2.50
CORE_BEAR_TRIGGER = -2.50
POSITIONING_HARD_OPPOSITE_STRENGTH = 0.65

# Overall-market decision engine.
# Direction is built from exactly five requested market pillars:
# Change-OI, PCR, NIFTY price/VWAP, overall NIFTY market movement, and
# NIFTY futures price/OI. Movement + VWAP identify price regime; derivatives
# confirm or qualify it without suppressing a genuine early reversal.
CORE_FACTOR_MIN_VOTES = int(os.getenv("CORE_FACTOR_MIN_VOTES", "3"))
CORE_FACTOR_MIN_SCORE = float(os.getenv("CORE_FACTOR_MIN_SCORE", "0.35"))
CORE_FACTOR_VOTE_THRESHOLD = float(os.getenv("CORE_FACTOR_VOTE_THRESHOLD", "0.20"))
CORE_CHANGE_OI_DEADZONE = float(os.getenv("CORE_CHANGE_OI_DEADZONE", "0.015"))
CORE_CHANGE_OI_FULL_SCALE = float(os.getenv("CORE_CHANGE_OI_FULL_SCALE", "0.08"))
CORE_PCR_BULL_THRESHOLD = float(os.getenv("CORE_PCR_BULL_THRESHOLD", "1.10"))
CORE_PCR_BEAR_THRESHOLD = float(os.getenv("CORE_PCR_BEAR_THRESHOLD", "0.90"))
CORE_VWAP_SLOPE_WEIGHT = float(os.getenv("CORE_VWAP_SLOPE_WEIGHT", "0.15"))
CORE_FUTURES_MIN_STRENGTH = float(os.getenv("CORE_FUTURES_MIN_STRENGTH", "0.20"))
MARKET_MOVEMENT_RECENT_WEIGHT = float(os.getenv("MARKET_MOVEMENT_RECENT_WEIGHT", "0.30"))
MARKET_MOVEMENT_SESSION_WEIGHT = float(os.getenv("MARKET_MOVEMENT_SESSION_WEIGHT", "0.70"))
REVERSAL_MIN_MOVEMENT_SCORE = float(os.getenv("REVERSAL_MIN_MOVEMENT_SCORE", "0.20"))
REVERSAL_MAX_OPPOSING_DERIVATIVE_SCORE = float(os.getenv("REVERSAL_MAX_OPPOSING_DERIVATIVE_SCORE", "0.75"))


# PRIMARY MARKET-STRUCTURE ENGINE
# The hierarchy is intentionally explicit:
#   1) NIFTY price relative to VWAP defines the directional environment
#   2) Option OI + Change-OI define authoritative structural support/resistance
#   3) Multi-window NIFTY price movement establishes persistence
#   4) Change-OI confirms the same direction
#   5) A support/resistance break strengthens the signal but is not required
#      for an already-established continuous trend
# Futures OI, PCR and Supertrend are confirmation/context only.
STRUCTURE_LEVEL_LOOKBACK_BARS = int(os.getenv("STRUCTURE_LEVEL_LOOKBACK_BARS", "12"))
STRUCTURE_LEVEL_MAX_DISTANCE_STEPS = float(os.getenv("STRUCTURE_LEVEL_MAX_DISTANCE_STEPS", "8"))
STRUCTURE_BREAK_BUFFER_ATR = float(os.getenv("STRUCTURE_BREAK_BUFFER_ATR", "0.08"))
STRUCTURE_HOLD_BARS = int(os.getenv("STRUCTURE_HOLD_BARS", "2"))
STRUCTURE_CHANGE_OI_CONFIRM = float(os.getenv("STRUCTURE_CHANGE_OI_CONFIRM", "0.08"))
STRUCTURE_CHANGE_OI_STRONG = float(os.getenv("STRUCTURE_CHANGE_OI_STRONG", "0.20"))
STRUCTURE_CHANGE_OI_CONFLICT = float(os.getenv("STRUCTURE_CHANGE_OI_CONFLICT", "0.35"))
STRUCTURE_VWAP_RECLAIM_BUFFER_ATR = float(os.getenv("STRUCTURE_VWAP_RECLAIM_BUFFER_ATR", "0.05"))
STRUCTURE_MIN_LEVEL_STRENGTH = float(os.getenv("STRUCTURE_MIN_LEVEL_STRENGTH", "0.20"))
STRUCTURE_ACTIVITY_PRICE_NOISE_PCT = float(os.getenv("STRUCTURE_ACTIVITY_PRICE_NOISE_PCT", "0.002"))
STRUCTURE_OI_WALL_WEIGHT = float(os.getenv("STRUCTURE_OI_WALL_WEIGHT", "0.70"))
STRUCTURE_FLOW_WEIGHT = float(os.getenv("STRUCTURE_FLOW_WEIGHT", "0.30"))
STRUCTURE_LEVEL_CANDIDATE_COUNT = int(os.getenv("STRUCTURE_LEVEL_CANDIDATE_COUNT", "6"))
STRUCTURE_LEVEL_MEDIAN_MULTIPLIER = float(os.getenv("STRUCTURE_LEVEL_MEDIAN_MULTIPLIER", "1.05"))
STRUCTURE_SWING_MIN_DISTANCE_ATR = float(os.getenv("STRUCTURE_SWING_MIN_DISTANCE_ATR", "0.10"))
STRUCTURE_LEVEL_MIN_GAP_POINTS = float(os.getenv("STRUCTURE_LEVEL_MIN_GAP_POINTS", "1.0"))
# Structural levels are option-OI levels. Price swings are retained only as
# secondary context for risk/targets and are never silently substituted into
# the authoritative support/resistance decision.
STRUCTURE_LEVEL_MIN_OI_RATIO = float(os.getenv("STRUCTURE_LEVEL_MIN_OI_RATIO", "0.60"))
STRUCTURE_LEVEL_PROXIMITY_DECAY_STEPS = float(os.getenv("STRUCTURE_LEVEL_PROXIMITY_DECAY_STEPS", "4.0"))
STRUCTURE_LEVEL_FLOW_BONUS = float(os.getenv("STRUCTURE_LEVEL_FLOW_BONUS", "0.25"))
STRUCTURE_LEVEL_FLOW_PENALTY = float(os.getenv("STRUCTURE_LEVEL_FLOW_PENALTY", "0.20"))
STRUCTURE_LEVEL_PERSIST_MAX_STEPS = float(os.getenv("STRUCTURE_LEVEL_PERSIST_MAX_STEPS", "6.0"))
# Continuous-trend classification: a small countertrend move is a pullback,
# not a regime reversal, while a material multi-bar recovery can weaken the
# directional state.
STRUCTURE_CONTINUOUS_MIN_SESSION_ATR = float(os.getenv("STRUCTURE_CONTINUOUS_MIN_SESSION_ATR", "0.20"))
STRUCTURE_CONTINUOUS_MIN_RECENT7_ATR = float(os.getenv("STRUCTURE_CONTINUOUS_MIN_RECENT7_ATR", "-0.10"))
STRUCTURE_CONTINUOUS_MAX_PULLBACK_ATR = float(os.getenv("STRUCTURE_CONTINUOUS_MAX_PULLBACK_ATR", "0.60"))
STRUCTURE_CONTINUOUS_MIN_TREND_STRENGTH = float(os.getenv("STRUCTURE_CONTINUOUS_MIN_TREND_STRENGTH", "0.30"))

# Entry confirmation controls. One scanner pass is sufficient once the overall
# market is aligned; forcing two polls would delay fast reversal/continuation entries.
CONTINUATION_CONFIRMATIONS_REQUIRED = int(
    os.getenv("CONTINUATION_CONFIRMATIONS_REQUIRED", "1")
)
CONTINUATION_MIN_DIRECTIONAL_BARS = int(
    os.getenv("CONTINUATION_MIN_DIRECTIONAL_BARS", "1")
)
CONTINUATION_PRICE_LOOKBACK_BARS = int(
    os.getenv("CONTINUATION_PRICE_LOOKBACK_BARS", "4")
)
CONTINUATION_MIN_NET_MOVE_ATR = float(
    os.getenv("CONTINUATION_MIN_NET_MOVE_ATR", "0.05")
)
OPTION_CONFIRMATION_LOOKBACK_BARS = int(
    os.getenv("OPTION_CONFIRMATION_LOOKBACK_BARS", "4")
)
OPTION_CONFIRMATION_RECENT_BARS = int(
    os.getenv("OPTION_CONFIRMATION_RECENT_BARS", "3")
)
OPTION_CONFIRMATION_MIN_NET_MOVE_ATR = float(
    os.getenv("OPTION_CONFIRMATION_MIN_NET_MOVE_ATR", "0.05")
)
OPTION_CONFIRMATION_LIVE_MIN_MOVE_ATR = float(
    os.getenv("OPTION_CONFIRMATION_LIVE_MIN_MOVE_ATR", "0.15")
)
OPTION_CONFIRMATION_REQUIRE_LATEST_BAR = os.getenv(
    "OPTION_CONFIRMATION_REQUIRE_LATEST_BAR", "1"
).strip().lower() not in {"0", "false", "no"}

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
STRUCTURAL_STOP_BUFFER_ATR = float(os.getenv("STRUCTURAL_STOP_BUFFER_ATR", "0.15"))
TRAIL_MIN_DISTANCE_ATR = float(os.getenv("TRAIL_MIN_DISTANCE_ATR", "0.25"))



# Strike health.
MIN_DELTA = 0.25
MAX_DELTA = 0.85
MAX_SPREAD_PCT = 0.12
# Theta is a ranking/risk factor for long-option selection, not a hard entry gate.
# Near expiry, theta can become very large and a rigid percentage cutoff can
# incorrectly reject every otherwise-tradable directional option.
EXPECTED_HOLDING_MINUTES = 60.0
THETA_WARNING_BURDEN = 0.10
MIN_OI = 100.0
MIN_VOLUME = 1.0

# Dynamic target and stop constraints.
MIN_T1_RISK_REWARD = 1.10
MIN_T2_RISK_REWARD = 1.60
OPTION_MAX_STOP_PCT = 0.30
OPTION_MIN_STOP_PCT = 0.15
# Option targets use the underlying structural targets, but the option-price
# projection is deliberately conservative.  The linear delta term is primary;
# the quadratic gamma term is capped so large underlying moves cannot create
# unrealistic premium targets.
OPTION_TARGET_GAMMA_MAX_FRACTION = float(
    os.getenv("OPTION_TARGET_GAMMA_MAX_FRACTION", "0.10")
)

# Trade monitoring.
REVERSAL_CONFIRMATIONS_REQUIRED = 2
STRUCTURE_REVERSAL_CONFIDENCE = 60.0

# Phase-aware state thresholds. These classify market movement separately from
# entry readiness, so conflicting derivatives can mark a weakening trend
# without falsely flipping the market direction.
WEAKENING_MIN_OPPOSITE_CONFIRMATIONS = 1
SIDEWAYS_CORE_THRESHOLD = 2.00

# URLs.
INSTRUMENT_SEARCH_URL = f"{BASE_URL}/v2/instruments/search"
OPTION_CONTRACT_URL = f"{BASE_URL}/v2/option/contract"
OPTION_CHAIN_URL = f"{BASE_URL}/v2/option/chain"
MARKET_QUOTE_URL = f"{BASE_URL}/v3/market-quote/quotes"
MARKET_STATUS_URL = f"{BASE_URL}/v2/market/status/NSE"
MARKET_HOLIDAY_URL = f"{BASE_URL}/v2/market/holidays"
MARKET_OI_URL = f"{BASE_URL}/v2/market/oi"
CHANGE_OI_URL = f"{BASE_URL}/v2/market/change-oi"
PCR_URL = f"{BASE_URL}/v2/market/pcr"
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
    gamma: float
    theta: float
    iv: float
    spread_pct: float
    theta_burden_pct_day: float


@dataclass(frozen=True)
class StructureResult:
    direction: str
    score: float
    confidence: float
    interpretation: str
    components: dict[str, float]
    timeframe_directions: dict[str, int]
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
    pcr_rate_15m: float
    pcr_higher_low: bool
    pcr_lower_high: bool
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
    gamma: float
    theta: float
    support_1: float
    support_2: float
    resistance_1: float
    resistance_2: float
    reasons: list[str]


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

def is_bse_holiday(current: datetime) -> bool:
    url = f"{MARKET_HOLIDAY_URL}/{current.strftime('%Y-%m-%d')}"
    try:
        payload = api_get(url, retries=2)
    except ScannerError as exc:
        # Availability of holiday API should not create a false "closed" result.
        logger.warning("Holiday API unavailable: %s", exc)
        return False

    data = payload.get("data")
    if isinstance(data, dict):
        return bool(data)
    if isinstance(data, list):
        return bool(data)
    return False


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


def get_current_session_futures_candles(instrument_key: str) -> pd.DataFrame:
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
    lookback_days: int = MAX_HISTORY_DAYS,
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


def merge_current_into_history(
    historical: pd.DataFrame,
    current: Optional[pd.DataFrame],
) -> pd.DataFrame:
    if current is None or current.empty:
        return historical
    combined = pd.concat([historical, current], ignore_index=True)
    return (
        combined.sort_values("timestamp")
        .drop_duplicates("timestamp", keep="last")
        .reset_index(drop=True)
    )


def _resample_intraday_bars(df: pd.DataFrame, interval_minutes: int) -> pd.DataFrame:
    """Resample 3m bars locally into higher NIFTY timeframes without crossing sessions."""
    if df is None or df.empty:
        return pd.DataFrame()
    if interval_minutes == 3:
        return df.copy().sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)

    work = df.copy().sort_values("timestamp").drop_duplicates("timestamp", keep="last")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"])
    work["local_date"] = work["timestamp"].dt.tz_convert(IST).dt.date
    rows: list[pd.DataFrame] = []

    for _, day in work.groupby("local_date", sort=True):
        local = day.copy()
        local["timestamp"] = local["timestamp"].dt.tz_convert(IST)
        local = local.set_index("timestamp").sort_index()
        local = local.between_time("09:15", "15:30", inclusive="both")
        if local.empty:
            continue
        agg = local.resample(
            f"{interval_minutes}min",
            origin="start_day",
            offset="9h15min",
            label="left",
            closed="left",
        ).agg(
            open=("open", "first"),
            high=("high", "max"),
            low=("low", "min"),
            close=("close", "last"),
            volume=("volume", "sum"),
            oi=("oi", "last"),
        )
        agg = agg.dropna(subset=["open", "high", "low", "close"]).reset_index()
        if not agg.empty:
            agg["timestamp"] = agg["timestamp"].dt.tz_convert("UTC")
            rows.append(agg)

    if not rows:
        return pd.DataFrame()
    return (
        pd.concat(rows, ignore_index=True)
        .sort_values("timestamp")
        .drop_duplicates("timestamp", keep="last")
        .reset_index(drop=True)
    )


def timeframe_snapshot(
    spot_key: str,
    base_3m: Optional[pd.DataFrame] = None,
) -> tuple[dict[int, pd.DataFrame], dict[int, int]]:
    """Build all NIFTY timeframe structures from one 3m history + current-session feed.

    The previous implementation made a historical + intraday API request for every
    timeframe (3/15/30/60/120/180), creating 12+ candle requests per scan. This
    version fetches the 3m series once and resamples locally, preserving indicator
    warm-up while materially reducing scan latency and API exposure.
    """
    current = base_3m if base_3m is not None and not base_3m.empty else get_intraday_candles(spot_key, 3, strict=False)
    historical = get_historical_candles(spot_key, 3, lookback_days=MAX_HISTORY_DAYS)
    merged = merge_current_into_history(historical, current)
    if merged.empty:
        raise ScannerError("Unable to build NIFTY timeframe data from 3m candles.")

    frames: dict[int, pd.DataFrame] = {}
    directions: dict[int, int] = {}
    for tf in TIMEFRAMES:
        bars = _resample_intraday_bars(merged, tf)
        completed = filter_completed_candles(bars, tf)
        if len(completed) < 25:
            raise ScannerError(f"Too few completed {tf}m candles for a stable Supertrend: {len(completed)} < 25.")
        st = calculate_supertrend(completed, period=SUPERTREND_PERIOD, factor=SUPERTREND_FACTOR)
        frames[tf] = st
        latest_dir = safe_float(st["direction"].iloc[-1], 0.0)
        directions[tf] = 1 if latest_dir > 0 else -1 if latest_dir < 0 else 0
        logger.info(
            "TF %dm: Supertrend=%s level=%.2f structure=%s",
            tf,
            "BULLISH" if directions[tf] > 0 else "BEARISH" if directions[tf] < 0 else "NEUTRAL",
            safe_float(st["supertrend"].iloc[-1]),
            market_structure_state(st, 8),
        )
    return frames, directions


def get_timeframe_candles(
    instrument_key: str,
    interval_minutes: int,
    min_bars: int = 25,
) -> pd.DataFrame:
    """
    Use historical V3 data for indicator warm-up and merge today's intraday data.
    This is critical for 60/120/180m Supertrend: computing ST from only 1-3
    current-day candles is structurally invalid.
    """
    history_days = 35 if interval_minutes <= 15 else 60

    historical = get_historical_candles(
        instrument_key,
        interval_minutes,
        lookback_days=history_days,
    )

    current = None
    try:
        current = get_intraday_candles(instrument_key, interval_minutes)
    except ScannerError as exc:
        logger.info(
            "Current intraday %dm refresh unavailable; using historical data: %s",
            interval_minutes,
            exc,
        )

    merged = merge_current_into_history(historical, current)

    if len(merged) < min_bars:
        raise ScannerError(
            f"Insufficient {interval_minutes}m bars: {len(merged)} < {min_bars}."
        )

    return merged


def filter_completed_candles(
    df: pd.DataFrame,
    interval_minutes: int,
    now: Optional[datetime] = None,
) -> pd.DataFrame:
    """
    Keep only bars whose full interval has completed.

    Timestamp is assumed to be the candle start time, which is the standard
    representation of OHLC time series returned by Upstox.
    """
    if df.empty:
        return df

    current = now or now_ist()
    local_ts = df["timestamp"].dt.tz_convert(IST)
    interval = pd.to_timedelta(interval_minutes, unit="m")
    completed = local_ts + interval <= current

    result = df.loc[completed].copy()
    return result.reset_index(drop=True)


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


def calculate_supertrend(
    df: pd.DataFrame,
    period: int = SUPERTREND_PERIOD,
    factor: float = SUPERTREND_FACTOR,
) -> pd.DataFrame:
    if df.empty:
        raise ScannerError("Cannot calculate Supertrend on empty data.")

    out = df.copy().reset_index(drop=True)
    atr = calculate_atr(out, period=period)
    out["atr"] = atr

    hl2 = (out["high"] + out["low"]) / 2.0
    upper_basic = hl2 + factor * atr
    lower_basic = hl2 - factor * atr

    upper = pd.Series(np.nan, index=out.index, dtype=float)
    lower = pd.Series(np.nan, index=out.index, dtype=float)
    direction = pd.Series(np.nan, index=out.index, dtype=float)
    st = pd.Series(np.nan, index=out.index, dtype=float)

    upper.iloc[0] = upper_basic.iloc[0]
    lower.iloc[0] = lower_basic.iloc[0]
    direction.iloc[0] = 1
    st.iloc[0] = lower.iloc[0]

    for i in range(1, len(out)):
        if (
            upper_basic.iloc[i] < upper.iloc[i - 1]
            or out["close"].iloc[i - 1] > upper.iloc[i - 1]
        ):
            upper.iloc[i] = upper_basic.iloc[i]
        else:
            upper.iloc[i] = upper.iloc[i - 1]

        if (
            lower_basic.iloc[i] > lower.iloc[i - 1]
            or out["close"].iloc[i - 1] < lower.iloc[i - 1]
        ):
            lower.iloc[i] = lower_basic.iloc[i]
        else:
            lower.iloc[i] = lower.iloc[i - 1]

        if out["close"].iloc[i] > upper.iloc[i - 1]:
            direction.iloc[i] = 1
        elif out["close"].iloc[i] < lower.iloc[i - 1]:
            direction.iloc[i] = -1
        else:
            direction.iloc[i] = direction.iloc[i - 1]

        st.iloc[i] = (
            lower.iloc[i] if direction.iloc[i] > 0 else upper.iloc[i]
        )

    out["supertrend"] = st
    out["direction"] = direction
    return out


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


def market_structure_state(
    df: pd.DataFrame,
    lookback: int = 8,
) -> str:
    if len(df) < 3:
        return "NEUTRAL"

    n = min(lookback, len(df))
    recent = df.tail(n)
    if len(recent) < 3:
        return "NEUTRAL"

    highs = recent["high"].to_numpy(dtype=float)
    lows = recent["low"].to_numpy(dtype=float)

    # Compare the latest third to the earliest third rather than one candle
    # against one candle; this is less noisy and captures HH/HL or LH/LL.
    split = max(1, len(recent) // 3)
    early_high = float(np.mean(highs[:split]))
    late_high = float(np.mean(highs[-split:]))
    early_low = float(np.mean(lows[:split]))
    late_low = float(np.mean(lows[-split:]))

    if late_high > early_high and late_low > early_low:
        return "BULLISH"
    if late_high < early_high and late_low < early_low:
        return "BEARISH"
    return "NEUTRAL"


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


def futures_price_oi_regime(
    futures_3m: pd.DataFrame,
    live_quote: Optional[dict[str, Any]] = None,
) -> tuple[str, int, float, float]:
    result = futures_oi_structure(futures_3m, live_quote)
    return (
        str(result["regime"]),
        int(result["bias"]),
        float(result["price_delta"]),
        float(result["oi_delta"]),
    )


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
        "gamma": safe_float(greeks.get("gamma"), 0.0),
        "theta": safe_float(greeks.get("theta"), 0.0),
        "iv": safe_float(greeks.get("iv"), 0.0),
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
                api.get("call_change"),
                safe_float(ce.get("oi")) - safe_float(ce.get("prev_oi")),
            )
            put_oi_change = safe_float(
                api.get("put_change"),
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
    price_session: Optional[pd.DataFrame] = None,
    vwap: Optional[float] = None,
    atr3: Optional[float] = None,
    previous_option_snapshot: Optional[dict[str, Any]] = None,
    expiry: str = "",
    previous_support: Optional[float] = None,
    previous_resistance: Optional[float] = None,
) -> dict[str, Any]:
    """Build the authoritative option-OI structural map.

    VWAP is the primary regime anchor. Option OI plus Change-OI establish the
    structural walls. Price swings are *not* substituted into support/resistance
    when an OI wall is absent; they remain secondary context only.

    The selected wall is the strongest meaningful put-OI wall below spot for
    support and call-OI wall above spot for resistance. OI concentration,
    proximity and wall-consistent flow determine wall strength. Once a level has
    been established, a previously persisted OI level may be retained when the
    current chain temporarily provides an incomplete/weak wall.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    atr = max(safe_float(atr3, 50.0), 1.0)

    if vwap is None:
        if price_session is None or price_session.empty:
            raise ScannerError("VWAP unavailable for structural analysis.")
        vwap, _, _ = vwap_snapshot(price_session)
    vwap_value = safe_float(vwap, spot)

    flow_map, flow_mode = _intraday_option_changes(
        chain,
        previous_option_snapshot,
        change_oi_by_strike,
        expiry,
    )

    entries: list[dict[str, Any]] = []
    for strike, row in rows.items():
        dist_steps = abs(float(strike) - atm) / step if step > 0 else 0.0
        if dist_steps > STRUCTURE_LEVEL_MAX_DISTANCE_STEPS:
            continue
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        flow = flow_map.get(float(strike), {})
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
            "proximity": 1.0 / (1.0 + dist_steps),
            "dist_steps": float(dist_steps),
        })

    if not entries:
        raise ScannerError("No nearby option-chain strikes available for structural analysis.")

    max_call_oi = max((float(x["call_oi"]) for x in entries), default=1.0)
    max_put_oi = max((float(x["put_oi"]) for x in entries), default=1.0)
    median_call_oi = float(np.median([float(x["call_oi"]) for x in entries]))
    median_put_oi = float(np.median([float(x["put_oi"]) for x in entries]))

    def _flow_quality(activity: str, side: str) -> float:
        a = str(activity).upper()
        if side == "support":
            if a == "PUT_WRITING":
                return 1.0
            if a in {"PUT_LONG_UNWINDING", "PUT_SHORT_COVERING"}:
                return 0.65
            if a == "PUT_BUYING":
                return 0.25
            return 0.50
        if a == "CALL_WRITING":
            return 1.0
        if a in {"CALL_LONG_UNWINDING", "CALL_SHORT_COVERING"}:
            return 0.65
        if a == "CALL_BUYING":
            return 0.25
        return 0.50

    def support_strength(x: dict[str, Any]) -> float:
        oi_ratio = min(float(x["put_oi"]) / max(max_put_oi, 1.0), 1.0)
        flow_quality = _flow_quality(x["put_activity"], "support")
        proximity = 1.0 / (1.0 + float(x["dist_steps"]) / max(STRUCTURE_LEVEL_PROXIMITY_DECAY_STEPS, 1.0))
        score = 0.60 * oi_ratio + 0.20 * proximity + 0.20 * flow_quality
        if float(x["put_oi"]) < median_put_oi * STRUCTURE_LEVEL_MEDIAN_MULTIPLIER:
            score *= 0.70
        return max(0.0, min(1.0, score))

    def resistance_strength(x: dict[str, Any]) -> float:
        oi_ratio = min(float(x["call_oi"]) / max(max_call_oi, 1.0), 1.0)
        flow_quality = _flow_quality(x["call_activity"], "resistance")
        proximity = 1.0 / (1.0 + float(x["dist_steps"]) / max(STRUCTURE_LEVEL_PROXIMITY_DECAY_STEPS, 1.0))
        score = 0.60 * oi_ratio + 0.20 * proximity + 0.20 * flow_quality
        if float(x["call_oi"]) < median_call_oi * STRUCTURE_LEVEL_MEDIAN_MULTIPLIER:
            score *= 0.70
        return max(0.0, min(1.0, score))

    support_pool = [x for x in entries if float(x["strike"]) < spot and float(x["put_oi"]) / max(max_put_oi, 1.0) >= STRUCTURE_LEVEL_MIN_OI_RATIO]
    resistance_pool = [x for x in entries if float(x["strike"]) > spot and float(x["call_oi"]) / max(max_call_oi, 1.0) >= STRUCTURE_LEVEL_MIN_OI_RATIO]

    # If the 60%-of-maximum filter is too strict, retain the top OI wall on each
    # side rather than inventing a price-derived structural level.
    if not support_pool:
        support_pool = [x for x in entries if float(x["strike"]) < spot]
        support_pool = sorted(support_pool, key=lambda x: (-float(x["put_oi"]), float(x["dist_steps"])))[:STRUCTURE_LEVEL_CANDIDATE_COUNT]
    if not resistance_pool:
        resistance_pool = [x for x in entries if float(x["strike"]) > spot]
        resistance_pool = sorted(resistance_pool, key=lambda x: (-float(x["call_oi"]), float(x["dist_steps"])))[:STRUCTURE_LEVEL_CANDIDATE_COUNT]

    support_ranked = sorted(
        [(x, support_strength(x)) for x in support_pool],
        key=lambda z: (-z[1], float(z[0]["dist_steps"])),
    )
    resistance_ranked = sorted(
        [(x, resistance_strength(x)) for x in resistance_pool],
        key=lambda z: (-z[1], float(z[0]["dist_steps"])),
    )

    support_level = float("nan")
    support_row: Optional[dict[str, Any]] = None
    support_score = 0.0
    for row, score in support_ranked:
        if score >= STRUCTURE_MIN_LEVEL_STRENGTH:
            support_level = float(row["strike"])
            support_row = row
            support_score = score
            break

    resistance_level = float("nan")
    resistance_row: Optional[dict[str, Any]] = None
    resistance_score = 0.0
    for row, score in resistance_ranked:
        if score >= STRUCTURE_MIN_LEVEL_STRENGTH:
            resistance_level = float(row["strike"])
            resistance_row = row
            resistance_score = score
            break

    # Persisted OI levels are stabilizers, not price-derived replacements. They
    # are retained only when still reasonably close to the current ATM region.
    if not math.isfinite(support_level) and previous_support is not None and math.isfinite(safe_float(previous_support, float("nan"))):
        ps = safe_float(previous_support, float("nan"))
        if ps < spot and abs(ps - spot) / max(step, 1.0) <= STRUCTURE_LEVEL_PERSIST_MAX_STEPS:
            support_level = ps
            support_row = next((x for x in entries if abs(float(x["strike"]) - ps) < 0.01), None)
            support_score = support_strength(support_row) if support_row else 0.0
            support_source = "PERSISTED_OPTION_OI"
        else:
            support_source = "NONE"
    else:
        support_source = "OPTION_OI" if math.isfinite(support_level) else "NONE"

    if not math.isfinite(resistance_level) and previous_resistance is not None and math.isfinite(safe_float(previous_resistance, float("nan"))):
        pr = safe_float(previous_resistance, float("nan"))
        if pr > spot and abs(pr - spot) / max(step, 1.0) <= STRUCTURE_LEVEL_PERSIST_MAX_STEPS:
            resistance_level = pr
            resistance_row = next((x for x in entries if abs(float(x["strike"]) - pr) < 0.01), None)
            resistance_score = resistance_strength(resistance_row) if resistance_row else 0.0
            resistance_source = "PERSISTED_OPTION_OI"
        else:
            resistance_source = "NONE"
    else:
        resistance_source = "OPTION_OI" if math.isfinite(resistance_level) else "NONE"

    # Secondary OI levels: next strongest distinct wall on each side.
    support_2 = support_level
    resistance_2 = resistance_level
    for row, score in support_ranked:
        level = float(row["strike"])
        if math.isfinite(support_level) and abs(level - support_level) < 0.01:
            continue
        if score >= STRUCTURE_MIN_LEVEL_STRENGTH:
            support_2 = level
            break
    for row, score in resistance_ranked:
        level = float(row["strike"])
        if math.isfinite(resistance_level) and abs(level - resistance_level) < 0.01:
            continue
        if score >= STRUCTURE_MIN_LEVEL_STRENGTH:
            resistance_2 = level
            break

    # Safe display fallbacks are not structural signals. They keep downstream
    # target/risk formatting numeric if the chain is temporarily incomplete.
    if not math.isfinite(support_level):
        support_level = float(spot - max(step, 0.75 * atr))
        support_2 = support_level
        support_source = "NO_OI_LEVEL"
    if not math.isfinite(resistance_level):
        resistance_level = float(spot + max(step, 0.75 * atr))
        resistance_2 = resistance_level
        resistance_source = "NO_OI_LEVEL"

    if not math.isfinite(support_2) or support_2 >= support_level:
        support_2 = support_level
    if not math.isfinite(resistance_2) or resistance_2 <= resistance_level:
        resistance_2 = resistance_level

    # Structural flow around the local OI walls. This is descriptive; direction
    # remains determined by NIFTY price/VWAP plus Change-OI confirmation.
    nearby = [x for x in entries if abs(float(x["strike"]) - atm) <= step * 5]
    bull_pressure = sum(
        x["proximity"] * (max(float(x["put_oi_change"]), 0.0) + max(-float(x["call_oi_change"]), 0.0))
        for x in nearby
    )
    bear_pressure = sum(
        x["proximity"] * (max(float(x["call_oi_change"]), 0.0) + max(-float(x["put_oi_change"]), 0.0))
        for x in nearby
    )
    pressure_den = bull_pressure + bear_pressure
    pressure_score = (bull_pressure - bear_pressure) / pressure_den if pressure_den > 0 else 0.0

    total_put_oi = sum(float(x["put_oi"]) for x in entries)
    total_call_oi = sum(float(x["call_oi"]) for x in entries)
    pcr = total_put_oi / total_call_oi if total_call_oi > 0 else float("nan")
    pcr_bias = 1 if math.isfinite(pcr) and pcr >= PCR_BULL_THRESHOLD else -1 if math.isfinite(pcr) and pcr <= PCR_BEAR_THRESHOLD else 0

    migration_bias = (
        -1 if (resistance_row and support_row and float(resistance_row["call_oi_change"]) > abs(float(support_row["put_oi_change"])) * 1.10) else
        1 if (support_row and resistance_row and float(support_row["put_oi_change"]) > abs(float(resistance_row["call_oi_change"])) * 1.10) else
        0
    )
    predictive_raw = 0.70 * pressure_score + 0.15 * (support_score - resistance_score) + 0.15 * migration_bias
    predictive_bias = 1 if predictive_raw >= CHAIN_PREDICTIVE_STRENGTH_THRESHOLD else -1 if predictive_raw <= -CHAIN_PREDICTIVE_STRENGTH_THRESHOLD else 0

    support_change_strength = min(abs(float(support_row["put_oi_change"])) / max(max_put_oi, 1.0), 1.0) if support_row else 0.0
    resistance_change_strength = min(abs(float(resistance_row["call_oi_change"])) / max(max_call_oi, 1.0), 1.0) if resistance_row else 0.0

    support_flow_bias = int(support_row["put_bias"]) if support_row else 0
    resistance_flow_bias = int(resistance_row["call_bias"]) if resistance_row else 0
    support_activity = str(support_row["put_activity"]) if support_row else "NO_OI_DATA"
    resistance_activity = str(resistance_row["call_activity"]) if resistance_row else "NO_OI_DATA"

    major_support = float(support_row["strike"]) if support_row else support_level
    major_resistance = float(resistance_row["strike"]) if resistance_row else resistance_level

    put_writing_at_support = support_activity == "PUT_WRITING"
    put_unwinding_at_support = support_activity in {"PUT_LONG_UNWINDING", "PUT_SHORT_COVERING"}
    call_writing_at_resistance = resistance_activity == "CALL_WRITING"
    call_unwinding_at_resistance = resistance_activity in {"CALL_LONG_UNWINDING", "CALL_SHORT_COVERING"}

    level_bias = 0
    if math.isfinite(vwap_value):
        if math.isfinite(resistance_level) and resistance_level > spot and resistance_score > support_score + 0.10:
            level_bias = -1
        elif math.isfinite(support_level) and support_level < spot and support_score > resistance_score + 0.10:
            level_bias = 1

    logger.info(
        "CHAIN STRUCTURE: VWAP=%.2f support=%.2f/%0.2f resistance=%.2f/%0.2f "
        "source=%s/%s flow_mode=%s change_flow=%+.3f bias=%+d predictive=%+d strength=%.3f",
        vwap_value, support_level, support_2, resistance_level, resistance_2,
        support_source, resistance_source, flow_mode, pressure_score, int(1 if pressure_score >= 0.08 else -1 if pressure_score <= -0.08 else 0),
        predictive_bias, abs(predictive_raw),
    )

    if support_row:
        logger.info(
            "CHAIN SUPPORT LEVEL: strike=%.0f source=%s put_oi=%.0f put_oi_change=%+.0f activity=%s flow_bias=%+d",
            support_level, support_source, float(support_row["put_oi"]), float(support_row["put_oi_change"]), support_activity, support_flow_bias,
        )
    if resistance_row:
        logger.info(
            "CHAIN RESISTANCE LEVEL: strike=%.0f source=%s call_oi=%.0f call_oi_change=%+.0f activity=%s flow_bias=%+d",
            resistance_level, resistance_source, float(resistance_row["call_oi"]), float(resistance_row["call_oi_change"]), resistance_activity, resistance_flow_bias,
        )

    return {
        "support_1": float(support_level), "support_2": float(support_2),
        "resistance_1": float(resistance_level), "resistance_2": float(resistance_2),
        "support_source": support_source, "resistance_source": resistance_source,
        "support_strength": float(support_score), "resistance_strength": float(resistance_score),
        "support_change_strength": float(support_change_strength), "resistance_change_strength": float(resistance_change_strength),
        "major_support": float(major_support), "major_resistance": float(major_resistance),
        "support_flow_bias": support_flow_bias, "resistance_flow_bias": resistance_flow_bias,
        "support_activity": support_activity, "resistance_activity": resistance_activity,
        "put_writing_at_support": put_writing_at_support,
        "put_unwinding_at_support": put_unwinding_at_support,
        "call_writing_at_resistance": call_writing_at_resistance,
        "call_unwinding_at_resistance": call_unwinding_at_resistance,
        "pressure_score": float(pressure_score),
        "normalized_diff": float(pressure_score),
        "normalized_change": int(migration_bias),
        "oi_bias": int(1 if pressure_score > 0.08 else -1 if pressure_score < -0.08 else 0),
        "change_bias": int(migration_bias),
        "predictive_bias": int(predictive_bias),
        "predictive_strength": float(abs(predictive_raw)),
        "level_bias": int(level_bias),
        "pcr": float(pcr) if math.isfinite(pcr) else float("nan"),
        "pcr_bias": int(pcr_bias),
        "flow_mode": flow_mode,
        "change_flow_score": float(pressure_score),
        "change_flow_bias": int(1 if pressure_score >= 0.08 else -1 if pressure_score <= -0.08 else 0),
    }

def get_daily_oi_confirmation(
    expiry: str,
) -> tuple[int, float]:
    """
    Optional v2 market/OI endpoint.
    The endpoint is date-based, so it is used as a secondary cross-check only.
    """
    today = now_ist().date().isoformat()

    try:
        payload = api_get(
            MARKET_OI_URL,
            {
                "instrument_key": NIFTY_KEY,
                "expiry": expiry,
                "date": today,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("Daily OI endpoint unavailable: %s", exc)
        return 0, 0.0

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return 0, 0.0

    total_put = safe_float(data.get("total_puts"))
    total_call = safe_float(data.get("total_calls"))
    denominator = total_put + total_call

    if denominator <= 0:
        return 0, 0.0

    pcr = total_put / total_call if total_call > 0 else 999.0
    score = (total_put - total_call) / denominator
    bias = 1 if score > 0.05 else -1 if score < -0.05 else 0

    logger.info(
        "DAILY OI: puts=%.0f calls=%.0f PCR=%.3f score=%+.3f bias=%+d",
        total_put, total_call, pcr, score, bias,
    )
    return bias, score


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
            by_strike[float(strike)] = {
                "call_change": safe_float(item.get("call_change_oi")),
                "put_change": safe_float(item.get("put_change_oi")),
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


def get_intraday_pcr(expiry: str) -> tuple[float, float, int, bool, bool]:
    """Return current PCR, 15-minute change, trend, and local turning-pattern flags."""
    today = now_ist().date().isoformat()
    try:
        payload = api_get(
            PCR_URL,
            {
                "instrument_key": NIFTY_KEY,
                "expiry": expiry,
                "date": today,
                "bucket_interval": PCR_BUCKET_MINUTES,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("PCR endpoint unavailable: %s", exc)
        return float("nan"), 0.0, 0, False, False

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return float("nan"), 0.0, 0, False, False

    fallback = safe_float(data.get("pcr"), float("nan"))
    values: list[float] = []
    insights = data.get("insights", [])
    if isinstance(insights, list):
        for row in insights:
            if not isinstance(row, dict):
                continue
            value = safe_float(row.get("pcr"), float("nan"))
            if math.isfinite(value):
                values.append(value)

    if not values:
        return fallback, 0.0, 0, False, False

    current = values[-1]
    previous = values[-2] if len(values) >= 2 else current
    rate = current - previous
    trend = 1 if rate > 0 else -1 if rate < 0 else 0

    higher_low = False
    lower_high = False
    if len(values) >= 4:
        prior = values[:-2]
        recent = values[-2:]
        higher_low = min(recent) >= min(prior) + PCR_PATTERN_MIN_MOVE
        lower_high = max(recent) <= max(prior) - PCR_PATTERN_MIN_MOVE

    logger.info(
        "PCR INTRADAY: current=%.3f rate_15m=%+.3f trend=%+d higher_low=%s lower_high=%s points=%d",
        current, rate, trend, higher_low, lower_high, len(values),
    )
    return current, rate, trend, higher_low, lower_high


# =============================================================================
# VWAP / TIMEFRAME STRUCTURE
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

def intraday_trend_snapshot(
    price_session: pd.DataFrame,
    vwap: float,
) -> tuple[int, float, float]:
    """Measure fast NIFTY-index intraday direction independently of derivatives.

    The index is the primary market-price series. Futures price/OI is consumed
    separately, preventing the futures basis from distorting price structure.
    """
    if price_session is None or price_session.empty:
        return 0, 0.0, 0.0

    work = price_session.copy().sort_values("timestamp")
    for col in ("high", "low", "close"):
        work[col] = pd.to_numeric(work[col], errors="coerce")
    work = work.dropna(subset=["high", "low", "close"])
    if len(work) < 3:
        return 0, 0.0, 0.0

    closes = work["close"].tail(INTRADAY_LOOKBACK_BARS)
    atr = calculate_atr(work).dropna()
    atr_value = max(
        float(atr.iloc[-1]) if not atr.empty and math.isfinite(float(atr.iloc[-1])) else 0.0,
        1.0,
    )

    net_move = float(closes.iloc[-1] - closes.iloc[0])
    recent_count = min(INTRADAY_RECENT_BARS + 1, len(closes))
    recent_move = float(closes.iloc[-1] - closes.iloc[-recent_count])

    recent = work.tail(min(INTRADAY_LOOKBACK_BARS, len(work)))
    split = max(1, len(recent) // 2)
    early = recent.iloc[:split]
    late = recent.iloc[-split:]

    higher_structure = (
        float(late["high"].mean()) > float(early["high"].mean())
        and float(late["low"].mean()) > float(early["low"].mean())
    )
    lower_structure = (
        float(late["high"].mean()) < float(early["high"].mean())
        and float(late["low"].mean()) < float(early["low"].mean())
    )

    price = float(closes.iloc[-1])
    vwap_bias = 1 if price > vwap else -1 if price < vwap else 0

    net_component = math.tanh(net_move / (1.25 * atr_value))
    recent_component = math.tanh(recent_move / (0.90 * atr_value))
    structure_component = 1.0 if higher_structure else -1.0 if lower_structure else 0.0

    raw_score = (
        1.55 * net_component
        + 1.35 * recent_component
        + 0.90 * structure_component
        + 0.75 * vwap_bias
    )

    bias = (
        1 if raw_score >= INTRADAY_TREND_TRIGGER
        else -1 if raw_score <= -INTRADAY_TREND_TRIGGER
        else 0
    )
    strength = min(abs(raw_score) / 4.0, 1.0)

    logger.info(
        "INDEX INTRADAY: bias=%+d strength=%.3f score=%+.2f "
        "net_%dbars=%+.2f recent_%dbars=%+.2f structure=%s vwap_bias=%+d",
        bias,
        strength,
        raw_score,
        len(closes) - 1,
        net_move,
        recent_count - 1,
        recent_move,
        "HH_HL" if higher_structure else "LH_LL" if lower_structure else "MIXED",
        vwap_bias,
    )
    return bias, float(strength), float(raw_score)


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

def entry_timing_filter(
    price_session: pd.DataFrame,
    direction: str,
    vwap: float,
    atr3: float,
    market_phase: Optional[str] = None,
) -> tuple[bool, str, float, float]:
    """Reject stale/chased entries while allowing genuine reversal setups.

    Continuations need a fresh breakout or pullback/reclaim. A reversal may use
    the reversal impulse itself as the fresh setup, but it still cannot be
    extended from VWAP or have a blow-off 3m candle.
    """
    if price_session is None or price_session.empty or direction not in {"BULLISH", "BEARISH"}:
        return False, "INSUFFICIENT_DATA", float("inf"), float("inf")

    work = price_session.copy().sort_values("timestamp")
    work = filter_completed_candles(work, 3)
    if len(work) < max(ENTRY_BREAKOUT_LOOKBACK_BARS + 1, 7):
        return False, "INSUFFICIENT_COMPLETED_3M_BARS", float("inf"), float("inf")

    atr = max(float(atr3), 1.0)
    price = float(work["close"].iloc[-1])
    vwap_distance_atr = abs(price - vwap) / atr
    latest_move_atr = abs(float(work["close"].iloc[-1] - work["close"].iloc[-2])) / atr

    if vwap_distance_atr > OVEREXTENSION_ATR:
        return False, "VWAP_EXTENDED", vwap_distance_atr, latest_move_atr
    if latest_move_atr > ENTRY_MAX_3M_MOVE_ATR:
        return False, "LATEST_3M_BLOWOFF", vwap_distance_atr, latest_move_atr

    prior = work.iloc[-(ENTRY_BREAKOUT_LOOKBACK_BARS + 1):-1]
    last = work.iloc[-1]
    buffer = ENTRY_BREAKOUT_BUFFER_ATR * atr

    if direction == "BULLISH":
        prior_level = float(prior["high"].max())
        fresh_breakout = float(last["close"]) > prior_level + buffer
        reclaim = (
            float(last["close"]) > float(work["close"].iloc[-2])
            and float(last["low"]) <= float(work["low"].tail(4).min())
        )
    else:
        prior_level = float(prior["low"].min())
        fresh_breakout = float(last["close"]) < prior_level - buffer
        reclaim = (
            float(last["close"]) < float(work["close"].iloc[-2])
            and float(last["high"]) >= float(work["high"].tail(4).max())
        )

    is_reversal = str(market_phase or "").upper().startswith((
        "BEARISH_TO_BULLISH_REVERSAL", "BULLISH_TO_BEARISH_REVERSAL"
    ))

    if fresh_breakout:
        return True, "FRESH_BREAKOUT", vwap_distance_atr, latest_move_atr
    if reclaim:
        return True, "PULLBACK_RECLAIM", vwap_distance_atr, latest_move_atr

    if is_reversal:
        # For a reversal, a sustained recent directional impulse is the fresh
        # setup even before a six-bar breakout is printed.
        recent_count = min(4, len(work))
        recent_move = float(work["close"].iloc[-1] - work["close"].iloc[-recent_count]) / atr
        if (
            abs(recent_move) >= REVERSAL_MIN_RECENT_MOVE_ATR
            and ((direction == "BULLISH" and recent_move > 0) or
                 (direction == "BEARISH" and recent_move < 0))
        ):
            return True, "REVERSAL_IMPULSE", vwap_distance_atr, latest_move_atr

    return False, "NO_FRESH_ENTRY_SETUP", vwap_distance_atr, latest_move_atr


def _directional_sign(direction: str) -> int:
    return 1 if str(direction).upper() == "BULLISH" else -1


def continuation_price_confirmation(
    price_session: pd.DataFrame,
    direction: str,
    tf_frames: Optional[dict[int, pd.DataFrame]],
    atr3: float,
) -> tuple[bool, str, dict[str, float]]:
    """Confirm that completed NIFTY 3m price structure agrees with the core trend.

    This is intentionally independent from the four-factor market-state score.
    It prevents a one-scan derivatives alignment from opening a CE/PE while
    the actual NIFTY 3m structure is still moving the other way.
    """
    stats = {
        "net_move_atr": 0.0,
        "latest_move_atr": 0.0,
        "directional_bars": 0.0,
        "completed_bars": 0.0,
        "supertrend_direction": 0.0,
    }
    if direction not in {"BULLISH", "BEARISH"}:
        return False, "INVALID_DIRECTION", stats

    work = (
        filter_completed_candles(
            price_session.copy().sort_values("timestamp"), 3
        )
        if price_session is not None and not price_session.empty
        else pd.DataFrame()
    )
    if len(work) < max(CONTINUATION_PRICE_LOOKBACK_BARS, 4):
        return False, "INSUFFICIENT_COMPLETED_3M_BARS", stats

    for column in ("open", "high", "low", "close"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["high", "low", "close"]).reset_index(drop=True)
    if len(work) < max(CONTINUATION_PRICE_LOOKBACK_BARS, 4):
        return False, "INVALID_3M_PRICE_DATA", stats

    lookback = work.tail(max(CONTINUATION_PRICE_LOOKBACK_BARS, 4))
    closes = lookback["close"].to_numpy(dtype=float)
    diffs = np.diff(closes)
    if len(diffs) < 3:
        return False, "INSUFFICIENT_3M_PRICE_CHANGES", stats

    atr = max(float(atr3), 1.0)
    net_move = float(closes[-1] - closes[0])
    latest_move = float(diffs[-1])
    target_sign = _directional_sign(direction)
    directional_bars = int(np.sum(diffs * target_sign > 0))

    stats.update(
        {
            "net_move_atr": net_move / atr,
            "latest_move_atr": latest_move / atr,
            "directional_bars": float(directional_bars),
            "completed_bars": float(len(work)),
        }
    )

    st_direction = 0
    try:
        frame3 = tf_frames.get(3) if isinstance(tf_frames, dict) else None
        if frame3 is not None and not frame3.empty and "direction" in frame3.columns:
            st_direction = int(safe_float(frame3["direction"].iloc[-1], 0.0))
        elif frame3 is not None and not frame3.empty and "supertrend" in frame3.columns:
            last_close = float(frame3["close"].iloc[-1])
            st = float(frame3["supertrend"].iloc[-1])
            st_direction = 1 if last_close >= st else -1
    except (IndexError, KeyError, TypeError, ValueError):
        st_direction = 0

    stats["supertrend_direction"] = float(st_direction)

    if st_direction != target_sign:
        return (
            False,
            f"3M_SUPERTREND_OPPOSES_{direction}",
            stats,
        )
    if directional_bars < CONTINUATION_MIN_DIRECTIONAL_BARS:
        return (
            False,
            f"3M_DIRECTIONAL_BARS_{direction}_{directional_bars}/{CONTINUATION_MIN_DIRECTIONAL_BARS}",
            stats,
        )
    if stats["net_move_atr"] * target_sign < CONTINUATION_MIN_NET_MOVE_ATR:
        return (
            False,
            f"3M_NET_MOVE_TOO_WEAK_{direction}_{stats['net_move_atr']:+.2f}ATR",
            stats,
        )
    if (
        OPTION_CONFIRMATION_REQUIRE_LATEST_BAR
        and latest_move * target_sign <= 0
    ):
        return False, f"3M_LATEST_BAR_OPPOSES_{direction}", stats

    return True, "3M_PRICE_ALIGNED", stats


def continuation_market_timing_filter(
    price_session: pd.DataFrame,
    direction: str,
    vwap: float,
    atr3: float,
    market_movement_factor: float,
    chain_levels: Optional[dict[str, Any]] = None,
) -> tuple[bool, str, float, float]:
    """Confirm entry only from the established structural break and current flow."""
    if price_session is None or price_session.empty or direction not in {"BULLISH", "BEARISH"}:
        return False, "INSUFFICIENT_DATA", float("inf"), float("inf")

    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 2:
        return False, "INSUFFICIENT_COMPLETED_3M_BARS", float("inf"), float("inf")
    closes = pd.to_numeric(work["close"], errors="coerce").dropna().to_numpy(dtype=float)
    if len(closes) < 2:
        return False, "INVALID_PRICE_DATA", float("inf"), float("inf")

    atr = max(float(atr3), 1.0)
    price = float(closes[-1])
    vwap_distance_atr = abs(price - vwap) / atr
    latest_move_atr = abs(closes[-1] - closes[-2]) / atr
    levels = chain_levels or {}
    support = safe_float(levels.get("support_1"), price)
    resistance = safe_float(levels.get("resistance_1"), price)
    flow = safe_float(levels.get("change_flow_score"), 0.0)
    buffer = STRUCTURE_BREAK_BUFFER_ATR * atr
    hold_n = max(STRUCTURE_HOLD_BARS, 2)
    recent = closes[-hold_n:] if len(closes) >= hold_n else closes

    # Entry timing can reject an overextended move, but cannot reject a pullback
    # simply because the latest 3m candle points the other way.
    if vwap_distance_atr > REGIME_ENTRY_MAX_VWAP_DISTANCE_ATR:
        return False, "VWAP_TOO_FAR_FOR_ENTRY", vwap_distance_atr, latest_move_atr

    if direction == "BEARISH":
        if price >= vwap - STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * atr:
            return False, "VWAP_RECLAIMED", vwap_distance_atr, latest_move_atr
        if price >= support - buffer:
            return False, "SUPPORT_NOT_BROKEN_OR_RECLAIMED", vwap_distance_atr, latest_move_atr
        if flow > -STRUCTURE_CHANGE_OI_CONFIRM:
            return False, "BEARISH_CHANGE_OI_NOT_CONFIRMING", vwap_distance_atr, latest_move_atr
        if len(recent) >= hold_n and not np.all(recent < support - buffer):
            return False, "BROKEN_SUPPORT_NOT_HOLDING", vwap_distance_atr, latest_move_atr
        return True, "STRUCTURAL_BEARISH_CONTINUATION", vwap_distance_atr, latest_move_atr

    if price <= vwap + STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * atr:
        return False, "VWAP_LOST", vwap_distance_atr, latest_move_atr
    if price <= resistance + buffer:
        return False, "RESISTANCE_NOT_BROKEN_OR_REJECTED", vwap_distance_atr, latest_move_atr
    if flow < STRUCTURE_CHANGE_OI_CONFIRM:
        return False, "BULLISH_CHANGE_OI_NOT_CONFIRMING", vwap_distance_atr, latest_move_atr
    if len(recent) >= hold_n and not np.all(recent > resistance + buffer):
        return False, "BROKEN_RESISTANCE_NOT_HOLDING", vwap_distance_atr, latest_move_atr
    return True, "STRUCTURAL_BULLISH_CONTINUATION", vwap_distance_atr, latest_move_atr


def option_momentum_confirmation(
    option: OptionCandidate,
    direction: str,
) -> tuple[bool, str, dict[str, float]]:
    """Advisory premium confirmation for the selected directional option.

    For a long CE or long PE entry, rising option premium is favorable. The
    option type, not the underlying direction sign, determines how premium
    movement should be interpreted. This prevents bearish PE moves from being
    sign-inverted into a false rejection.
    """
    stats = {
        "net_move_atr": 0.0, "latest_move_atr": 0.0, "live_move_atr": 0.0,
        "directional_bars": 0.0, "completed_bars": 0.0, "last_close": option.ltp,
        "aligned_net_move_atr": 0.0, "aligned_latest_move_atr": 0.0,
        "aligned_live_move_atr": 0.0,
    }
    if direction not in {"BULLISH", "BEARISH"}:
        return False, "INVALID_DIRECTION", stats
    expected_type = "CE" if direction == "BULLISH" else "PE"
    if option.option_type != expected_type:
        return False, "WRONG_OPTION_TYPE_FOR_DIRECTION", stats

    try:
        option_bars = get_intraday_candles(option.instrument_key, 3, strict=False)
    except Exception as exc:
        logger.info("OPTION MOMENTUM: %s %.0f unavailable: %s", option.option_type, option.strike, exc)
        return False, "OPTION_CANDLE_FETCH_FAILED", stats
    if option_bars is None or option_bars.empty:
        return False, "OPTION_3M_CANDLES_UNAVAILABLE", stats

    work = filter_completed_candles(option_bars.copy().sort_values("timestamp"), 3)
    if len(work) < max(OPTION_CONFIRMATION_LOOKBACK_BARS, 3):
        return False, "OPTION_INSUFFICIENT_COMPLETED_3M_BARS", stats
    for column in ("close", "high", "low"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["close", "high", "low"]).reset_index(drop=True)
    if len(work) < 3:
        return False, "OPTION_INVALID_3M_DATA", stats

    lookback = work.tail(max(OPTION_CONFIRMATION_LOOKBACK_BARS, 3))
    closes = lookback["close"].to_numpy(dtype=float)
    diffs = np.diff(closes)
    atr_series = calculate_atr(lookback).replace([np.inf, -np.inf], np.nan).dropna()
    atr = max(float(atr_series.iloc[-1]) if not atr_series.empty else 1.0, 0.01)

    net_move = float(closes[-1] - closes[0])
    latest_move = float(diffs[-1]) if len(diffs) else 0.0
    recent_count = min(OPTION_CONFIRMATION_RECENT_BARS, len(diffs))
    recent_diffs = diffs[-recent_count:] if recent_count else np.array([])
    directional_bars = int(np.sum(recent_diffs > 0))
    live_move = float(option.ltp - closes[-1])

    aligned_net = net_move / atr
    aligned_latest = latest_move / atr
    aligned_live = live_move / atr
    stats.update({
        "net_move_atr": net_move / atr,
        "latest_move_atr": latest_move / atr,
        "live_move_atr": live_move / atr,
        "directional_bars": float(directional_bars),
        "completed_bars": float(len(work)),
        "last_close": float(closes[-1]),
        "aligned_net_move_atr": aligned_net,
        "aligned_latest_move_atr": aligned_latest,
        "aligned_live_move_atr": aligned_live,
    })

    if (
        aligned_live >= REGIME_LIVE_OPTION_MIN_ALIGNED_ATR
        and aligned_latest >= -REGIME_LIVE_OPTION_MAX_ADVERSE_ATR
        and aligned_net >= -REGIME_OPTION_MAX_ADVERSE_NET_ATR
        and directional_bars >= 1
    ):
        return True, "LIVE_PREMIUM_ACCELERATION_CONFIRMED", stats
    if aligned_latest >= OPTION_CONFIRMATION_MIN_NET_MOVE_ATR and aligned_net >= -REGIME_OPTION_MAX_ADVERSE_NET_ATR:
        return True, "LAST_COMPLETED_PREMIUM_MOVE", stats
    if aligned_net >= OPTION_CONFIRMATION_MIN_NET_MOVE_ATR and directional_bars >= REGIME_REQUIRE_OPTION_DIRECTIONAL_BARS:
        return True, "RECENT_PREMIUM_TREND", stats
    return False, "OPTION_PREMIUM_NOT_CONFIRMING", stats


def infer_prior_session_direction(
    price_session: pd.DataFrame,
    current_direction: Optional[str] = None,
) -> tuple[Optional[str], str]:
    """Infer prior intraday direction from NIFTY-index 3m history.

    This works even when the saved market snapshot is NEUTRAL. The last decisive
    direction is reconstructed from earlier completed 3m bars rather than from
    a single previous scan.
    """
    if price_session is None or price_session.empty:
        return None, "NO_DATA"

    work = filter_completed_candles(price_session, 3)
    minimum = max(REVERSAL_LOOKBACK_BARS, REVERSAL_RECENT_BARS + 4)
    if len(work) < minimum:
        return None, "INSUFFICIENT_HISTORY"

    recent_count = min(REVERSAL_RECENT_BARS + 1, len(work) - 3)
    recent = work.tail(recent_count)
    prior_end = len(work) - recent_count
    prior_start = max(0, prior_end - REVERSAL_LOOKBACK_BARS)
    prior = work.iloc[prior_start:prior_end]

    if len(prior) < 4 or len(recent) < 3:
        return None, "INSUFFICIENT_WINDOWS"

    def window_score(window: pd.DataFrame) -> float:
        closes = pd.to_numeric(window["close"], errors="coerce").dropna()
        if len(closes) < 3:
            return 0.0
        atr = calculate_atr(window).dropna()
        atr_value = max(float(atr.iloc[-1]) if not atr.empty else 1.0, 1.0)
        net = float(closes.iloc[-1] - closes.iloc[0]) / atr_value
        return 1.40 * math.tanh(net / 1.4)

    prior_s = window_score(prior)
    recent_s = window_score(recent)

    if prior_s <= -0.35:
        prior_direction = "BEARISH"
    elif prior_s >= 0.35:
        prior_direction = "BULLISH"
    else:
        prior_direction = None

    current = (current_direction or "").upper()
    if current == "BULLISH" and prior_direction == "BEARISH" and recent_s >= 0.20:
        return prior_direction, "BEARISH_TO_BULLISH"
    if current == "BEARISH" and prior_direction == "BULLISH" and recent_s <= -0.20:
        return prior_direction, "BULLISH_TO_BEARISH"

    return prior_direction, "NO_CONFIRMED_TRANSITION"

def vwap_acceptance_context(
    price_session: pd.DataFrame,
    vwap: float,
    atr3: float,
) -> dict[str, Any]:
    """Measure completed-3m VWAP acceptance/rejection and slope change."""
    result = {
        "bull_acceptance": False, "bear_acceptance": False,
        "bull_cross": False, "bear_cross": False,
        "slope_change": 0.0, "current_slope": 0.0, "previous_slope": 0.0,
        "completed": 0,
    }
    if price_session is None or price_session.empty:
        return result
    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 3:
        return result
    for c in ("close", "high", "low"):
        work[c] = pd.to_numeric(work[c], errors="coerce")
    work = work.dropna(subset=["close", "high", "low"])
    if len(work) < 3:
        return result
    v = calculate_vwap(work).replace([np.inf, -np.inf], np.nan).dropna()
    if len(v) < 3:
        return result
    current_slope = float(v.iloc[-1] - v.iloc[-2])
    previous_slope = float(v.iloc[-2] - v.iloc[-3])
    result.update({
        "current_slope": current_slope,
        "previous_slope": previous_slope,
        "slope_change": current_slope - previous_slope,
        "completed": len(work),
    })
    n = max(2, REVERSAL_ACCEPTANCE_BARS)
    c = work["close"].tail(n).to_numpy(dtype=float)
    vw = v.tail(n).to_numpy(dtype=float)
    result["bull_acceptance"] = bool(len(c) == n and np.all(c > vw))
    result["bear_acceptance"] = bool(len(c) == n and np.all(c < vw))
    result["bull_cross"] = float(work["close"].iloc[-2]) <= float(v.iloc[-2]) and float(work["close"].iloc[-1]) > float(v.iloc[-1])
    result["bear_cross"] = float(work["close"].iloc[-2]) >= float(v.iloc[-2]) and float(work["close"].iloc[-1]) < float(v.iloc[-1])
    return result


def detect_false_breakout_trap(
    price_session: pd.DataFrame,
    spot: float,
    vwap: float,
    atr3: float,
    chain_levels: dict[str, Any],
) -> dict[str, Any]:
    """Detect wall breach + adverse wall OI + fast VWAP failure/reclaim."""
    result = {"detected": False, "direction": 0, "level": 0.0, "kind": "", "reason": ""}
    if price_session is None or price_session.empty:
        return result
    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 4:
        return result
    work = work.tail(6)
    atr = max(float(atr3), 1.0)
    buffer = ENTRY_BREAKOUT_BUFFER_ATR * atr
    ctx = vwap_acceptance_context(work, vwap, atr)
    r = safe_float(chain_levels.get("major_resistance"), float("nan"))
    s = safe_float(chain_levels.get("major_support"), float("nan"))

    if math.isfinite(r):
        breached = float(work["high"].iloc[:-1].max()) > r + buffer
        rejected = float(work["close"].iloc[-1]) < r and float(spot) < r
        vwap_failed = float(work["close"].iloc[-1]) < vwap and (ctx["bear_cross"] or float(spot) < vwap)
        if breached and rejected and vwap_failed and bool(chain_levels.get("call_writing_at_resistance")):
            return {
                "detected": True, "direction": -1, "level": r, "kind": "RESISTANCE_TRAP",
                "reason": f"Resistance {r:.2f} was breached, Call OI writing increased aggressively, and price failed back below VWAP.",
            }

    if math.isfinite(s):
        breached = float(work["low"].iloc[:-1].min()) < s - buffer
        rejected = float(work["close"].iloc[-1]) > s and float(spot) > s
        vwap_reclaimed = float(work["close"].iloc[-1]) > vwap and (ctx["bull_cross"] or float(spot) > vwap)
        if breached and rejected and vwap_reclaimed and bool(chain_levels.get("put_writing_at_support")):
            return {
                "detected": True, "direction": 1, "level": s, "kind": "SUPPORT_TRAP",
                "reason": f"Support {s:.2f} was breached, Put OI writing increased aggressively, and price reclaimed VWAP.",
            }

    return result


def overall_market_movement(
    price_session: pd.DataFrame,
    atr3: float,
) -> tuple[float, int, float, float, float]:
    """Measure the overall NIFTY movement without letting a short bounce erase trend.

    Returns:
        score in [-1, +1], directional bias, session net, recent-7-bar net,
        recent-3-bar net.

    The session component carries most of the weight so a temporary 3m bounce
    inside a still-bearish session does not flip the market regime. The recent
    component makes a fresh reversal visible quickly.
    """
    if price_session is None or price_session.empty:
        return 0.0, 0, 0.0, 0.0, 0.0

    work = filter_completed_candles(
        price_session.copy().sort_values("timestamp"), 3
    )
    if len(work) < 4:
        return 0.0, 0, 0.0, 0.0, 0.0

    closes = pd.to_numeric(work["close"], errors="coerce").dropna().to_numpy(dtype=float)
    if len(closes) < 4:
        return 0.0, 0, 0.0, 0.0, 0.0

    atr = max(float(atr3), 1.0)
    session_net = float(closes[-1] - closes[0])
    recent7_net = float(closes[-1] - closes[-min(8, len(closes))])
    recent3_net = float(closes[-1] - closes[-4])

    session_component = math.tanh(session_net / max(2.0 * atr, 1.0))
    recent_component = (
        0.60 * math.tanh(recent7_net / max(1.5 * atr, 1.0))
        + 0.40 * math.tanh(recent3_net / max(1.0 * atr, 1.0))
    )
    score = (
        MARKET_MOVEMENT_SESSION_WEIGHT * session_component
        + MARKET_MOVEMENT_RECENT_WEIGHT * recent_component
    )
    score = max(-1.0, min(1.0, float(score)))
    bias = 1 if score >= CORE_FACTOR_VOTE_THRESHOLD else -1 if score <= -CORE_FACTOR_VOTE_THRESHOLD else 0
    return score, bias, session_net, recent7_net, recent3_net


# =============================================================================
# MARKET STRUCTURE ENGINE
# =============================================================================

def resolve_change_oi_flow(
    intraday_score: float,
    intraday_bias: int,
    day_score: float,
    day_bias: int,
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
        if day_directional and (intra * day) < 0 and intra_abs >= STRUCTURE_CHANGE_OI_CONFLICT and day_abs >= STRUCTURE_CHANGE_OI_CONFLICT:
            # Current intraday flow is the most responsive signal, but a strong
            # cumulative contradiction is important enough to block confirmation.
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
    tf_frames: dict[int, pd.DataFrame],
    tf_directions: dict[int, int],
    chain_levels: dict[str, Any],
    daily_oi_bias: int,
    daily_oi_score: float,
    change_oi_bias: int,
    change_oi_score: float,
    futures_live_quote: Optional[dict[str, Any]] = None,
    previous_direction: Optional[str] = None,
    previous_phase: Optional[str] = None,
    previous_reversal_confirmations: int = 0,
    price_session: Optional[pd.DataFrame] = None,
    inferred_prior_direction: Optional[str] = None,
    transition_hint: Optional[str] = None,
    pcr_value: Optional[float] = None,
    pcr_rate_15m: float = 0.0,
    pcr_higher_low: bool = False,
    pcr_lower_high: bool = False,
) -> StructureResult:
    """Authoritative market-structure state machine.

    Primary direction:
        NIFTY price vs VWAP -> OI/Change-OI structural level -> break/hold.

    The latest 3m candle is context only. It can describe a pullback but cannot
    by itself flip a confirmed structural regime. Futures OI, PCR and
    Supertrend are secondary confirmation/context and never define direction.
    """
    primary_session = price_session if price_session is not None and not price_session.empty else futures_session
    vwap, vwap_slope, _ = vwap_snapshot(primary_session)

    futures_info = futures_oi_structure(futures_3m, futures_live_quote)
    futures_regime = str(futures_info.get("regime", "UNAVAILABLE"))
    futures_bias = int(futures_info.get("bias", 0))
    futures_strength = float(futures_info.get("oi_strength", 0.0))

    atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 1.0), 1.0)
    vwap_distance_atr = abs(spot - vwap) / atr3 if math.isfinite(vwap) else float("inf")

    work = filter_completed_candles(primary_session.copy().sort_values("timestamp"), 3)
    for c in ("open", "high", "low", "close"):
        if c in work.columns:
            work[c] = pd.to_numeric(work[c], errors="coerce")
    if not work.empty:
        work = work.dropna(subset=["open", "high", "low", "close"]).reset_index(drop=True)
    current_close = float(work["close"].iloc[-1]) if not work.empty else float(spot)
    latest_move = float(work["close"].iloc[-1] - work["close"].iloc[-2]) if len(work) >= 2 else 0.0

    support_1 = safe_float(chain_levels.get("support_1"), current_close - max(50.0, atr3))
    support_2 = safe_float(chain_levels.get("support_2"), support_1)
    resistance_1 = safe_float(chain_levels.get("resistance_1"), current_close + max(50.0, atr3))
    resistance_2 = safe_float(chain_levels.get("resistance_2"), resistance_1)
    change_flow_score = safe_float(chain_levels.get("change_flow_score"), safe_float(change_oi_score))
    change_flow_bias = int(chain_levels.get("change_flow_bias", 0))
    if change_flow_bias == 0:
        change_flow_bias = (
            1 if change_flow_score >= STRUCTURE_CHANGE_OI_CONFIRM
            else -1 if change_flow_score <= -STRUCTURE_CHANGE_OI_CONFIRM
            else 0
        )

    previous_support = safe_float(chain_levels.get("previous_support_1"), float("nan"))
    previous_resistance = safe_float(chain_levels.get("previous_resistance_1"), float("nan"))
    prior = (previous_direction or "").upper().strip()
    prior_phase = (previous_phase or "").upper().strip()
    break_buffer = STRUCTURE_BREAK_BUFFER_ATR * atr3

    bullish_prior = prior == "BULLISH" or prior_phase in {"BULLISH", "BULLISH_BREAKOUT", "CONTINUOUS_BULLISH"}
    bearish_prior = prior == "BEARISH" or prior_phase in {"BEARISH", "BEARISH_BREAKDOWN", "CONTINUOUS_BEARISH"}

    # Do not let the structural level chase an already-broken trend. Once a
    # confirmed bearish/bullish regime exists, its broken level stays the active
    # reference until price decisively reclaims it.
    if bearish_prior and math.isfinite(previous_support) and current_close < previous_support - break_buffer:
        support_1 = previous_support
        if math.isfinite(support_2) and support_2 >= support_1:
            support_2 = chain_levels.get("support_1", support_1)
    elif bullish_prior and math.isfinite(previous_resistance) and current_close > previous_resistance + break_buffer:
        resistance_1 = previous_resistance
        if math.isfinite(resistance_2) and resistance_2 <= resistance_1:
            resistance_2 = chain_levels.get("resistance_1", resistance_1)

    # Hard structural invariants. VWAP never becomes a support/resistance value.
    # IMPORTANT: after a breakout/breakdown, the broken level is allowed to sit
    # on the opposite side of current price because it remains the reference
    # level that price has broken through. Only missing/invalid levels are
    # synthesized here.
    if not math.isfinite(support_1):
        support_1 = current_close - max(STRUCTURE_LEVEL_MIN_GAP_POINTS, break_buffer)
    if not math.isfinite(resistance_1):
        resistance_1 = current_close + max(STRUCTURE_LEVEL_MIN_GAP_POINTS, break_buffer)
    if support_1 >= resistance_1:
        support_1 = min(support_1, current_close - max(STRUCTURE_LEVEL_MIN_GAP_POINTS, 1.0))
        resistance_1 = max(resistance_1, current_close + max(STRUCTURE_LEVEL_MIN_GAP_POINTS, 1.0))

    below_vwap = current_close < vwap - STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * atr3
    above_vwap = current_close > vwap + STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * atr3

    hold_bars = max(STRUCTURE_HOLD_BARS, 2)
    closes = work["close"].tail(hold_bars).to_numpy(dtype=float) if not work.empty else np.array([])
    below_support_bars = int(np.sum(closes < support_1 - break_buffer)) if len(closes) else 0
    above_resistance_bars = int(np.sum(closes > resistance_1 + break_buffer)) if len(closes) else 0

    flow_mode = str(chain_levels.get("flow_mode", "DAY_CHANGE_API_WARMUP")).upper()
    intraday_flow_score = change_flow_score
    intraday_flow_bias = change_flow_bias
    effective_change_flow, effective_change_bias, effective_change_source, change_flow_conflict = resolve_change_oi_flow(
        intraday_score=intraday_flow_score,
        intraday_bias=intraday_flow_bias,
        day_score=change_oi_score,
        day_bias=change_oi_bias,
        flow_mode=flow_mode,
    )
    change_flow_score = float(effective_change_flow)
    change_flow_bias = int(effective_change_bias)
    bearish_flow_ok = bool(change_flow_score <= -STRUCTURE_CHANGE_OI_CONFIRM and not change_flow_conflict)
    bullish_flow_ok = bool(change_flow_score >= STRUCTURE_CHANGE_OI_CONFIRM and not change_flow_conflict)

    price_info = price_action_regime_snapshot(primary_session, vwap, atr3)
    session_atr = safe_float(price_info.get("session_move_atr"), 0.0)
    recent7_atr = safe_float(price_info.get("recent7_move_atr"), 0.0)
    recent3_atr = safe_float(price_info.get("recent3_move_atr"), 0.0)
    recent12_atr = safe_float(price_info.get("recent12_move_atr"), 0.0)
    down_ratio = safe_float(price_info.get("directional_down_ratio"), 0.0)
    up_ratio = safe_float(price_info.get("directional_up_ratio"), 0.0)
    efficiency = safe_float(price_info.get("trend_efficiency"), 0.0)
    price_structure = str(price_info.get("structure", "MIXED")).upper()

    # VWAP + Change-OI establish directional environment. A multi-bar movement
    # measure establishes persistence. The latest 3 bars are never a primary veto.
    bearish_movement = bool(
        session_atr <= -0.15
        or recent12_atr <= -0.20
        or (price_structure == "LH_LL" and down_ratio >= 0.45)
    )
    bullish_movement = bool(
        session_atr >= 0.15
        or recent12_atr >= 0.20
        or (price_structure == "HH_HL" and up_ratio >= 0.45)
    )

    bearish_environment = bool(below_vwap and bearish_movement)
    bullish_environment = bool(above_vwap and bullish_movement)
    bearish_base = bool(below_vwap and bearish_flow_ok)
    bullish_base = bool(above_vwap and bullish_flow_ok)

    # Once a continuous regime is established, keep it through ordinary pullbacks.
    # A reversal requires both a VWAP-side transition and opposing price/flow evidence.
    strong_bullish_reversal = bool(
        above_vwap
        and bullish_flow_ok
        and (
            price_info.get("bullish_structure", False)
            or recent12_atr >= 0.35
        )
        and (price_info.get("trend_efficiency", 0.0) >= 0.20 or recent3_atr >= 0.35)
    )
    strong_bearish_reversal = bool(
        below_vwap
        and bearish_flow_ok
        and (
            price_info.get("bearish_structure", False)
            or recent12_atr <= -0.35
        )
        and (price_info.get("trend_efficiency", 0.0) >= 0.20 or recent3_atr <= -0.35)
    )

    carried_bearish = bool(
        bearish_prior
        and bearish_base
        and not strong_bullish_reversal
    )
    carried_bullish = bool(
        bullish_prior
        and bullish_base
        and not strong_bearish_reversal
    )

    fresh_bearish_break = bool(
        math.isfinite(support_1)
        and below_vwap
        and current_close < support_1 - break_buffer
        and below_support_bars >= max(1, STRUCTURE_HOLD_BARS)
        and bearish_flow_ok
    )
    fresh_bullish_break = bool(
        math.isfinite(resistance_1)
        and above_vwap
        and current_close > resistance_1 + break_buffer
        and above_resistance_bars >= max(1, STRUCTURE_HOLD_BARS)
        and bullish_flow_ok
    )

    continuous_bearish = bool(
        bearish_base
        and (bearish_movement or carried_bearish or fresh_bearish_break)
        and not strong_bullish_reversal
    )
    continuous_bullish = bool(
        bullish_base
        and (bullish_movement or carried_bullish or fresh_bullish_break)
        and not strong_bearish_reversal
    )

    if continuous_bearish and continuous_bullish:
        # Valid VWAP-side logic should make this impossible. If a malformed feed
        # creates both states, refuse a trade and retain only the Change-OI side.
        if change_flow_score < 0:
            continuous_bullish = False
        elif change_flow_score > 0:
            continuous_bearish = False
        else:
            continuous_bearish = continuous_bullish = False

    if continuous_bearish:
        direction = "BEARISH"
        market_phase = "CONTINUOUS_BEARISH"
        entry_confirmed = True
        confirmation_state = "STRUCTURAL_CONTINUATION"
        interpretation = "CONTINUOUS BEARISH — BELOW VWAP + SUSTAINED DOWNWARD STRUCTURE + CHANGE-OI CONFIRMED"
        scenario_trigger = (
            f"NIFTY remains below VWAP with bearish Change-OI and sustained bearish price structure; "
            f"support={support_1:.2f} is a strengthening breakdown trigger, not a prerequisite for the bearish regime."
        )
        scenario_invalidation = (
            f"Invalidate bearish structure on sustained VWAP reclaim with opposing Change-OI and/or decisive HH/HL transition. "
            f"A temporary 3m bounce alone does not invalidate the regime."
        )
    elif continuous_bullish:
        direction = "BULLISH"
        market_phase = "CONTINUOUS_BULLISH"
        entry_confirmed = True
        confirmation_state = "STRUCTURAL_CONTINUATION"
        interpretation = "CONTINUOUS BULLISH — ABOVE VWAP + SUSTAINED UPWARD STRUCTURE + CHANGE-OI CONFIRMED"
        scenario_trigger = (
            f"NIFTY remains above VWAP with bullish Change-OI and sustained bullish price structure; "
            f"resistance={resistance_1:.2f} is a strengthening breakout trigger, not a prerequisite for the bullish regime."
        )
        scenario_invalidation = (
            f"Invalidate bullish structure on sustained VWAP loss with opposing Change-OI and/or decisive LH/LL transition. "
            f"A temporary 3m dip alone does not invalidate the regime."
        )
    elif below_vwap and change_flow_conflict:
        direction = "BEARISH"
        market_phase = "BEARISH"
        entry_confirmed = False
        confirmation_state = "FLOW_WAIT"
        interpretation = "BEARISH — BELOW VWAP / BEARISH PRICE ENVIRONMENT, CHANGE-OI CONFLICT"
        scenario_trigger = f"Maintain bearish watch; wait for non-conflicting bearish Change-OI before continuous confirmation. Support={support_1:.2f}."
        scenario_invalidation = "Bearish bias weakens on sustained VWAP reclaim and bullish price structure."
    elif above_vwap and change_flow_conflict:
        direction = "BULLISH"
        market_phase = "BULLISH"
        entry_confirmed = False
        confirmation_state = "FLOW_WAIT"
        interpretation = "BULLISH — ABOVE VWAP / BULLISH PRICE ENVIRONMENT, CHANGE-OI CONFLICT"
        scenario_trigger = f"Maintain bullish watch; wait for non-conflicting bullish Change-OI before continuous confirmation. Resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish bias weakens on sustained VWAP loss and bearish price structure."
    elif below_vwap and bearish_flow_ok:
        direction = "BEARISH"
        market_phase = "BEARISH"
        entry_confirmed = False
        confirmation_state = "STRUCTURAL_WATCH"
        interpretation = "BEARISH — BELOW VWAP + BEARISH CHANGE-OI, CONTINUATION NOT YET ESTABLISHED"
        scenario_trigger = f"Maintain bearish bias; continuous bearish state requires sustained downward price structure and/or a confirmed support breakdown. Support={support_1:.2f}."
        scenario_invalidation = "Bearish bias weakens on sustained VWAP reclaim with opposing price structure and Change-OI."
    elif above_vwap and bullish_flow_ok:
        direction = "BULLISH"
        market_phase = "BULLISH"
        entry_confirmed = False
        confirmation_state = "STRUCTURAL_WATCH"
        interpretation = "BULLISH — ABOVE VWAP + BULLISH CHANGE-OI, CONTINUATION NOT YET ESTABLISHED"
        scenario_trigger = f"Maintain bullish bias; continuous bullish state requires sustained upward price structure and/or a confirmed resistance breakout. Resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish bias weakens on sustained VWAP loss with opposing price structure and Change-OI."
    elif bearish_environment:
        direction = "BEARISH"
        market_phase = "BEARISH"
        entry_confirmed = False
        confirmation_state = "FLOW_WAIT"
        interpretation = "BEARISH — PRICE/VWAP STRUCTURE DOWN, CHANGE-OI NOT CONFIRMING"
        scenario_trigger = f"Maintain bearish price watch; wait for bearish Change-OI confirmation. Support={support_1:.2f}."
        scenario_invalidation = "Bearish bias weakens on sustained VWAP reclaim and bullish price structure."
    elif bullish_environment:
        direction = "BULLISH"
        market_phase = "BULLISH"
        entry_confirmed = False
        confirmation_state = "FLOW_WAIT"
        interpretation = "BULLISH — PRICE/VWAP STRUCTURE UP, CHANGE-OI NOT CONFIRMING"
        scenario_trigger = f"Maintain bullish price watch; wait for bullish Change-OI confirmation. Resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish bias weakens on sustained VWAP loss and bearish price structure."
    else:
        direction = "NEUTRAL"
        market_phase = "SIDEWAYS"
        entry_confirmed = False
        confirmation_state = "NO_TRADE"
        interpretation = "SIDEWAYS / MIXED — NO STRUCTURAL DIRECTION CONFIRMED"
        scenario_trigger = f"Wait for VWAP-side alignment plus sustained price structure and Change-OI; support={support_1:.2f} resistance={resistance_1:.2f}."
        scenario_invalidation = "No directional entry while VWAP/price structure/Change-OI remain mixed."

    pcr = safe_float(pcr_value, safe_float(chain_levels.get("pcr"), float("nan")))
    pcr_bias = 1 if math.isfinite(pcr) and pcr >= 1.10 else -1 if math.isfinite(pcr) and pcr <= 0.90 else 0

    # Secondary confirmations are logged only; they do not vote on direction.
    secondary_confirmations = [
        int(below_vwap if direction == "BEARISH" else above_vwap if direction == "BULLISH" else False),
        int(bearish_flow_ok if direction == "BEARISH" else bullish_flow_ok if direction == "BULLISH" else False),
        int(futures_bias < 0 if direction == "BEARISH" else futures_bias > 0 if direction == "BULLISH" else False),
        int(pcr_bias < 0 if direction == "BEARISH" else pcr_bias > 0 if direction == "BULLISH" else False),
        int(tf_directions.get(3, 0) < 0 if direction == "BEARISH" else tf_directions.get(3, 0) > 0 if direction == "BULLISH" else False),
    ]
    confirmation_count = int(sum(secondary_confirmations))

    confidence = 40.0
    if direction in {"BULLISH", "BEARISH"}:
        confidence += 10.0 * confirmation_count
        confidence += 22.0 * abs(change_flow_score)
        confidence += 8.0 * min(vwap_distance_atr / 1.5, 1.0)
        if fresh_bullish_break or fresh_bearish_break:
            confidence += 8.0
        if continuous_bullish or continuous_bearish:
            confidence += 15.0
    confidence = min(95.0, max(5.0, confidence))

    structure_score = (
        8.0 if continuous_bullish else -8.0 if continuous_bearish
        else 5.0 if fresh_bullish_break else -5.0 if fresh_bearish_break
        else 2.0 if direction == "BULLISH" else -2.0 if direction == "BEARISH" else 0.0
    )

    reasons = [
        f"PRIMARY STRUCTURE: direction={direction}; phase={market_phase}; NIFTY={current_close:.2f}; VWAP={vwap:.2f}; distance={vwap_distance_atr:.2f}ATR.",
        f"STRUCTURAL LEVELS: support={support_1:.2f}/{support_2:.2f}; resistance={resistance_1:.2f}/{resistance_2:.2f}; break_buffer={break_buffer:.2f}; hold_bars={hold_bars}.",
        f"BREAK TEST: below_support_bars={below_support_bars}; above_resistance_bars={above_resistance_bars}; breakdown={fresh_bearish_break}; breakout={fresh_bullish_break}.",
        f"CHANGE-OI PRIMARY: effective={change_flow_score:+.3f}; bias={change_flow_bias:+d}; source={effective_change_source}; raw_intraday={intraday_flow_score:+.3f}; API_day_change={change_oi_score:+.3f}; mode={flow_mode}; conflict={change_flow_conflict}.",
        f"PRICE ACTION CONTEXT: structure={price_structure}; session={session_atr:+.2f}ATR; recent7={recent7_atr:+.2f}ATR; recent12={recent12_atr:+.2f}ATR; recent3={recent3_atr:+.2f}ATR; down_ratio={down_ratio:.2f}; up_ratio={up_ratio:.2f}; efficiency={efficiency:.2f}; recent 3-bar movement is context only.",
        f"FUTURES CONFIRMATION: regime={futures_regime}; bias={futures_bias:+d}; strength={futures_strength:.3f}.",
        f"PCR CONFIRMATION: value={pcr:.3f}; bias={pcr_bias:+d}; 15m_rate={pcr_rate_15m:+.3f}.",
        f"HIGHER-TF CONTEXT: {', '.join(f'{tf}m={tf_directions.get(tf,0):+d}' for tf in TIMEFRAMES)}.",
        f"SECONDARY CONFIRMATIONS: {confirmation_count}/5 align with {direction}; not used as primary directional voters.",
    ]

    logger.info(
        "CHANGE-OI RESOLUTION: effective=%+.3f bias=%+d source=%s raw_intraday=%+.3f api_day=%+.3f conflict=%s",
        change_flow_score, change_flow_bias, effective_change_source,
        intraday_flow_score, change_oi_score, change_flow_conflict,
    )
    logger.info(
        "STRUCTURE ENGINE: phase=%s direction=%s price=%.2f VWAP=%.2f support=%.2f resistance=%.2f "
        "ChangeOI=%+.3f flow=%+.3f below_support=%d above_resistance=%d breakout=%s breakdown=%s Entry=%s",
        market_phase, direction, current_close, vwap, support_1, resistance_1,
        change_oi_score, change_flow_score, below_support_bars, above_resistance_bars,
        fresh_bullish_break, fresh_bearish_break, entry_confirmed,
    )

    components = {
        "structure_change_oi": float(change_flow_score),
        "structure_change_oi_intraday_raw": float(intraday_flow_score),
        "structure_change_oi_day_raw": float(change_oi_score),
        "structure_change_oi_conflict": 1.0 if change_flow_conflict else 0.0,
        "structure_change_oi_source": effective_change_source,
        "structure_vwap": float(1 if above_vwap else -1 if below_vwap else 0),
        "structure_price_break": float(1 if fresh_bullish_break else -1 if fresh_bearish_break else 0),
        "structure_support": float(support_1),
        "structure_resistance": float(resistance_1),
        "structure_score": float(structure_score),
        "change_oi_api_score": float(change_oi_score),
        "change_oi_bias": float(change_oi_bias),
        "support_break_strength": float(max(0.0, (support_1 - current_close) / atr3)),
        "resistance_break_strength": float(max(0.0, (current_close - resistance_1) / atr3)),
        "below_support_bars": float(below_support_bars),
        "above_resistance_bars": float(above_resistance_bars),
        "intraday_trend": float(latest_move / atr3),
        "vwap_level": float(1 if above_vwap else -1 if below_vwap else 0),
        "recent3_movement_atr": float(latest_move / atr3),
        "price_session_atr": float(session_atr),
        "price_recent7_atr": float(recent7_atr),
        "price_recent3_atr": float(recent3_atr),
        "price_recent12_atr": float(recent12_atr),
        "price_directional_down_ratio": float(down_ratio),
        "price_directional_up_ratio": float(up_ratio),
        "price_trend_efficiency": float(efficiency),
        "price_structure": 1.0 if price_structure == "HH_HL" else -1.0 if price_structure == "LH_LL" else 0.0,
        "vwap_distance_atr": float(vwap_distance_atr),
        "bull_votes": float(secondary_confirmations.count(1) if direction == "BULLISH" else 0),
        "bear_votes": float(secondary_confirmations.count(1) if direction == "BEARISH" else 0),
        "chain_context": float(change_flow_score),
        "daily_oi_context": float(daily_oi_bias),
        "active_structure_level": float(support_1 if direction == "BEARISH" else resistance_1 if direction == "BULLISH" else float("nan")),
    }

    return StructureResult(
        direction=direction,
        score=float(structure_score),
        confidence=float(confidence),
        interpretation=interpretation,
        components=components,
        timeframe_directions={str(k): int(v) for k, v in tf_directions.items()},
        vwap=float(vwap),
        vwap_slope=float(vwap_slope),
        futures_regime=futures_regime,
        futures_bias=futures_bias,
        futures_oi_strength=futures_strength,
        futures_oi_persistence=float(futures_info.get("oi_persistence", 0.0)),
        futures_live_oi_change=float(futures_info.get("live_oi_change", float("nan"))),
        intraday_bias=1 if latest_move > 0 else -1 if latest_move < 0 else 0,
        intraday_strength=float(min(abs(latest_move) / atr3, 1.0)),
        intraday_score=float(latest_move / atr3),
        chain_predictive_bias=int(chain_levels.get("predictive_bias", change_flow_bias)),
        chain_predictive_strength=float(chain_levels.get("predictive_strength", abs(change_flow_score))),
        chain_level_bias=int(chain_levels.get("level_bias", 0)),
        support_strength=float(chain_levels.get("support_strength", 0.0)),
        resistance_strength=float(chain_levels.get("resistance_strength", 0.0)),
        support_change_strength=float(chain_levels.get("support_change_strength", 0.0)),
        resistance_change_strength=float(chain_levels.get("resistance_change_strength", 0.0)),
        support_1=float(support_1),
        support_2=float(support_2),
        resistance_1=float(resistance_1),
        resistance_2=float(resistance_2),
        market_phase=market_phase,
        entry_confirmed=bool(entry_confirmed),
        reversal_confirmations=0,
        confirmation_state=confirmation_state,
        pcr=pcr if math.isfinite(pcr) else float("nan"),
        pcr_bias=int(pcr_bias),
        pcr_rate_15m=float(pcr_rate_15m),
        pcr_higher_low=bool(pcr_higher_low),
        pcr_lower_high=bool(pcr_lower_high),
        false_breakout=False,
        trap_level=0.0,
        entry_trigger=scenario_trigger,
        invalidation_rule=scenario_invalidation,
        reasons=reasons,
    )

# OPTION SELECTION
# =============================================================================

def contract_lookup_from_chain(
    chain: list[dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"), float("nan"))
        if not math.isfinite(strike):
            continue

        for option_type in ("CE", "PE"):
            data = option_side_data(row, option_type)
            key = data.get("instrument_key")
            if key:
                out[str(key)] = {
                    "strike": strike,
                    "type": option_type,
                    "data": data,
                    "expiry": str(row.get("expiry", ""))[:10],
                }
    return out


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
        gamma=safe_float(data["gamma"]),
        theta=theta,
        iv=safe_float(data["iv"]),
        spread_pct=spread_pct,
        theta_burden_pct_day=theta_burden,
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
    market_phase: Optional[str] = None,
    *,
    require_option_momentum: bool = False,
) -> OptionCandidate:
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Option selection requires BULLISH or BEARISH.")

    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    atm_distance_steps = abs(atm - spot) / max(step, 1.0)

    # Fail safe rather than silently selecting a materially displaced strike.
    # This catches malformed/incomplete chains and prevents a stale chain from
    # converting an otherwise correct reversal into an obviously wrong option.
    if atm_distance_steps > 1.25:
        raise ScannerError(
            f"ATM strike sanity check failed: index spot={spot:.2f}, "
            f"nearest strike={atm:.0f}, step={step:.0f} "
            f"({atm_distance_steps:.2f} steps away)."
        )

    is_reversal = str(market_phase or "").upper() in {
        "BEARISH_TO_BULLISH_REVERSAL",
        "BEARISH_TO_BULLISH_REVERSAL_CONFIRMED",
        "BULLISH_TO_BEARISH_REVERSAL",
        "BULLISH_TO_BEARISH_REVERSAL_CONFIRMED",
    }

    expiry_dates = {
        parse_date(str(row.get("expiry", "")))
        for row in rows.values()
        if parse_date(str(row.get("expiry", ""))) is not None
    }
    expiry_day = now_ist().date() in expiry_dates

    # Preserve the scanner's directional ITM strike convention.
    # BULLISH -> ATM-1 CE, then ATM-2 CE as fallback.
    # BEARISH -> ATM+1 PE, then ATM+2 PE as fallback.
    # ATM is never the preferred directional strike. This convention is kept
    # unchanged here; the Oct-6 strike hopping was caused by false trade exits,
    # not by nondeterministic strike ranking.
    candidate_strikes = (
        [atm - step, atm - 2 * step]
        if direction == "BULLISH"
        else [atm + step, atm + 2 * step]
    )
    option_type = "CE" if direction == "BULLISH" else "PE"

    candidates: list[OptionCandidate] = []
    rejection_log: list[str] = []

    for target in candidate_strikes:
        target = round(float(target), 2)

        # Never depend on exact float equality.
        row_key = min(strikes, key=lambda s: abs(s - target))
        if abs(row_key - target) > 0.01:
            rejection_log.append(f"{option_type} {target:.0f} absent from chain")
            continue

        data = option_side_data(rows[row_key], option_type)

        if not data["instrument_key"]:
            rejection_log.append(f"{option_type} {row_key:.0f}: no instrument key")
            continue

        if data["ltp"] <= 0:
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid LTP")
            continue

        if data["oi"] < MIN_OI:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: OI {data['oi']:.0f} below {MIN_OI:.0f}"
            )
            continue

        if data["volume"] < MIN_VOLUME:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: volume {data['volume']:.0f} below {MIN_VOLUME:.0f}"
            )
            continue

        delta = safe_float(data["delta"], float("nan"))
        if not math.isfinite(delta):
            if option_type == "CE":
               delta = 0.50 + ((spot - target) / (2 * step)) * 0.15
            else:
                delta = -0.50 - ((target - spot) / (2 * step)) * 0.15
                delta = max(-0.95, min(0.95, delta))
            data["delta"] = delta

        bid = safe_float(data["bid"])
        ask = safe_float(data["ask"])
        if bid <= 0 or ask <= 0 or ask < bid:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: invalid bid/ask"
            )
            continue

        mid = (bid + ask) / 2.0
        spread_pct = (ask - bid) / mid if mid > 0 else 1.0
        if spread_pct > MAX_SPREAD_PCT:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: spread={spread_pct:.1%}"
            )
            continue

        theta = safe_float(data["theta"])
        theta_burden = abs(theta) / data["ltp"] if data["ltp"] > 0 else 999.0

        # Upstox exposes theta as a time-decay measure. For ranking a long
        # intraday option, we linearize it to the planned holding window only
        # as a risk estimate. This is intentionally NOT a hard rejection rule,
        # because theta is non-linear near expiry and can become very large.
        trading_day_minutes = 375.0  # 09:15-15:30 IST
        intraday_theta_burden = (
            theta_burden * EXPECTED_HOLDING_MINUTES / trading_day_minutes
        )
        if intraday_theta_burden > THETA_WARNING_BURDEN:
            logger.info(
                "OPTION HEALTH WARNING: %s %.0f has estimated %.1f%% theta burden for the planned holding window; ranking penalty only.",
                option_type, row_key, intraday_theta_burden * 100.0,
            )
        meta = {
            "strike": row_key,
            "type": option_type,
            "expiry": str(rows[row_key].get("expiry", ""))[:10],
        }
        candidate = build_option_candidate(meta, data)
        candidates.append(candidate)

    if not candidates:
        detail = "; ".join(rejection_log[-8:]) or "no valid candidates"
        raise ScannerError(
            f"No healthy directional {option_type} option. {detail}"
        )

    # Continuous entries require the option premium itself to confirm the
    # direction. Try both hard-permitted strikes; never let a healthy-looking
    # but falling option win solely on delta/spread/liquidity.
    if require_option_momentum and not is_reversal:
        confirmed: list[OptionCandidate] = []
        for candidate in candidates:
            ok, reason, momentum_stats = option_momentum_confirmation(
                candidate, direction
            )
            logger.info(
                "OPTION MOMENTUM: %s %.0f ltp=%.2f net=%.2fATR latest=%.2fATR "
                "directional_bars=%d/%d status=%s reason=%s",
                candidate.option_type,
                candidate.strike,
                candidate.ltp,
                momentum_stats["net_move_atr"],
                momentum_stats["latest_move_atr"],
                int(momentum_stats["directional_bars"]),
                OPTION_CONFIRMATION_RECENT_BARS,
                "PASS" if ok else "FAIL",
                reason,
            )
            if ok:
                confirmed.append(candidate)
            else:
                rejection_log.append(
                    f"{option_type} {candidate.strike:.0f}: {reason}"
                )

        if not confirmed:
            detail = "; ".join(rejection_log[-8:]) or "no option momentum confirmation"
            raise ScannerError(
                f"No directional {option_type} option with premium confirmation. {detail}"
            )
        candidates = confirmed

    if is_reversal:
        candidates = [
            x for x in candidates
            if abs(x.strike - spot) / max(step, 1.0) <= REVERSAL_STRIKE_MAX_DISTANCE_STEPS
        ]
        if not candidates:
            raise ScannerError(
                f"No reversal option within {REVERSAL_STRIKE_MAX_DISTANCE_STEPS:.2f} strike steps of index spot={spot:.2f}."
            )

    # Deterministic strike priority: nearest directional OTM strike wins when
    # valid; the second strike is only a fallback. Health remains a validity filter
    # and is logged, but it cannot cause ATM+2 to beat a healthy ATM+1.
    candidate_by_strike = {round(x.strike, 2): x for x in candidates}
    selected = None
    for preferred_strike in candidate_strikes:
        key = round(float(preferred_strike), 2)
        if key in candidate_by_strike:
            selected = candidate_by_strike[key]
            break
    if selected is None:
        raise ScannerError("No valid directional strike remained after strike filtering.")

    # Final hard invariant for continuous entries. This is deliberately checked
    # after candidate filtering/ranking so an invalid strike can NEVER propagate
    # into Signal -> state -> email.
    if not is_reversal:
        permitted = (
            {round(atm - step, 2), round(atm - 2.0 * step, 2)}
            if direction == "BULLISH"
            else {round(atm + step, 2), round(atm + 2.0 * step, 2)}
        )
        if round(selected.strike, 2) not in permitted:
            raise ScannerError(
                f"STRICT STRIKE VALIDATION FAILED: direction={direction} "
                f"ATM={atm:.2f} step={step:.2f} selected={selected.strike:.2f} "
                f"permitted={sorted(permitted)}"
            )
        if direction == "BULLISH" and selected.option_type != "CE":
            raise ScannerError("STRICT STRIKE VALIDATION FAILED: bullish entry must use CE.")
        if direction == "BEARISH" and selected.option_type != "PE":
            raise ScannerError("STRICT STRIKE VALIDATION FAILED: bearish entry must use PE.")

    logger.info(
        "OPTION SELECT: direction=%s ATM=%.0f -> %s %.0f | "
        "LTP=%.2f OI=%.0f volume=%.0f delta=%.3f spread=%.2f%% "
        "theta=%.4f burden=%.2f%%/day",
        direction, atm, selected.trading_symbol, selected.strike,
        selected.ltp, selected.oi, selected.volume, selected.delta,
        selected.spread_pct * 100.0, selected.theta,
        selected.theta_burden_pct_day * 100.0,
    )
    return selected


def validate_continuous_option_entry(
    option: OptionCandidate,
    chain: list[dict[str, Any]],
    direction: str,
    market_phase: str,
    spot: float,
) -> None:
    """Final pre-signal/pre-email invariant check for continuous trend trades."""
    phase = str(market_phase or "").upper()
    if phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}:
        return

    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    permitted = (
        {round(atm - step, 2), round(atm - 2.0 * step, 2)}
        if direction == "BULLISH"
        else {round(atm + step, 2), round(atm + 2.0 * step, 2)}
    )
    selected_strike = round(float(option.strike), 2)

    if selected_strike not in permitted:
        raise ScannerError(
            f"PRE-EMAIL STRIKE VALIDATION FAILED: {direction} continuous entry "
            f"requires {sorted(permitted)} but selected {selected_strike:.2f}."
        )

    expected_type = "CE" if direction == "BULLISH" else "PE"
    if option.option_type != expected_type:
        raise ScannerError(
            f"PRE-EMAIL OPTION TYPE VALIDATION FAILED: {direction} "
            f"requires {expected_type}, got {option.option_type}."
        )

    exact_row = rows.get(selected_strike)
    if exact_row is None:
        raise ScannerError(
            f"PRE-EMAIL CHAIN VALIDATION FAILED: strike {selected_strike:.2f} "
            "is not present in the live option chain."
        )

    side = option_side_data(exact_row, expected_type)
    live_key = str(side.get("instrument_key") or "")
    if not live_key or live_key != option.instrument_key:
        raise ScannerError(
            "PRE-EMAIL INSTRUMENT VALIDATION FAILED: selected instrument does not "
            "match the live chain contract at the selected strike."
        )

    if safe_float(side.get("ltp"), 0.0) <= 0:
        raise ScannerError(
            f"PRE-EMAIL LTP VALIDATION FAILED: {expected_type} {selected_strike:.2f} has invalid LTP."
        )

    logger.info(
        "STRICT STRIKE VALIDATION PASSED: direction=%s phase=%s ATM=%.0f step=%.0f selected=%s %.0f permitted=%s",
        direction, phase, atm, step, expected_type, selected_strike, sorted(permitted),
    )


# =============================================================================
# DYNAMIC LEVEL / GREEK TARGET ENGINE
# =============================================================================

def choose_underlying_levels(
    structure: StructureResult,
    spot: float,
    tf_frames: dict[int, pd.DataFrame],
) -> tuple[float, float, float]:
    """Build T1/T2/SL from the next structural wall or 1.5x/3x ATR.

    T1 prefers the next major option-chain wall when it is sufficiently
    separated from spot; otherwise it falls back to 1.5 ATR. T2 prefers the
    second wall; otherwise it uses 3 ATR. The stop sits behind the nearest
    structural anchor, using VWAP, Supertrend and the opposite option wall.
    """
    atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 0.0), 1.0)
    atr15 = max(safe_float(tf_frames[15]["atr"].iloc[-1], atr3), atr3)

    # Keep the risk model realistic for unusually large ATR readings.
    max_allowed_atr = max(spot * 0.0025, 1.0)
    atr3 = min(atr3, max_allowed_atr)
    atr15 = min(max(atr15, atr3), max_allowed_atr * 1.5)

    st3 = safe_float(tf_frames[3]["supertrend"].iloc[-1], spot)
    st15 = safe_float(tf_frames[15]["supertrend"].iloc[-1], spot)

    is_bear = structure.direction == "BEARISH"
    if is_bear:
        wall1 = structure.support_1 if structure.support_1 < spot else float("nan")
        wall2 = structure.support_2 if structure.support_2 < spot else float("nan")
        wall1_dist = spot - wall1 if math.isfinite(wall1) else 0.0
        target1 = wall1 if wall1_dist >= 0.50 * atr3 else spot - 1.50 * atr3
        if math.isfinite(wall2) and wall2 < target1 and (spot - wall2) >= 1.00 * atr3:
            target2 = wall2
        else:
            target2 = spot - 3.00 * atr3

        recent_swing_high = safe_float(tf_frames[3]["high"].tail(6).max(), spot)
        stop_candidates = [
            structure.vwap + 0.25 * atr3,
            st3 + 0.20 * atr3,
            st15 + 0.20 * atr15,
            recent_swing_high + STRUCTURAL_STOP_BUFFER_ATR * atr3,
        ]
        if structure.resistance_1 > spot:
            stop_candidates.append(structure.resistance_1 + 0.25 * atr3)
        # For a bearish trade the nearest valid anchor above spot is the stop.
        underlying_stop = min(x for x in stop_candidates if x > spot)
        if underlying_stop <= spot:
            underlying_stop = spot + 0.80 * atr3

        target1 = min(target1, spot - 0.25 * atr3)
        target2 = min(target2, target1 - 0.50 * atr3)
        return float(target1), float(target2), float(underlying_stop)

    wall1 = structure.resistance_1 if structure.resistance_1 > spot else float("nan")
    wall2 = structure.resistance_2 if structure.resistance_2 > spot else float("nan")
    wall1_dist = wall1 - spot if math.isfinite(wall1) else 0.0
    target1 = wall1 if wall1_dist >= 0.50 * atr3 else spot + 1.50 * atr3
    if math.isfinite(wall2) and wall2 > target1 and (wall2 - spot) >= 1.00 * atr3:
        target2 = wall2
    else:
        target2 = spot + 3.00 * atr3

    recent_swing_low = safe_float(tf_frames[3]["low"].tail(6).min(), spot)
    stop_candidates = [
        structure.vwap - 0.25 * atr3,
        st3 - 0.20 * atr3,
        st15 - 0.20 * atr15,
        recent_swing_low - STRUCTURAL_STOP_BUFFER_ATR * atr3,
    ]
    if structure.support_1 < spot:
        stop_candidates.append(structure.support_1 - 0.25 * atr3)
    # For a bullish trade the nearest valid anchor below spot is the stop.
    underlying_stop = max(x for x in stop_candidates if x < spot)
    if underlying_stop >= spot:
        underlying_stop = spot - 0.80 * atr3

    target1 = max(target1, spot + 0.25 * atr3)
    target2 = max(target2, target1 + 0.50 * atr3)
    return float(target1), float(target2), float(underlying_stop)


def project_option_premium(
    entry: float,
    underlying_move: float,
    delta: float,
    gamma: float,
) -> float:
    """Conservative long-option premium projection for target estimation.

    The first-order delta estimate is the primary component.  Gamma is allowed
    only as a bounded adjustment (default 10% of the delta contribution). This
    prevents a large dS² term from exploding T1/T2 while still acknowledging
    that delta changes as the option moves ITM/OTM. This is a target estimate,
    not a pricing model or execution guarantee.
    """
    move = abs(float(underlying_move))
    first_order = abs(float(delta)) * move
    raw_gamma = 0.5 * abs(float(gamma)) * move * move
    gamma_cap = max(0.0, OPTION_TARGET_GAMMA_MAX_FRACTION) * first_order
    gamma_adjustment = min(raw_gamma, gamma_cap)
    change = first_order + gamma_adjustment
    return float(max(0.0, entry + change))


def migrate_active_trade_targets(
    trade: dict[str, Any],
) -> bool:
    """Migrate one legacy active trade to the V21 target engine exactly once.

    The migration deliberately uses the trade's stored entry-underlying and
    underlying target/stop levels. It does not recompute structural levels from
    the current market, and it never runs again after the engine version is saved.
    If T1 has already been hit, the live monetary levels are preserved because
    changing a milestone retrospectively would alter an in-flight trade.
    """
    current_engine = str(trade.get("target_engine_version", "")).strip()
    if current_engine == OPTION_TARGET_ENGINE_VERSION:
        return False

    if bool(trade.get("t1_hit", False)):
        logger.warning(
            "TARGET ENGINE MIGRATION: preserving legacy levels because T1 is already hit | %s",
            trade.get("trading_symbol", ""),
        )
        trade["target_engine_version"] = OPTION_TARGET_ENGINE_VERSION
        return True

    entry = safe_float(trade.get("entry"), float("nan"))
    entry_underlying = safe_float(trade.get("entry_underlying"), float("nan"))
    underlying_t1 = safe_float(trade.get("underlying_target_1"), float("nan"))
    underlying_t2 = safe_float(trade.get("underlying_target_2"), float("nan"))
    underlying_stop = safe_float(trade.get("underlying_stop"), float("nan"))
    delta = safe_float(trade.get("delta"), float("nan"))
    gamma = safe_float(trade.get("gamma"), 0.0)
    direction = str(trade.get("direction", "")).upper()

    values = (entry, entry_underlying, underlying_t1, underlying_t2, underlying_stop, delta)
    if not all(math.isfinite(v) for v in values):
        logger.warning(
            "TARGET ENGINE MIGRATION: insufficient stored levels/Greeks; preserving legacy levels | %s",
            trade.get("trading_symbol", ""),
        )
        return False

    if direction == "BEARISH":
        move_t1 = entry_underlying - underlying_t1
        move_t2 = entry_underlying - underlying_t2
        adverse_move = underlying_stop - entry_underlying
    elif direction == "BULLISH":
        move_t1 = underlying_t1 - entry_underlying
        move_t2 = underlying_t2 - entry_underlying
        adverse_move = entry_underlying - underlying_stop
    else:
        logger.warning(
            "TARGET ENGINE MIGRATION: unknown direction=%s; preserving legacy levels | %s",
            direction, trade.get("trading_symbol", ""),
        )
        return False

    if move_t1 <= 0 or move_t2 <= move_t1 or adverse_move <= 0 or entry <= 0:
        logger.warning(
            "TARGET ENGINE MIGRATION: stored underlying levels invalid; preserving legacy levels | %s "
            "entry_u=%.2f T1u=%.2f T2u=%.2f SLu=%.2f",
            trade.get("trading_symbol", ""), entry_underlying, underlying_t1, underlying_t2, underlying_stop,
        )
        return False

    target1 = project_option_premium(entry, move_t1, delta, gamma)
    target2 = project_option_premium(entry, move_t2, delta, gamma)

    delta_abs = abs(delta)
    gamma_abs = abs(gamma)
    estimated_loss = (delta_abs * adverse_move) - (0.5 * gamma_abs * adverse_move * adverse_move)
    estimated_loss = max(0.0, estimated_loss)
    min_loss = entry * OPTION_MIN_STOP_PCT
    max_loss = entry * OPTION_MAX_STOP_PCT
    risk = min(max(estimated_loss, min_loss), max_loss)
    stop_loss = entry - risk

    min_t1 = entry + MIN_T1_RISK_REWARD * risk
    min_t2 = entry + MIN_T2_RISK_REWARD * risk
    target1 = max(target1, min_t1)
    target2 = max(target2, min_t2, target1 + 0.25 * risk)

    if not (stop_loss < entry < target1 < target2):
        logger.warning(
            "TARGET ENGINE MIGRATION: generated levels invalid; preserving legacy levels | %s",
            trade.get("trading_symbol", ""),
        )
        return False

    old = (
        safe_float(trade.get("target_1"), float("nan")),
        safe_float(trade.get("target_2"), float("nan")),
        safe_float(trade.get("stop_loss"), float("nan")),
    )
    trade["target_1"] = round(target1, 2)
    trade["target_2"] = round(target2, 2)
    trade["stop_loss"] = round(stop_loss, 2)
    trade["target_engine_version"] = OPTION_TARGET_ENGINE_VERSION

    logger.info(
        "TARGET ENGINE MIGRATED: %s | old T1=%.2f T2=%.2f SL=%.2f -> "
        "V21 T1=%.2f T2=%.2f SL=%.2f | entry_u=%.2f T1u=%.2f T2u=%.2f SLu=%.2f",
        trade.get("trading_symbol", ""), old[0], old[1], old[2],
        target1, target2, stop_loss, entry_underlying, underlying_t1, underlying_t2, underlying_stop,
    )
    return True


def project_option_premium_signed(
    entry: float,
    underlying_move: float,
    delta: float,
    gamma: float,
) -> float:
    """Signed second-order premium projection for trailing-stop estimation."""
    move = float(underlying_move)
    change = float(delta) * move + 0.5 * abs(float(gamma)) * move * move
    return float(max(0.0, entry + change))


def create_dynamic_targets(
    option: OptionCandidate,
    structure: StructureResult,
    spot: float,
    tf_frames: dict[int, pd.DataFrame],
) -> tuple[float, float, float, float, float, float]:
    """Create option and underlying targets without allowing risk math to crash a valid signal.

    Important: the option is long, so an adverse underlying move must reduce
    premium. The previous implementation accidentally used the *positive*
    premium projection for the adverse move; with a high-delta/high-gamma
    option that could make ``adverse_premium >= entry`` and produce zero risk.
    """
    target_u1, target_u2, stop_u = choose_underlying_levels(
        structure, spot, tf_frames,
    )

    atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 0.0), 1.0)
    atr15 = max(safe_float(tf_frames[15]["atr"].iloc[-1], atr3), atr3)

    # Final defensive validation/fallback for unusual chain levels.
    if structure.direction == "BEARISH":
        if target_u1 >= spot:
            target_u1 = spot - 0.75 * atr3
        if target_u2 >= target_u1:
            target_u2 = target_u1 - max(0.75 * atr3, 0.50 * atr15)
        if stop_u <= spot:
            stop_u = spot + 0.80 * atr3
        move_t1 = spot - target_u1
        move_t2 = spot - target_u2
        adverse_move = stop_u - spot
    else:
        if target_u1 <= spot:
            target_u1 = spot + 0.75 * atr3
        if target_u2 <= target_u1:
            target_u2 = target_u1 + max(0.75 * atr3, 0.50 * atr15)
        if stop_u >= spot:
            stop_u = spot - 0.80 * atr3
        move_t1 = target_u1 - spot
        move_t2 = target_u2 - spot
        adverse_move = spot - stop_u

    if move_t1 <= 0:
        move_t1 = 0.75 * atr3
        target_u1 = spot + move_t1 if structure.direction == "BULLISH" else spot - move_t1
    if move_t2 <= move_t1:
        move_t2 = max(1.25 * atr15, move_t1 + 0.50 * atr3)
        target_u2 = spot + move_t2 if structure.direction == "BULLISH" else spot - move_t2
    if adverse_move <= 0:
        adverse_move = 0.80 * atr3
        stop_u = spot - adverse_move if structure.direction == "BULLISH" else spot + adverse_move

    target1 = project_option_premium(option.ltp, move_t1, option.delta, option.gamma)
    target2 = project_option_premium(option.ltp, move_t2, option.delta, option.gamma)

    logger.info(
        "OPTION TARGET PROJECTION: move1=%.2f move2=%.2f delta=%.3f gamma=%.5f "
        "gamma_cap=%.0f%% T1=%.2f T2=%.2f",
        move_t1, move_t2, abs(option.delta), abs(option.gamma),
        OPTION_TARGET_GAMMA_MAX_FRACTION * 100.0, target1, target2,
    )

    # Correct signed adverse-premium estimate for a LONG option.
    # First order loses premium; gamma partially offsets that loss.
    delta_abs = abs(option.delta)
    gamma_abs = abs(option.gamma)
    estimated_loss = (delta_abs * adverse_move) - (0.5 * gamma_abs * adverse_move * adverse_move)
    estimated_loss = max(0.0, estimated_loss)

    # Always keep a real, bounded monetary risk. This is a safety bound, not
    # a directional veto. Near-expiry/high-gamma options can otherwise make
    # the second-order approximation mathematically negative.
    min_loss = option.ltp * OPTION_MIN_STOP_PCT
    max_loss = option.ltp * OPTION_MAX_STOP_PCT
    risk = min(max(estimated_loss, min_loss), max_loss)
    stop_loss = option.ltp - risk

    # Guarantee valid ordering without rejecting a structurally valid market
    # signal merely because the option's local Greek approximation is noisy.
    min_t1 = option.ltp + MIN_T1_RISK_REWARD * risk
    min_t2 = option.ltp + MIN_T2_RISK_REWARD * risk
    target1 = max(target1, min_t1)
    target2 = max(target2, min_t2, target1 + 0.25 * risk)

    if not (stop_loss < option.ltp < target1 < target2):
        raise ScannerError(
            f"Invalid option risk levels after fallback: entry={option.ltp:.2f}, "
            f"SL={stop_loss:.2f}, T1={target1:.2f}, T2={target2:.2f}."
        )

    logger.info(
        "OPTION RISK: entry=%.2f SL=%.2f risk=%.2f (%.1f%%) T1=%.2f T2=%.2f | "
        "underlying T1=%.2f T2=%.2f SL=%.2f",
        option.ltp, stop_loss, risk, 100.0 * risk / option.ltp,
        target1, target2, target_u1, target_u2, stop_u,
    )

    return (
        round(target1, 2), round(target2, 2), round(stop_loss, 2),
        round(stop_u, 2), round(target_u1, 2), round(target_u2, 2),
    )


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
    """Return the exact six-part scanner output requested by the strategy spec."""
    return (
        f"1. Market State: [{signal.market_state}]\n"
        f"2. Bias: [{signal.bias}]\n"
        f"3. Entry Trigger: [{signal.entry_trigger}]\n"
        f"4. Targets:\n"
        f"   - T1: {signal.target_1:.2f} (underlying {signal.underlying_target_1:.2f})\n"
        f"   - T2: {signal.target_2:.2f} (underlying {signal.underlying_target_2:.2f})\n"
        f"5. Stop Loss: {signal.stop_loss:.2f} (underlying {signal.underlying_stop:.2f})\n"
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
<tr><td><b>Target 1</b></td><td>₹{signal.target_1:.2f}</td></tr>
<tr><td><b>Target 2</b></td><td>₹{signal.target_2:.2f}</td></tr>
<tr><td><b>Stop Loss</b></td><td>₹{signal.stop_loss:.2f}</td></tr>
<tr><td><b>Underlying T1</b></td><td>{signal.underlying_target_1:.2f}</td></tr>
<tr><td><b>Underlying T2</b></td><td>{signal.underlying_target_2:.2f}</td></tr>
<tr><td><b>Underlying SL</b></td><td>{signal.underlying_stop:.2f}</td></tr>
<tr><td><b>Delta</b></td><td>{signal.delta:.4f}</td></tr>
<tr><td><b>Gamma</b></td><td>{signal.gamma:.6f}</td></tr>
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


def monitor_active_trade(
    state: dict[str, Any],
    structure: StructureResult,
    tf_frames: Optional[dict[int, pd.DataFrame]] = None,
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
    target1 = safe_float(trade.get("target_1"))
    target2 = safe_float(trade.get("target_2"))
    stop = safe_float(trade.get("stop_loss"))
    t1_hit = bool(trade.get("t1_hit", False)) or ltp >= target1
    intrabar_outcome = None
    intrabar_exit_reference = None
    intrabar_reason = "DISABLED"

    if ACTIVE_TRADE_INTRABAR_MONITOR:
        try:
            option_1m_raw = get_intraday_candles(
                str(trade["instrument_key"]), 1, strict=False
            )
            option_1m = _prepare_active_trade_1m_window(trade, option_1m_raw)

            # A stop on the option is subordinate to the NIFTY structural stop.
            # Fetch the underlying 1m bars separately so an option IV/theta spike
            # cannot close a trade while NIFTY is still respecting its structure.
            underlying_1m = None
            if ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION:
                underlying_1m_raw = get_intraday_candles(
                    NIFTY_KEY, 1, strict=False
                )
                underlying_1m = _prepare_active_trade_1m_window(
                    trade, underlying_1m_raw
                )

            (
                intrabar_outcome,
                intrabar_exit_reference,
                intrabar_reason,
            ) = _active_trade_intrabar_exit(
                trade,
                option_1m,
                underlying_1m=underlying_1m,
                underlying_3m=(tf_frames or {}).get(3),
            )

            # Record the newest bar examined, but the helper always rechecks the
            # latest bar because that candle may still be forming.
            if option_1m is not None and not option_1m.empty:
                trade["intrabar_last_checked_at"] = (
                    option_1m["timestamp"].max().isoformat()
                )

            if intrabar_outcome:
                logger.info(
                    "ACTIVE TRADE INTRABAR: %s outcome=%s reference=%.2f reason=%s",
                    trade["trading_symbol"],
                    intrabar_outcome,
                    float(intrabar_exit_reference or 0.0),
                    intrabar_reason,
                )
            else:
                logger.info(
                    "ACTIVE TRADE INTRABAR: %s no exit | structure=%s",
                    trade["trading_symbol"],
                    intrabar_reason,
                )
        except Exception as exc:
            intrabar_reason = f"1M_MONITOR_ERROR:{exc}"
            logger.info(
                "Active trade 1m monitor unavailable: %s",
                exc,
            )

    if intrabar_outcome == "T1_HIT":
        t1_hit = True

    # A quote-only option stop is not allowed to override the underlying
    # structure when structural confirmation is enabled. The current NIFTY
    # snapshot is a second line of defence; the 1m structural breach is the
    # preferred intrabar path above.
    snapshot_for_stop = (
        state.get("market_snapshot")
        if isinstance(state.get("market_snapshot"), dict)
        else {}
    )
    spot_for_stop = safe_float(snapshot_for_stop.get("spot"), float("nan"))
    underlying_stop_for_quote = safe_float(
        trade.get("underlying_stop"), float("nan")
    )
    direction_for_quote = str(trade.get("direction", "")).upper()
    latest_3m_close = float("nan")
    latest_3m_bar = ""
    if tf_frames and 3 in tf_frames and not tf_frames[3].empty:
        latest_3m_close = safe_float(tf_frames[3]["close"].iloc[-1], float("nan"))
        latest_3m_bar = str(tf_frames[3]["timestamp"].iloc[-1])
    armed_bar = str(trade.get("underlying_stop_armed_bar") or "")
    quote_stop_structure_confirmed = not ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION
    if not quote_stop_structure_confirmed and math.isfinite(underlying_stop_for_quote) and math.isfinite(latest_3m_close):
        newer_bar = True
        if armed_bar and latest_3m_bar:
            try:
                newer_bar = pd.Timestamp(latest_3m_bar) > pd.Timestamp(armed_bar)
            except Exception:
                newer_bar = True
        quote_stop_structure_confirmed = newer_bar and (
            (direction_for_quote == "BULLISH" and latest_3m_close <= underlying_stop_for_quote)
            or (direction_for_quote == "BEARISH" and latest_3m_close >= underlying_stop_for_quote)
        )

    # T1 is a milestone, not a full exit. Once reached, the stop ratchets to
    # cost and then trails until T2 or a protective stop is reached.
    if intrabar_outcome == "STOP_LOSS":
        outcome = "STOP_LOSS"
        exit_ltp = float(intrabar_exit_reference or stop)
    elif intrabar_outcome == "TARGET_2":
        outcome = "TARGET_2"
        exit_ltp = float(intrabar_exit_reference or target2)
    elif ltp >= target2:
        outcome = "TARGET_2"
        exit_ltp = ltp
    elif ltp <= stop and quote_stop_structure_confirmed:
        outcome = "STOP_LOSS"
        exit_ltp = ltp
    else:
        outcome = ""
        exit_ltp = ltp

    if outcome:
        closed = dict(trade)
        closed.update(
            {
                "status": "CLOSED",
                "outcome": outcome,
                "exit_ltp": round(exit_ltp, 2),
                "closed_at": now_ist().isoformat(),
                "exit_reason": intrabar_reason if intrabar_outcome else "QUOTE_LTP",
                "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            }
        )
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"NIFTY TRADE {outcome} - {trade['trading_symbol']}",
            (
                f"<p>{html.escape(str(trade['direction']))} trade closed.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry:.2f}<br>"
                f"Exit: ₹{exit_ltp:.2f}<br>"
                f"Outcome: {outcome}<br>"
                f"Reason: {html.escape(intrabar_reason if intrabar_outcome else 'live quote')}</p>"
            ),
        )
        return "CLOSED"

    # After T1, move the option stop to cost and then trail from the live
    # underlying Supertrend/ATR boundary. This ratchets risk only upward.
    if t1_hit:
        trade["t1_hit"] = True
        current_stop = safe_float(trade.get("stop_loss"), 0.0)
        if entry > current_stop:
            current_stop = entry
        trade["stop_loss"] = round(current_stop, 2)

        if tf_frames and 3 in tf_frames:
            try:
                atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 0.0), 1.0)
                st3 = safe_float(tf_frames[3]["supertrend"].iloc[-1], 0.0)
                snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
                spot_now = safe_float(snapshot.get("spot"), 0.0)
                base_spot = safe_float(trade.get("entry_underlying"), spot_now)
                direction = str(trade.get("direction", "")).upper()
                if spot_now > 0 and base_spot > 0 and st3 > 0:
                    recent_low = safe_float(tf_frames[3]["low"].tail(6).min(), spot_now)
                    recent_high = safe_float(tf_frames[3]["high"].tail(6).max(), spot_now)
                    if direction == "BULLISH":
                        structural_trail = max(
                            st3 - STRUCTURAL_STOP_BUFFER_ATR * atr3,
                            recent_low - STRUCTURAL_STOP_BUFFER_ATR * atr3,
                        )
                        trail_underlying = min(
                            structural_trail,
                            spot_now - TRAIL_MIN_DISTANCE_ATR * atr3,
                        )
                        previous_underlying_stop = safe_float(trade.get("underlying_stop"), -float("inf"))
                        trail_underlying = max(previous_underlying_stop, trail_underlying)
                    else:
                        structural_trail = min(
                            st3 + STRUCTURAL_STOP_BUFFER_ATR * atr3,
                            recent_high + STRUCTURAL_STOP_BUFFER_ATR * atr3,
                        )
                        trail_underlying = max(
                            structural_trail,
                            spot_now + TRAIL_MIN_DISTANCE_ATR * atr3,
                        )
                        previous_underlying_stop = safe_float(trade.get("underlying_stop"), float("inf"))
                        trail_underlying = min(previous_underlying_stop, trail_underlying)

                    old_underlying_stop = safe_float(trade.get("underlying_stop"), float("nan"))
                    trade["underlying_stop"] = round(trail_underlying, 2)
                    latest_bar = str(tf_frames[3]["timestamp"].iloc[-1])
                    if not math.isfinite(old_underlying_stop) or abs(trail_underlying - old_underlying_stop) >= 0.01:
                        # The new stop is armed only from this completed 3m bar onward;
                        # never use the same bar retroactively against a newly raised stop.
                        trade["underlying_stop_armed_bar"] = latest_bar
                    signed_move = trail_underlying - base_spot
                    # Do not tighten beyond the entry-side direction: for a
                    # long CE, trail must remain above entry underlying; for a
                    # long PE, it must remain below entry underlying.
                    signed_move = signed_move if (
                        (direction == "BULLISH" and signed_move > 0)
                        or (direction == "BEARISH" and signed_move < 0)
                    ) else 0.0
                    trail_option = project_option_premium_signed(
                        entry, signed_move, safe_float(trade.get("delta")), safe_float(trade.get("gamma"))
                    )
                    # A long option stop must remain below the current premium.
                    trail_option = min(trail_option, max(0.0, ltp - 0.01))
                    trade["stop_loss"] = round(max(safe_float(trade.get("stop_loss")), trail_option), 2)
            except (KeyError, IndexError, TypeError, ValueError) as exc:
                logger.info("Trailing-stop update skipped: %s", exc)

    if t1_hit and not bool(trade.get("t1_notified", False)):
        trade["t1_notified"] = True
        send_email(
            f"NIFTY T1 HIT - {trade['trading_symbol']}",
            (
                f"<p>T1 reached; trade remains active for T2.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry:.2f}<br>"
                f"Current: ₹{ltp:.2f}<br>"
                f"New protective SL: ₹{safe_float(trade.get('stop_loss')):.2f}</p>"
            ),
        )

    active_direction = str(trade.get("direction", "")).upper()
    last_opposite = int(trade.get("reversal_confirmations", 0) or 0)

    # Enforce the invalidation rule promised by the signal itself. The four-factor
    # engine remains the entry-direction authority; this check only protects an
    # already-open position when the confirmed continuous structure is lost.
    expected_phase = (
        "CONTINUOUS_BULLISH" if active_direction == "BULLISH"
        else "CONTINUOUS_BEARISH"
    )
    snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    spot_now = safe_float(snapshot.get("spot"), 0.0)
    vwap_now = safe_float(snapshot.get("vwap"), float("nan"))

    vwap_reclaimed_against_trade = False
    if spot_now > 0 and math.isfinite(vwap_now):
        vwap_reclaimed_against_trade = (
            active_direction == "BEARISH" and spot_now > vwap_now
        ) or (
            active_direction == "BULLISH" and spot_now < vwap_now
        )

    same_continuous_phase = structure.market_phase == expected_phase
    market_alignment_failure = not same_continuous_phase or vwap_reclaimed_against_trade

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
        structure.market_phase,
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
                    "four-factor continuous phase lost and/or NIFTY reclaimed VWAP"
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

    if (
        structure.direction in {"BULLISH", "BEARISH"}
        and structure.direction != active_direction
        and structure.confidence >= STRUCTURE_REVERSAL_CONFIDENCE
        and last_opposite >= REVERSAL_CONFIRMATIONS_REQUIRED
    ):
        closed = dict(trade)
        closed.update(
            {
                "status": "CLOSED",
                "outcome": "STRUCTURE_REVERSAL",
                "exit_ltp": round(ltp, 2),
                "closed_at": now_ist().isoformat(),
                "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            }
        )
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"NIFTY STRUCTURE REVERSAL - {trade['trading_symbol']}",
            (
                f"<p>Trade exited on confirmed opposite market structure.</p>"
                f"<p>Active={active_direction}; current={structure.direction}; "
                f"confidence={structure.confidence:.1f}%.</p>"
            ),
        )
        return "CLOSED"

    state["active_trade"] = trade
    save_state(state)

    logger.info(
        "ACTIVE TRADE: %s LTP=%.2f T1=%.2f T2=%.2f SL=%.2f "
        "market=%s reversal=%d/%d",
        trade["trading_symbol"],
        ltp,
        target1,
        target2,
        stop,
        structure.direction,
        last_opposite,
        REVERSAL_CONFIRMATIONS_REQUIRED,
    )
    return "ACTIVE"


# =============================================================================
# SCAN
# =============================================================================



def update_continuation_persistence(
    state: dict[str, Any],
    market_phase: str,
    latest_completed_3m_bar: Optional[Any] = None,
) -> tuple[bool, int]:
    """Track continuous-state confirmations on distinct completed 3m bars."""
    phase = str(market_phase or "").upper()
    if phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}:
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
    required = max(CONTINUATION_CONFIRMATIONS_REQUIRED, 1)
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


def _active_trade_intrabar_exit(
    trade: dict[str, Any],
    df_1m: Optional[pd.DataFrame],
    *,
    underlying_1m: Optional[pd.DataFrame] = None,
    underlying_3m: Optional[pd.DataFrame] = None,
) -> tuple[Optional[str], Optional[float], str]:
    """Return (outcome, exit_reference, reason) from post-entry 1m OHLC.

    Two protections are important here:

    1. Only candles after the actual option entry are eligible. A 1m candle can
       contain movement that occurred before the trade was opened.
    2. A structural stop on the option is confirmed by the NIFTY index. This
       prevents a later trailing option stop from being compared with an old
       option candle and prevents option-only IV/theta noise from overriding a
       still-valid NIFTY trend.

    For a single OHLC bar that touches both a protective stop and a target, the
    stop is treated as first for conservative, non-look-ahead accounting.
    """
    if df_1m is None or df_1m.empty:
        return None, None, "NO_1M_DATA"

    work = df_1m.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    for column in ("high", "low"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low"])
    if work.empty:
        return None, None, "INVALID_1M_DATA"

    stop = safe_float(trade.get("stop_loss"), float("nan"))
    target1 = safe_float(trade.get("target_1"), float("nan"))
    target2 = safe_float(trade.get("target_2"), float("nan"))
    direction = str(trade.get("direction", "")).upper()
    underlying_stop = safe_float(trade.get("underlying_stop"), float("nan"))

    underlying = None
    if underlying_1m is not None and not underlying_1m.empty:
        underlying = underlying_1m.copy().sort_values("timestamp")
        underlying["timestamp"] = pd.to_datetime(
            underlying["timestamp"], utc=True, errors="coerce"
        )
        for column in ("high", "low"):
            underlying[column] = pd.to_numeric(underlying[column], errors="coerce")
        underlying = underlying.dropna(subset=["timestamp", "high", "low"])

    for _, bar in work.tail(max(ACTIVE_TRADE_INTRABAR_LOOKBACK, 1)).iterrows():
        low = float(bar["low"])
        high = float(bar["high"])
        ts_value = pd.Timestamp(bar["timestamp"])
        ts = ts_value.isoformat()

        # Match the same underlying 1m candle. Exact timestamp matching is
        # preferable to nearest-neighbour matching because the stop is a
        # structural confirmation, not an approximate quote proxy.
        # Structural confirmation is based on completed 3m closes, not a single
        # 1m wick. This aligns the stop with the market structure and prevents
        # option IV/noise or a transient index spike from closing the trade.
        underlying_breach = False
        underlying_close = float("nan")
        underlying_3m_ts = ""
        if underlying_3m is not None and not underlying_3m.empty and math.isfinite(underlying_stop):
            u3 = underlying_3m.copy().sort_values("timestamp")
            u3["timestamp"] = pd.to_datetime(u3["timestamp"], utc=True, errors="coerce")
            u3["close"] = pd.to_numeric(u3["close"], errors="coerce")
            u3 = u3.dropna(subset=["timestamp", "close"])
            if not u3.empty:
                required = max(STRUCTURAL_STOP_CONFIRM_BARS, 1)
                recent = u3.tail(required)
                armed_raw = str(trade.get("underlying_stop_armed_bar") or "").strip()
                armed_ts = None
                if armed_raw:
                    try:
                        armed_ts = pd.Timestamp(armed_raw)
                        if armed_ts.tzinfo is None:
                            armed_ts = armed_ts.tz_localize("UTC")
                        else:
                            armed_ts = armed_ts.tz_convert("UTC")
                    except Exception:
                        armed_ts = None
                if armed_ts is not None:
                    recent = recent[recent["timestamp"] > armed_ts]
                if len(recent) >= required:
                    closes = recent["close"].to_numpy(dtype=float)
                    underlying_breach = (
                        bool(np.all(closes <= underlying_stop)) if direction == "BULLISH"
                        else bool(np.all(closes >= underlying_stop))
                    )
                    if underlying_breach:
                        underlying_close = float(closes[-1])
                        underlying_3m_ts = pd.Timestamp(recent["timestamp"].iloc[-1]).isoformat()

        if math.isfinite(stop) and low <= stop:
            if ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION:
                if underlying_breach:
                    return (
                        "STOP_LOSS",
                        stop,
                        f"OPTION_1M_LOW={low:.2f}@{ts}; "
                        f"NIFTY_3M_CLOSE_BREACH={underlying_close:.2f}@{underlying_3m_ts}; "
                        f"underlying_stop={underlying_stop:.2f}",
                    )
                # Do not let the option alone invalidate the trade. T1/target
                # checks below remain valid because they are favourable events.
            else:
                return "STOP_LOSS", stop, f"1M_LOW={low:.2f}@{ts}"

        if math.isfinite(target2) and high >= target2:
            return "TARGET_2", target2, f"1M_HIGH={high:.2f}@{ts}"
        if math.isfinite(target1) and high >= target1:
            # T1 is handled as a milestone below; do not fully close here.
            return "T1_HIT", target1, f"1M_HIGH={high:.2f}@{ts}"

    if ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION:
        return None, None, "NO_INTRABAR_EXIT_OR_NIFTY_STRUCTURE_STOP_NOT_BREACHED"
    return None, None, "NO_INTRABAR_EXIT"


def execute_scan(
    state: Optional[dict[str, Any]] = None,
) -> Optional[Signal]:
    if not market_window_open():
        logger.info("Outside NSE market hours.")
        return None

    status = get_market_status()
    logger.info("NSE status=%s", status)
    if status != "OPEN":
        return None

    state = state if isinstance(state, dict) else {}
    today_iso = now_ist().date().isoformat()

    # State is intraday state. Never carry a prior session's direction or reversal
    # counter into a new trading day, and never carry v9's stale reversal labels
    # into v10. Active trades are preserved here and are cleaned by the existing
    # session-date monitor before a new trade can be opened.
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
    index_session = get_current_session_futures_candles(NIFTY_KEY)
    index_live_quote = get_quote(NIFTY_KEY)
    spot = extract_ltp(index_live_quote)

    # -------------------------------------------------------------------------
    # DERIVATIVES FEED = NIFTY FUTURES PRICE/OI
    # -------------------------------------------------------------------------
    futures_session = get_current_session_futures_candles(future.instrument_key)
    futures_live_quote = get_quote(future.instrument_key)
    futures_ltp_now = extract_ltp(futures_live_quote)

    logger.info(
        "UNDERLYING PRICES: index_spot=%.2f futures_ltp=%.2f basis=%+.2f",
        spot, futures_ltp_now, futures_ltp_now - spot,
    )

    # If the current index feed is late, use the current-session slice from the
    # regular V3 timeframe path; only then fall back to a live quote proxy.
    if index_session.empty:
        try:
            index_history = get_timeframe_candles(NIFTY_KEY, 3, min_bars=25)
            local_dates = index_history["timestamp"].dt.tz_convert(IST).dt.date
            index_session = index_history.loc[local_dates == now_ist().date()].copy()
        except ScannerError as exc:
            logger.warning("Index 3m session fallback unavailable: %s", exc)

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

    # Historical futures bars are only for OI warm-up; historical index bars are
    # only used if the live current-session index feed is too short.
    try:
        historical_futures = get_historical_candles(
            future.instrument_key, 3, lookback_days=10
        )
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

    # Multi-timeframe structures are already computed from the NIFTY index.
    tf_frames, tf_directions = timeframe_snapshot(NIFTY_KEY, base_3m=index_session)
    expiry, chain = get_option_chain(state)
    daily_oi_bias, daily_oi_score = get_daily_oi_confirmation(expiry)
    change_oi_bias, change_oi_score, change_oi_by_strike = get_change_oi_confirmation(expiry)
    pcr_value, pcr_rate_15m, pcr_trend, pcr_higher_low, pcr_lower_high = get_intraday_pcr(expiry)
    vwap_seed, _, _ = vwap_snapshot(index_session)
    atr_seed = max(safe_float(tf_frames[3]["atr"].iloc[-1], 50.0), 1.0)
    previous_snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    previous_option_snapshot = state.get("option_oi_snapshot") if isinstance(state.get("option_oi_snapshot"), dict) else {}
    chain_levels = chain_oi_support_resistance(
        chain,
        spot,
        change_oi_by_strike,
        price_session=index_session,
        vwap=vwap_seed,
        atr3=atr_seed,
        previous_option_snapshot=previous_option_snapshot,
        expiry=expiry,
        previous_support=safe_float(previous_snapshot.get("support_1"), float("nan")),
        previous_resistance=safe_float(previous_snapshot.get("resistance_1"), float("nan")),
    )
    chain_levels["pcr_trend"] = pcr_trend
    chain_levels["previous_support_1"] = safe_float(previous_snapshot.get("support_1"), float("nan"))
    chain_levels["previous_resistance_1"] = safe_float(previous_snapshot.get("resistance_1"), float("nan"))
    previous_direction = str(previous_snapshot.get("direction", "")).upper() or None
    persistent_direction = str(
        state.get("persistent_direction")
        or previous_snapshot.get("persistent_direction", "")
    ).upper() or None
    previous_phase = str(previous_snapshot.get("market_phase", "")).upper() or None
    previous_reversal_confirmations = int(previous_snapshot.get("reversal_confirmations", 0) or 0)

    # Provisional index direction for history reconstruction.
    provisional_intraday_bias, _, provisional_intraday_score = intraday_trend_snapshot(
        index_session, vwap_seed
    )
    provisional_current_direction = (
        "BULLISH" if provisional_intraday_score >= CORE_BULL_TRIGGER
        else "BEARISH" if provisional_intraday_score <= CORE_BEAR_TRIGGER
        else persistent_direction or previous_direction or "NEUTRAL"
    )

    inferred_prior_direction, transition_hint = infer_prior_session_direction(
        index_session, provisional_current_direction
    )

    # Do not let an older price window override a decisive current-day state.
    # This was the main source of the production log's repeated
    # BULLISH_TO_BEARISH_REVERSAL_CONFIRMED state while the market was already
    # continuously bearish.
    if (
        previous_direction in {"BULLISH", "BEARISH"}
        and provisional_current_direction == previous_direction
    ):
        inferred_prior_direction = None
        transition_hint = "NO_CONFIRMED_TRANSITION"

    seed_direction = persistent_direction or previous_direction
    if inferred_prior_direction and transition_hint in {
        "BEARISH_TO_BULLISH", "BULLISH_TO_BEARISH"
    } and previous_direction != provisional_current_direction:
        seed_direction = inferred_prior_direction
    elif not seed_direction and inferred_prior_direction:
        seed_direction = inferred_prior_direction

    structure = build_market_structure(
        spot=spot,
        futures_3m=futures_3m,
        futures_session=futures_session,
        tf_frames=tf_frames,
        tf_directions=tf_directions,
        chain_levels=chain_levels,
        daily_oi_bias=daily_oi_bias,
        daily_oi_score=daily_oi_score,
        change_oi_bias=change_oi_bias,
        change_oi_score=change_oi_score,
        futures_live_quote=futures_live_quote,
        previous_direction=seed_direction,
        previous_phase=previous_phase,
        previous_reversal_confirmations=previous_reversal_confirmations,
        price_session=index_session,
        inferred_prior_direction=inferred_prior_direction,
        transition_hint=transition_hint,
        pcr_value=pcr_value,
        pcr_rate_15m=pcr_rate_15m,
        pcr_higher_low=pcr_higher_low,
        pcr_lower_high=pcr_lower_high,
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
        "inferred_prior_direction": inferred_prior_direction or "",
        "transition_hint": transition_hint,
        "score": round(structure.score, 3),
        "confidence": round(structure.confidence, 2),
        "market_phase": structure.market_phase,
        "entry_confirmed": structure.entry_confirmed,
        "reversal_confirmations": structure.reversal_confirmations,
        "confirmation_state": structure.confirmation_state,
        "pcr": structure.pcr if math.isfinite(structure.pcr) else None,
        "pcr_bias": structure.pcr_bias,
        "pcr_rate_15m": round(structure.pcr_rate_15m, 4),
        "pcr_higher_low": structure.pcr_higher_low,
        "pcr_lower_high": structure.pcr_lower_high,
        "false_breakout": structure.false_breakout,
        "trap_level": structure.trap_level,
        "entry_trigger": structure.entry_trigger,
        "invalidation_rule": structure.invalidation_rule,
        "support_1": structure.support_1,
        "support_2": structure.support_2,
        "resistance_1": structure.resistance_1,
        "resistance_2": structure.resistance_2,
        "timeframes": structure.timeframe_directions,
        "latest_completed_3m_bar": (
            str(filter_completed_candles(index_session, 3)["timestamp"].iloc[-1])
            if not filter_completed_candles(index_session, 3).empty else ""
        ),
        "components": structure.components,
    }
    state["option_oi_snapshot"] = build_option_oi_snapshot(chain, expiry)
    state["persistent_direction"] = (
        structure.direction if structure.direction in {"BULLISH", "BEARISH"}
        else (seed_direction or "")
    ) or None
    save_state(state)

    logger.info(
        "REVERSAL CONTEXT: persisted=%s inferred_prior=%s hint=%s immediate_previous=%s",
        state.get("persistent_direction") or "NONE",
        inferred_prior_direction or "NONE",
        transition_hint,
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
        migrated = migrate_active_trade_targets(active_trade)
        if migrated:
            state["active_trade"] = active_trade
            save_state(state)
        monitor_active_trade(state, structure, tf_frames)
        return None

    # Defensive duplicate guard: the same direction/strike/session signal should
    # never email twice merely because state persistence was delayed.
    last_hash = str(state.get("last_signal_hash", ""))
    last_signal = state.get("last_signal")
    if isinstance(last_signal, dict):
        same_day = str(last_signal.get("timestamp", ""))[:10] == today_iso
        if same_day and last_hash:
            logger.info("DUPLICATE SIGNAL GUARD: prior signal exists for this session; waiting for a new trade state.")
            # Do not block after a completed trade; the re-entry gate below decides when a new setup is valid.

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

    completed_session_bars = len(filter_completed_candles(index_session, 3))
    if REENTRY_REQUIRE_NEW_3M_BAR:
        last_exit_bar = str(last_completed.get("exit_3m_bar", "")) if isinstance(last_completed, dict) else ""
        current_completed_bar = (
            str(filter_completed_candles(index_session, 3)["timestamp"].iloc[-1])
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

    if structure.direction == "NEUTRAL":
        logger.info(
            "No entry: market structure is neutral/mixed; phase=%s.",
            structure.market_phase,
        )
        return None

    allowed_matrix_states = {
        "CONTINUOUS_BULLISH",
        "CONTINUOUS_BEARISH",
    }
    matrix_state = (
        structure.market_phase[:-10]
        if structure.market_phase.endswith("_CONFIRMED")
        else structure.market_phase
    )
    if matrix_state not in allowed_matrix_states:
        logger.info(
            "No entry: scenario matrix state not confirmed: %s",
            structure.market_phase,
        )
        return None

    if not structure.entry_confirmed:
        logger.info(
            "No entry: confirmation/tactical gate failed. direction=%s phase=%s state=%s reversal=%d/%d PCR_bias=%+d",
            structure.direction,
            structure.market_phase,
            structure.confirmation_state,
            structure.reversal_confirmations,
            REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED,
            structure.pcr_bias,
        )
        return None

    if structure.confidence < SIGNAL_THRESHOLD:
        logger.info(
            "No entry: confidence %.1f < %.1f",
            structure.confidence,
            SIGNAL_THRESHOLD,
        )
        return None

    atr3_val = max(safe_float(tf_frames[3]["atr"].iloc[-1], 50.0), 1.0)
    continuous_state = structure.market_phase in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}
    persistence_count = 0
    # These values are needed in the final Signal/reason text on every path.
    timing_state = "STRUCTURAL_CONTINUATION" if continuous_state else "STRUCTURAL_WATCH"
    vwap_distance_atr = abs(float(spot) - float(structure.vwap)) / atr3_val
    latest_3m_move_atr = abs(float(structure.components.get("recent3_movement_atr", 0.0)))
    movement_factor = float(structure.components.get("price_session_atr", 0.0))

    # Reversal path: preserve the fresh-entry filter because the reversal impulse
    # itself is the trigger.
    if structure.market_phase in {
        "BEARISH_TO_BULLISH_REVERSAL",
        "BULLISH_TO_BEARISH_REVERSAL",
    }:
        state["continuation_phase"] = ""
        state["continuation_count"] = 0
        state["continuation_last_bar"] = ""
        timing_ok, timing_state, vwap_distance_atr, latest_3m_move_atr = entry_timing_filter(
            price_session=index_session,
            direction=structure.direction,
            vwap=structure.vwap,
            atr3=atr3_val,
            market_phase=structure.market_phase,
        )
        logger.info(
            "ENTRY TIMING: reversal state=%s vwap_distance=%.2f ATR latest_3m_move=%.2f ATR",
            timing_state,
            vwap_distance_atr,
            latest_3m_move_atr,
        )
        if not timing_ok:
            logger.info(
                "No entry: reversal timing filter rejected setup: %s.", timing_state
            )
            return None
        option_require_momentum = False

    elif continuous_state:
        completed_for_confirmation = filter_completed_candles(index_session, 3)
        latest_completed_bar = (
            completed_for_confirmation["timestamp"].iloc[-1]
            if not completed_for_confirmation.empty
            else None
        )
        persistence_ok, persistence_count = update_continuation_persistence(
            state,
            structure.market_phase,
            latest_completed_3m_bar=latest_completed_bar,
        )
        logger.info(
            "STRUCTURAL ENTRY CHECK: phase=%s persistence=%d/%d support=%.2f resistance=%.2f "
            "ChangeOI=%+.3f VWAP=%.2f; recent 3m movement is context only.",
            structure.market_phase,
            persistence_count,
            max(CONTINUATION_CONFIRMATIONS_REQUIRED, 1),
            structure.support_1,
            structure.resistance_1,
            structure.components.get("structure_change_oi", 0.0),
            structure.vwap,
        )
        if not persistence_ok:
            logger.info(
                "No entry: structural persistence requires %d confirmation(s); got %d.",
                max(CONTINUATION_CONFIRMATIONS_REQUIRED, 1),
                persistence_count,
            )
            save_state(state)
            return None
        timing_state = "STRUCTURAL_CONTINUATION"
        option_require_momentum = False

    else:
        state["continuation_phase"] = ""
        state["continuation_count"] = 0
        state["continuation_last_bar"] = ""
        timing_ok, timing_state, vwap_distance_atr, latest_3m_move_atr = entry_timing_filter(
            price_session=index_session,
            direction=structure.direction,
            vwap=structure.vwap,
            atr3=atr3_val,
            market_phase=structure.market_phase,
        )
        logger.info(
            "ENTRY TIMING: state=%s vwap_distance=%.2f ATR latest_3m_move=%.2f ATR",
            timing_state,
            vwap_distance_atr,
            latest_3m_move_atr,
        )
        if not timing_ok or not structure.entry_confirmed:
            logger.info(
                "No entry: non-confirmed/mixed market state or timing rejection: state=%s confirmed=%s timing=%s.",
                structure.market_phase,
                structure.entry_confirmed,
                timing_state,
            )
            return None
        option_require_momentum = False

    option = select_directional_option(
        chain=chain,
        direction=structure.direction,
        spot=spot,
        market_phase=structure.market_phase,
        require_option_momentum=False,
    )
    validate_continuous_option_entry(
        option=option,
        chain=chain,
        direction=structure.direction,
        market_phase=structure.market_phase,
        spot=spot,
    )
    target1, target2, stop_loss, underlying_stop, underlying_target1, underlying_target2 = create_dynamic_targets(
        option=option,
        structure=structure,
        spot=spot,
        tf_frames=tf_frames,
    )

    setup_label = (
        "TACTICAL REVERSAL ENTRY"
        if structure.market_phase in {"BEARISH_TO_BULLISH_REVERSAL", "BULLISH_TO_BEARISH_REVERSAL"}
        else "STRUCTURAL CONTINUATION ENTRY"
    )
    reasons = list(structure.reasons)
    reasons.extend([
        f"Setup type: {setup_label}.",
        f"Entry timing: {timing_state}; index VWAP distance={vwap_distance_atr:.2f} ATR; latest 3m move={latest_3m_move_atr:.2f} ATR; completed index 3m bars={completed_session_bars}.",
        f"Strike rule: {'ATM-1/ATM-2 CE' if structure.direction == 'BULLISH' else 'ATM+1/ATM+2 PE'}.",
        f"Index spot used for option ATM selection={spot:.2f}; futures LTP={futures_ltp_now:.2f}; futures/index basis={futures_ltp_now - spot:+.2f}.",
        f"Selected option health: spread={option.spread_pct:.2%}, theta burden={option.theta_burden_pct_day:.2%}/day, volume={option.volume:.0f}, OI={option.oi:.0f}, delta={option.delta:.3f}.",
        f"Dynamic underlying targets: T1={underlying_target1:.2f}, T2={underlying_target2:.2f}, SL={underlying_stop:.2f}.",
        f"Dynamic option targets: T1=₹{target1:.2f}, T2=₹{target2:.2f}, SL=₹{stop_loss:.2f}.",
        "Primary entry alignment: NIFTY price vs VWAP + structural support/resistance + confirming Change-OI.",
        "Futures price/OI, PCR and higher-timeframe Supertrend are confirmation/context only; they do not override a confirmed structural breakout or breakdown.",
    ])

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
        direction=structure.direction,
        regime=structure.interpretation,
        market_state=(structure.market_phase[:-10] if structure.market_phase.endswith("_CONFIRMED") else structure.market_phase),
        bias="Bullish" if structure.direction == "BULLISH" else "Bearish" if structure.direction == "BEARISH" else "Neutral",
        entry_trigger=structure.entry_trigger,
        invalidation_rule=structure.invalidation_rule,
        confidence=structure.confidence,
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
        gamma=option.gamma,
        theta=option.theta,
        support_1=structure.support_1,
        support_2=structure.support_2,
        resistance_1=structure.resistance_1,
        resistance_2=structure.resistance_2,
        reasons=reasons,
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
        changes[float(k)] = {"call_change": call_change if k >= spot else 0.0,
                             "put_change": put_change if k <= spot else 0.0}
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
    """Deterministic regression suite for the final Oct-8 structure engine."""
    down = _synthetic_candles([120, 118, 116, 114, 112, 109, 106, 103, 100, 98, 96, 94])
    up = _synthetic_candles([94, 96, 98, 100, 103, 106, 109, 112, 114, 116, 118, 120])
    st_down = calculate_supertrend(down, SUPERTREND_PERIOD, 3.0)
    st_up = calculate_supertrend(up, SUPERTREND_PERIOD, 3.0)
    assert int(st_down["direction"].iloc[-1]) == -1
    assert int(st_up["direction"].iloc[-1]) == 1

    # Futures price/OI classification remains correct.
    fut_bear = _synthetic_candles(
        [100, 99.5, 99, 98.5, 98, 97.5, 97, 96.5, 96],
        [1000, 1020, 1045, 1070, 1100, 1130, 1160, 1190, 1220],
    )
    regime, bias, price_delta, oi_delta = futures_price_oi_regime(fut_bear)
    assert regime == "SHORT_BUILDUP"
    assert bias == -1 and price_delta < 0 and oi_delta > 0

    # Build a deterministic chain with real OI walls and directional flow.
    chain, changes = _synthetic_structure_chain(
        spot=102.0,
        support=100.0,
        resistance=110.0,
        put_change=2_000_000.0,
        call_change=3_000_000.0,
    )
    level_session = _synthetic_candles([106, 105, 104, 103, 102])
    levels = chain_oi_support_resistance(
        chain, 102.0, changes,
        price_session=level_session, vwap=105.0, atr3=4.0,
        expiry="2026-10-13",
    )
    assert levels["support_1"] < 102.0
    assert levels["resistance_1"] > 102.0
    assert levels["support_1"] != levels["resistance_1"]
    assert levels["flow_mode"] == "DAY_CHANGE_API_WARMUP"

    frames_bear = {tf: st_down.copy() for tf in TIMEFRAMES}
    tf_bear = {tf: -1 for tf in TIMEFRAMES}
    bearish_levels = {
        "support_1": 100.0, "support_2": 95.0,
        "resistance_1": 110.0, "resistance_2": 115.0,
        "change_flow_score": -0.70, "change_flow_bias": -1,
        "predictive_bias": -1, "predictive_strength": 0.70,
        "support_strength": 0.70, "resistance_strength": 0.60,
        "support_change_strength": 0.60, "resistance_change_strength": 0.70,
        "pcr": 0.70,
    }
    # Range-bound price action must remain neutral even when derivatives carry a
    # bearish background signal; derivatives cannot manufacture direction from
    # an otherwise sideways NIFTY price structure.
    watch_session = _synthetic_candles([120.0, 121.0, 122.0, 121.0, 122.0, 121.0, 122.0, 121.0])
    watch_levels = dict(bearish_levels)
    watch_levels.update({"support_1": 100.0, "support_2": 95.0, "resistance_1": 130.0, "resistance_2": 135.0})
    watch = build_market_structure(
        121.0, fut_bear, fut_bear, frames_bear, tf_bear, watch_levels,
        -1, -0.10, -1, -0.30, pcr_value=0.70, price_session=watch_session,
    )
    assert watch.direction == "BEARISH"
    assert watch.market_phase == "BEARISH"
    assert not watch.entry_confirmed

    # V17-style case: the market has moved down materially over the session,
    # remains below VWAP with bearish Change-OI, but the latest 3 bars bounce
    # upward. That bounce must not cancel the continuous bearish regime.
    v17_pullback = _synthetic_candles([121, 118, 115, 112, 109, 106, 108, 111])
    v17_levels = dict(bearish_levels)
    v17_levels.update({
        "support_1": 105.0, "support_2": 100.0,
        "resistance_1": 125.0, "resistance_2": 130.0,
        "flow_mode": "INTRADAY_SNAPSHOT",
        "change_flow_score": -0.70,
        "change_flow_bias": -1,
    })
    v17_result = build_market_structure(
        111.0, fut_bear, fut_bear, frames_bear, tf_bear, v17_levels,
        -1, -0.10, -1, -0.40, previous_direction="BEARISH",
        previous_phase="CONTINUOUS_BEARISH", price_session=v17_pullback,
    )
    assert v17_result.direction == "BEARISH"
    assert v17_result.market_phase == "CONTINUOUS_BEARISH"
    assert v17_result.entry_confirmed
    assert v17_result.support_1 == 105.0

    # V17/V18 regression: a strong bearish session can have a short-term HH/HL
    # bounce while still remaining continuously bearish below VWAP with bearish flow.
    v17_long_bounce = _synthetic_candles([120, 118, 116, 114, 112, 110, 108, 106, 104, 102, 105, 107])
    v17b_levels = dict(bearish_levels)
    v17b_levels.update({
        "support_1": 100.0, "support_2": 95.0,
        "resistance_1": 125.0, "resistance_2": 130.0,
        "flow_mode": "INTRADAY_SNAPSHOT",
        "change_flow_score": -0.70, "change_flow_bias": -1,
    })
    v17b = build_market_structure(
        107.0, fut_bear, fut_bear, frames_bear, tf_bear, v17b_levels,
        -1, -0.10, -1, -0.40, previous_direction="BEARISH",
        previous_phase="BEARISH", price_session=v17_long_bounce,
    )
    assert v17b.direction == "BEARISH"
    assert v17b.market_phase == "CONTINUOUS_BEARISH"
    assert v17b.entry_confirmed

    # OI structure regression: price swings cannot replace an available OI wall.
    oi_chain, oi_changes = _synthetic_structure_chain(
        spot=102.0, support=100.0, resistance=110.0,
        put_change=-900000.0, call_change=1200000.0,
    )
    oi_session = _synthetic_candles([107, 105, 103, 102, 101])
    oi_levels = chain_oi_support_resistance(
        oi_chain, 102.0, oi_changes,
        price_session=oi_session, vwap=105.0, atr3=4.0, expiry="2026-10-13",
    )
    assert oi_levels["support_source"] in {"OPTION_OI", "PERSISTED_OPTION_OI"}
    assert oi_levels["resistance_source"] in {"OPTION_OI", "PERSISTED_OPTION_OI"}
    assert oi_levels["support_1"] == 100.0
    assert oi_levels["resistance_1"] == 110.0
    assert oi_levels["support_1"] < 102.0 < oi_levels["resistance_1"]

    # Clean structural breakdown: two completed closes below support + bearish Change-OI.
    down_break = _synthetic_candles([104, 103, 102, 101, 100.5, 99.0, 97.5, 96.5])
    breakdown = build_market_structure(
        96.5, fut_bear, fut_bear, frames_bear, tf_bear, bearish_levels,
        -1, -0.10, -1, -0.30, pcr_value=0.70, price_session=down_break,
    )
    assert breakdown.direction == "BEARISH"
    assert breakdown.market_phase == "CONTINUOUS_BEARISH"
    assert breakdown.entry_confirmed
    assert breakdown.support_1 == 100.0

    # A small countertrend bounce below the broken support cannot erase the bearish regime.
    pullback = _synthetic_candles([104, 102, 100, 98, 96, 97, 96.5])
    pullback_levels = dict(bearish_levels)
    pullback_levels["previous_support_1"] = 100.0
    pullback_levels["flow_mode"] = "INTRADAY_SNAPSHOT"
    pullback_result = build_market_structure(
        96.5, fut_bear, fut_bear, frames_bear, tf_bear, pullback_levels,
        -1, -0.10, -1, -0.30, previous_direction="BEARISH",
        previous_phase="CONTINUOUS_BEARISH", price_session=pullback,
    )
    assert pullback_result.market_phase == "CONTINUOUS_BEARISH"
    assert pullback_result.entry_confirmed
    assert pullback_result.support_1 == 100.0

    # Continuous bearish trend may remain valid even while price is above support
    # when the broader completed-bar/session movement remains bearish and the
    # latest 3m move is only a small pullback.
    above_support_pullback = _synthetic_candles([120, 118, 116, 114, 111, 109, 110, 112])
    above_support_levels = dict(bearish_levels)
    above_support_levels.update({
        "support_1": 105.0, "support_2": 100.0,
        "resistance_1": 125.0, "resistance_2": 130.0,
        "flow_mode": "INTRADAY_SNAPSHOT",
    })
    trend_pullback = build_market_structure(
        112.0, fut_bear, fut_bear, frames_bear, tf_bear, above_support_levels,
        -1, -0.10, -1, -0.35, previous_direction="BEARISH",
        previous_phase="CONTINUOUS_BEARISH", price_session=above_support_pullback,
    )
    assert trend_pullback.direction == "BEARISH"
    assert trend_pullback.market_phase == "CONTINUOUS_BEARISH"
    assert trend_pullback.entry_confirmed
    assert trend_pullback.support_1 == 105.0

    # Clean structural breakout: two completed closes above resistance + bullish Change-OI.
    fut_bull = _synthetic_candles(
        [100, 100.5, 101, 101.5, 102, 102.5, 103, 103.5, 104],
        [1200, 1215, 1230, 1245, 1260, 1275, 1290, 1305, 1320],
    )
    frames_bull = {tf: st_up.copy() for tf in TIMEFRAMES}
    tf_bull = {tf: 1 for tf in TIMEFRAMES}
    bullish_levels = {
        "support_1": 90.0, "support_2": 85.0,
        "resistance_1": 100.0, "resistance_2": 105.0,
        "change_flow_score": 0.70, "change_flow_bias": 1,
        "predictive_bias": 1, "predictive_strength": 0.70,
        "support_strength": 0.60, "resistance_strength": 0.70,
        "support_change_strength": 0.60, "resistance_change_strength": 0.70,
        "pcr": 1.25,
    }
    up_break = _synthetic_candles([96, 97, 98, 99, 100.5, 102, 104, 105, 106])
    breakout = build_market_structure(
        106.0, fut_bull, fut_bull, frames_bull, tf_bull, bullish_levels,
        1, 0.10, 1, 0.30, pcr_value=1.25, price_session=up_break,
    )
    assert breakout.direction == "BULLISH"
    assert breakout.market_phase == "CONTINUOUS_BULLISH"
    assert breakout.entry_confirmed
    assert breakout.resistance_1 == 100.0

    # Exact V16 bug regression: support and resistance can never collapse to the same level.
    v16_like = dict(bearish_levels)
    v16_like.update({"support_1": 22421.25, "resistance_1": 22450.0})
    v16_session = _synthetic_candles([22480, 22465, 22455, 22450, 22447, 22446, 22445])
    v16_result = build_market_structure(
        22446.5, fut_bear, fut_bear, frames_bear, tf_bear, v16_like,
        -1, -0.10, -1, -0.43, pcr_value=0.71, price_session=v16_session,
    )
    assert v16_result.support_1 == 22421.25
    assert v16_result.resistance_1 == 22450.0
    assert v16_result.support_1 < 22446.5 < v16_result.resistance_1
    assert not v16_result.entry_confirmed
    assert v16_result.market_phase == "BEARISH"

    # Option flow interpretation: rising long PE premium confirms bearish direction.
    activity, activity_bias = classify_option_flow("PE", 0.05, 100000.0)
    assert activity == "PUT_BUYING" and activity_bias == -1
    activity, activity_bias = classify_option_flow("CE", -0.05, 100000.0)
    assert activity == "CALL_WRITING" and activity_bias == -1

    # Directional strike rule remains hard enforced.
    simple_chain = []
    for strike in [74000, 74050, 74100, 74150, 74200]:
        simple_chain.append({
            "strike_price": strike,
            "expiry": "2026-10-13",
            "call_options": {
                "instrument_key": f"CE{strike}",
                "market_data": {
                    "ltp": 100.0, "oi": 50000, "prev_oi": 49000, "volume": 10000,
                    "bid_price": 99.5, "ask_price": 100.5, "bid_qty": 100, "ask_qty": 100,
                },
                "option_greeks": {"delta": 0.55, "gamma": 0.01, "theta": -2.0, "iv": 20.0},
            },
            "put_options": {
                "instrument_key": f"PE{strike}",
                "market_data": {
                    "ltp": 100.0, "oi": 50000, "prev_oi": 49000, "volume": 10000,
                    "bid_price": 99.5, "ask_price": 100.5, "bid_qty": 100, "ask_qty": 100,
                },
                "option_greeks": {"delta": -0.55, "gamma": 0.01, "theta": -2.0, "iv": 20.0},
            },
        })
    ce = select_directional_option(simple_chain, "BULLISH", 74100.0)
    pe = select_directional_option(simple_chain, "BEARISH", 74100.0)
    assert ce.option_type == "CE" and ce.strike in {74000.0, 74050.0}
    assert pe.option_type == "PE" and pe.strike in {74150.0, 74200.0}

    # V19 regression: neutral intraday snapshot must fall back to strongly
    # directional current-session API Change-OI rather than becoming SIDEWAYS.
    neutral_intraday_levels = dict(bearish_levels)
    neutral_intraday_levels.update({
        "flow_mode": "INTRADAY_SNAPSHOT",
        "change_flow_score": 0.0,
        "change_flow_bias": 0,
    })
    neutral_intraday_result = build_market_structure(
        102.0, fut_bear, fut_bear, frames_bear, tf_bear, neutral_intraday_levels,
        -1, -0.10, -1, -0.65, price_session=_synthetic_candles([120, 118, 116, 114, 112, 110, 108, 107, 106, 105]),
    )
    assert neutral_intraday_result.direction == "BEARISH"
    assert neutral_intraday_result.market_phase == "CONTINUOUS_BEARISH"
    assert neutral_intraday_result.entry_confirmed
    assert neutral_intraday_result.components["structure_change_oi"] < -0.20

    # Exact Oct-8 V19 regression: intraday flow snapshot is neutral but the
    # current-session API Change-OI is strongly bearish. The scanner must fall
    # back to the API reading and must not call this market SIDEWAYS when price
    # is materially below VWAP with sustained bearish movement.
    oct8_levels = dict(bearish_levels)
    oct8_levels.update({
        "support_1": 22000.0, "support_2": 21950.0,
        "resistance_1": 22600.0, "resistance_2": 22650.0,
        "flow_mode": "INTRADAY_SNAPSHOT",
        "change_flow_score": 0.0,
        "change_flow_bias": 0,
    })
    oct8_result = build_market_structure(
        102.0, fut_bear, fut_bear, frames_bear, tf_bear, oct8_levels,
        -1, -0.10, -1, -0.65,
        price_session=_synthetic_candles([120, 118, 116, 114, 112, 110, 108, 107, 106, 105]),
    )
    assert oct8_result.direction == "BEARISH"
    assert oct8_result.market_phase == "CONTINUOUS_BEARISH"
    assert oct8_result.entry_confirmed
    assert oct8_result.components["structure_change_oi_source"] == "DAY_CHANGE_API_FALLBACK_NEUTRAL_INTRADAY"

    # V21 regression: target projection must not explode from the quadratic
    # gamma term.  The capped projection must remain close to the delta-based
    # estimate even for a large underlying move.
    target_option = OptionCandidate(
        instrument_key="TEST_PE_22300", trading_symbol="TESTPE", option_type="PE",
        strike=22300.0, expiry="2026-10-13", ltp=192.65, oi=5000000.0,
        prev_oi=4900000.0, volume=1000000.0, bid=192.4, ask=192.9,
        bid_qty=1000.0, ask_qty=1000.0, delta=-0.60, gamma=0.01,
        theta=-8.0, iv=20.0, spread_pct=0.0026, theta_burden_pct_day=0.04,
    )
    target_frames = {
        3: pd.DataFrame({
            "atr": [40.0], "supertrend": [22400.0],
            "high": [22380.0], "low": [22300.0],
        }),
        15: pd.DataFrame({
            "atr": [55.0], "supertrend": [22450.0],
            "high": [22460.0], "low": [22300.0],
        }),
    }
    target_structure = type("TargetStructure", (), {
        "direction": "BEARISH", "support_1": 22200.0, "support_2": 22000.0,
        "resistance_1": 22500.0, "resistance_2": 22600.0, "vwap": 22450.0,
    })()
    t1, t2, sl, _, u1, u2 = create_dynamic_targets(
        target_option, target_structure, 22316.25, target_frames
    )
    assert 192.65 < t1 < t2
    assert t1 < 330.0, (t1, t2)
    assert t2 < 430.0, (t1, t2)
    naive_move_t2 = abs(22316.25 - u2)
    naive_t2 = 192.65 + (0.60 * naive_move_t2) + (0.5 * 0.01 * naive_move_t2 * naive_move_t2)
    assert t2 < naive_t2

    # Strong intraday/day conflict must never authorize a directional Change-OI
    # entry by itself; price can retain only a directional WATCH state.
    conflict_levels = dict(bearish_levels)
    conflict_levels.update({
        "flow_mode": "INTRADAY_SNAPSHOT",
        "change_flow_score": 0.90,
        "change_flow_bias": 1,
    })
    conflict_result = build_market_structure(
        102.0, fut_bear, fut_bear, frames_bear, tf_bear, conflict_levels,
        -1, -0.10, -1, -0.65, price_session=_synthetic_candles([120, 118, 116, 114, 112, 110, 108, 107, 106, 105]),
    )
    assert conflict_result.direction == "BEARISH"
    assert conflict_result.market_phase == "BEARISH"
    assert not conflict_result.entry_confirmed

    # V22 regression: a legacy active trade must be migrated exactly once using
    # its stored entry/underlying levels and the V21 target engine.
    legacy_trade = {
        "status": "ACTIVE",
        "trading_symbol": "NIFTY25OCT22500PE",
        "direction": "BEARISH",
        "entry": 192.65,
        "entry_underlying": 22316.25,
        "underlying_target_1": 22200.0,
        "underlying_target_2": 22000.0,
        "underlying_stop": 22400.0,
        "delta": -0.60,
        "gamma": 0.01,
        "target_1": 261.76,
        "target_2": 423.71,
        "stop_loss": 143.06,
        "t1_hit": False,
    }
    assert migrate_active_trade_targets(legacy_trade)
    assert legacy_trade["target_engine_version"] == OPTION_TARGET_ENGINE_VERSION
    assert legacy_trade["target_1"] < 300.0
    assert legacy_trade["target_2"] < 410.0
    migrated_values = (legacy_trade["target_1"], legacy_trade["target_2"], legacy_trade["stop_loss"])
    assert not migrate_active_trade_targets(legacy_trade)
    assert migrated_values == (legacy_trade["target_1"], legacy_trade["target_2"], legacy_trade["stop_loss"])

    logger.info("SELF-TEST PASSED.")


# =============================================================================
# MAIN
# =============================================================================

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
            "confidence": signal.confidence,
            "instrument_key": signal.instrument_key,
            "trading_symbol": signal.trading_symbol,
            "option_type": signal.option_type,
            "strike": signal.strike,
            "entry": signal.entry,
            "entry_underlying": signal.spot,
            "t1_hit": False,
            "target_1": signal.target_1,
            "target_2": signal.target_2,
            "stop_loss": signal.stop_loss,
            "underlying_stop": signal.underlying_stop,
            "underlying_target_1": signal.underlying_target_1,
            "underlying_target_2": signal.underlying_target_2,
            "delta": signal.delta,
            "gamma": signal.gamma,
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
            "NEW SIGNAL LOCKED: %s | entry=%.2f T1=%.2f T2=%.2f SL=%.2f",
            signal.trading_symbol,
            signal.entry,
            signal.target_1,
            signal.target_2,
            signal.stop_loss,
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
