#!/usr/bin/env python3
"""NIFTY 50 multi-timeframe predictive intraday scanner with persistent position management v109.0.0.

Single-file runtime for an intraday workflow. Entry timing is based on completed
1-minute and 3-minute structure, while 15-minute structure supplies market context. It never places orders. Tests and documentation are separate files.

Design contract:
- signed OI changes are computed only between consecutive successful,
  same-session, same-expiry, identity-matched option-chain snapshots;
- one-minute candles are price observations, never a source of fabricated OI;
- a historical setup must pass a current-price/fresh-quote revalidation;
- initial T1/T2 are local, realistic and fixed at entry; they are not repeatedly reassessed;
- spot risk/reward is validated against local structure; option premium RR is not used;
- state is written atomically before notification is attempted;
- failures produce explicit reason codes and never silently reuse stale data.
- the persistent market thesis changes only on structural invalidation; short-term opposite momentum is treated as a pullback while defended structure survives.
- after T1, the runner is managed as a separate profit-protection state with structural/OI stop ratcheting and option-premium/theta safeguards.
"""
from __future__ import annotations

import argparse
import gzip
import html
import hashlib
import json
import logging
import math
import os
import random
import shutil
import smtplib
import ssl
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from datetime import date, datetime, time as dtime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from statistics import median
from typing import Any, Mapping, Optional, Sequence
from zoneinfo import ZoneInfo

VERSION = "111.0.0"
SCHEMA_VERSION = 109
IST = ZoneInfo("Asia/Kolkata")
UTC = timezone.utc
API_BASE = "https://api.upstox.com"
INSTRUMENTS_URL = "https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz"
LOG = logging.getLogger("nifty_scanner")

# Operational failures must make the GitHub Actions step fail. Market-quality
# blocks (for example low RR, weak setup, intact countertrend support) remain
# fail-closed NO_TRADE decisions but are not process failures.
OPERATIONAL_FAILURE_CODES = frozenset({
    # Code/config/state integrity.
    "UNEXPECTED_ERROR",
    "CONFIG_INVALID",
    "CONFIG_TOKEN_MISSING",
    "TIMEZONE_INVALID",
    "STATE_SAVE_FAILED",
    "STATE_READ_FAILED",
    "STATE_BACKUP_FAILED",
    "STATE_TOO_LARGE",
    "STATE_SCHEMA_UNSUPPORTED",
    "STATE_COLLECTION_INVALID",
    # Provider/network/data plumbing failures after built-in retries.
    "API_AUTH_FAILED",
    "API_PERMISSION_DENIED",
    "API_HTTP_ERROR",
    "API_HTTP_403",
    "API_HTTP_401",
    "API_NETWORK_ERROR",
    "API_RATE_LIMIT",
    "API_SERVER_ERROR",
    "API_REQUEST_FAILED",
    "API_INVALID_JSON",
    "API_INVALID_RESPONSE",
    "API_PROVIDER_ERROR",
    "INSTRUMENT_MASTER_INVALID",
    "INSTRUMENT_MASTER_UNAVAILABLE",
    "EXPIRY_NOT_FOUND",
    "WEEKLY_EXPIRY_NOT_FOUND",
    "CANDLE_DATA_MISSING",
    "CANDLES_STALE",
    "MARKET_QUOTES_INVALID",
    "MARKET_QUOTES_LIMIT",
    "QUOTE_TIMESTAMP_INVALID",
    "SPOT_QUOTE_INVALID",
    "SPOT_QUOTE_MISSING",
    "SPOT_QUOTE_STALE",
    "SPOT_QUOTE_TIMESTAMP_MISSING",
    # Position/state invariants must fail closed.
    "POSITION_CANDLE_GAP",
    "POSITION_SESSION_EXPIRED",
    "POSITION_SESSION_MISMATCH",
    "POSITION_RECONCILIATION_REQUIRED",
    "ACTIVE_POSITION_EXPIRY_MISMATCH",
    "ACTIVE_POSITION_STATE_INVALID",
    "ACTIVE_POSITION_INVALID",
    "DIRECTION_INVALID",
    "STRIKE_GRID_INVALID",
    "TARGET_GRID_INVALID",
})


def is_operational_failure(code: Any) -> bool:
    return str(code or "") in OPERATIONAL_FAILURE_CODES


# ---------- Configuration and errors ----------

class ScannerError(RuntimeError):
    def __init__(self, code: str, message: str, *, retryable: bool = False):
        super().__init__(message)
        self.code = code
        self.retryable = retryable


@dataclass(frozen=True)
class Config:
    token: str
    state_file: Path = Path("state/market_state_v109.json")
    audit_dir: Path = Path("audit")
    instrument_cache: Path = Path(".cache/upstox_nse.json.gz")
    explicit_expiry: Optional[date] = None
    request_timeout: float = 12.0
    max_retries: int = 2
    instrument_cache_hours: int = 12

    # Data quality / freshness.
    oi_material_threshold_pct: float = 2.0
    max_oi_age_seconds: int = 720
    expected_oi_interval_seconds: int = 180
    max_quote_age_seconds: int = 30
    max_candle_age_seconds: int = 150

    # Entry architecture: 1m trigger + 3m confirmation + 15m context.
    # Opening discovery deliberately becomes usable before a mature 15m trend
    # exists; 15m is context, never a warm-up gate.
    direction_entry_score_min: float = 0.44
    opening_entry_score_min: float = 0.52
    opening_strong_price_override_score: float = 0.70
    direction_reversal_score_min: float = 0.52
    min_1m_execution_confidence: float = 0.42
    min_3m_execution_confidence: float = 0.46
    opening_min_1m_bars: int = 6
    opening_min_3m_bars: int = 2
    opening_warmup_minutes: int = 6
    min_entry_minutes_to_close: float = 20.0
    max_entry_extension_atr: float = 0.80
    setup_max_age_minutes: int = 8
    setup_state_ttl_minutes: int = 8
    pivot_left: int = 2
    pivot_right: int = 2

    # Persistent market-thesis / structure invalidation.  A short-term momentum
    # flip is a pullback until a defended support/resistance zone actually fails.
    thesis_break_buffer_atr: float = 0.25
    thesis_test_zone_atr: float = 0.45
    thesis_min_level_strength: float = 1.80
    thesis_oi_support_score_min: float = 0.45
    thesis_oi_break_score_min: float = 0.55

    # Local NIFTY risk/target design.  Trend trades use meaningful 50-point
    # landmarks rather than tiny micro-swings as profit objectives.
    min_underlying_rr: float = 1.25
    minimum_stop_points: float = 6.0
    min_initial_stop_atr: float = 0.75
    max_initial_stop_points: float = 30.0
    max_stop_atr: float = 2.25
    stop_buffer_atr_fraction: float = 0.10
    target_grid_points: float = 50.0
    target1_min_points: float = 12.0
    target1_max_points: float = 65.0
    target2_max_points: float = 115.0
    trend_target_min_points: float = 25.0
    trend_target1_max_points: float = 85.0
    trend_target2_max_points: float = 135.0
    level_cluster_atr_fraction: float = 0.12
    min_level_strength: float = 1.0
    t1_partial_exit_pct: float = 50.0

    # Regime-aware strike selection. Reversal/sideways rules are explicit.
    trend_strike_offsets_ce: tuple[int, ...] = (0, -1)
    trend_strike_offsets_pe: tuple[int, ...] = (0, 1)
    reversal_sideways_offsets_ce: tuple[int, ...] = (-1, -2)
    reversal_sideways_offsets_pe: tuple[int, ...] = (1, 2)
    min_abs_delta: float = 0.30
    max_abs_delta: float = 0.85
    preferred_abs_delta: float = 0.58
    max_spread_pct: float = 3.0
    min_bid_qty: float = 1.0
    min_ask_qty: float = 1.0
    min_option_volume: float = 1.0
    expected_hold_minutes: float = 12.0

    # Position management. Before T1 we protect the structural thesis; after T1
    # we protect profit with a dedicated runner state so theta cannot silently
    # consume a winning option while NIFTY chops around support/resistance.
    max_premium_loss_pct: float = 18.0
    premium_trailing_drawdown_pct: float = 22.0  # legacy fallback / hard cap
    premium_decay_review_minutes: float = 8.0
    premium_decay_min_loss_pct: float = 10.0
    no_progress_min_spot_move_atr: float = 0.30
    sideways_exit_minutes: float = 6.0
    sideways_max_progress_atr: float = 0.40
    sideways_consensus_abs_max: float = 0.22
    pre_t1_trail_min_progress_atr: float = 0.75
    post_t1_base_peak_drawdown_pct: float = 13.0
    post_t1_expiry_afternoon_drawdown_pct: float = 9.0
    post_t1_min_no_progress_bars: int = 2
    post_t1_supportive_oi_extra_bars: int = 1
    post_t1_min_progress_atr: float = 0.25
    post_t1_theta_fraction_limit: float = 0.04

    # Retained compatibility knobs used by diagnostics / legacy helpers.
    min_oi_direction_confidence: float = 0.52
    min_oi_score_margin: float = 0.12
    min_mixed_price_confirmation: float = 0.65

    email_sender: str = ""
    email_receiver: str = ""
    email_password: str = ""
    email_username: str = ""
    smtp_host: str = "smtp.gmail.com"
    smtp_port: int = 465
    debug_audit: bool = False

    def __post_init__(self) -> None:
        if not self.token or not self.token.strip():
            raise ScannerError("CONFIG_TOKEN_MISSING", "Set UPSTOX_ANALYTICS_TOKEN in GitHub Secrets.")
        positive = {
            "request_timeout": self.request_timeout,
            "oi_material_threshold_pct": self.oi_material_threshold_pct,
            "min_underlying_rr": self.min_underlying_rr,
            "max_oi_age_seconds": self.max_oi_age_seconds,
            "expected_oi_interval_seconds": self.expected_oi_interval_seconds,
            "max_quote_age_seconds": self.max_quote_age_seconds,
            "max_candle_age_seconds": self.max_candle_age_seconds,
            "max_spread_pct": self.max_spread_pct,
            "max_entry_extension_atr": self.max_entry_extension_atr,
            "setup_max_age_minutes": self.setup_max_age_minutes,
            "setup_state_ttl_minutes": self.setup_state_ttl_minutes,
            "expected_hold_minutes": self.expected_hold_minutes,
            "minimum_stop_points": self.minimum_stop_points,
            "max_initial_stop_points": self.max_initial_stop_points,
            "target_grid_points": self.target_grid_points,
            "target1_min_points": self.target1_min_points,
            "target1_max_points": self.target1_max_points,
            "target2_max_points": self.target2_max_points,
            "trend_target_min_points": self.trend_target_min_points,
            "trend_target1_max_points": self.trend_target1_max_points,
            "trend_target2_max_points": self.trend_target2_max_points,
            "thesis_break_buffer_atr": self.thesis_break_buffer_atr,
            "thesis_test_zone_atr": self.thesis_test_zone_atr,
            "thesis_min_level_strength": self.thesis_min_level_strength,
            "premium_decay_review_minutes": self.premium_decay_review_minutes,
            "pre_t1_trail_min_progress_atr": self.pre_t1_trail_min_progress_atr,
            "post_t1_base_peak_drawdown_pct": self.post_t1_base_peak_drawdown_pct,
            "post_t1_expiry_afternoon_drawdown_pct": self.post_t1_expiry_afternoon_drawdown_pct,
            "post_t1_min_progress_atr": self.post_t1_min_progress_atr,
            "post_t1_theta_fraction_limit": self.post_t1_theta_fraction_limit,
        }
        for name, value in positive.items():
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite number greater than zero")
        if self.min_underlying_rr < 1.0:
            raise ScannerError("CONFIG_INVALID", "MIN_UNDERLYING_RR must be at least 1.0")
        if self.target1_max_points <= self.target1_min_points:
            raise ScannerError("CONFIG_INVALID", "TARGET1_MAX_POINTS must exceed TARGET1_MIN_POINTS")
        if self.target2_max_points <= self.target1_max_points:
            raise ScannerError("CONFIG_INVALID", "TARGET2_MAX_POINTS must exceed TARGET1_MAX_POINTS")
        if self.trend_target1_max_points <= self.trend_target_min_points:
            raise ScannerError("CONFIG_INVALID", "TREND_TARGET1_MAX_POINTS must exceed TREND_TARGET_MIN_POINTS")
        if self.trend_target2_max_points <= self.trend_target1_max_points:
            raise ScannerError("CONFIG_INVALID", "TREND_TARGET2_MAX_POINTS must exceed TREND_TARGET1_MAX_POINTS")
        if self.min_abs_delta < 0 or self.max_abs_delta > 1 or self.min_abs_delta >= self.max_abs_delta:
            raise ScannerError("CONFIG_INVALID", "Delta limits must satisfy 0 <= min_abs_delta < max_abs_delta <= 1")
        if not self.min_abs_delta <= self.preferred_abs_delta <= self.max_abs_delta:
            raise ScannerError("CONFIG_INVALID", "preferred_abs_delta must lie within the configured delta range")
        if self.max_retries < 0 or self.max_retries > 5:
            raise ScannerError("CONFIG_INVALID", "max_retries must be between 0 and 5")
        if self.setup_state_ttl_minutes < self.setup_max_age_minutes:
            raise ScannerError("CONFIG_INVALID", "setup_state_ttl_minutes must be at least setup_max_age_minutes")
        if self.smtp_port not in {465, 587}:
            raise ScannerError("CONFIG_INVALID", "SMTP_PORT must be 465 (SSL) or 587 (STARTTLS)")
        for name, value in {
            "direction_entry_score_min": self.direction_entry_score_min,
            "opening_entry_score_min": self.opening_entry_score_min,
            "opening_strong_price_override_score": self.opening_strong_price_override_score,
            "direction_reversal_score_min": self.direction_reversal_score_min,
            "min_1m_execution_confidence": self.min_1m_execution_confidence,
            "min_3m_execution_confidence": self.min_3m_execution_confidence,
            "sideways_consensus_abs_max": self.sideways_consensus_abs_max,
            "thesis_oi_support_score_min": self.thesis_oi_support_score_min,
            "thesis_oi_break_score_min": self.thesis_oi_break_score_min,
            "post_t1_theta_fraction_limit": self.post_t1_theta_fraction_limit,
        }.items():
            if not math.isfinite(float(value)) or not 0.0 <= float(value) <= 1.0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be between 0 and 1")
        if self.direction_reversal_score_min < self.direction_entry_score_min:
            raise ScannerError("CONFIG_INVALID", "direction_reversal_score_min must be >= direction_entry_score_min")
        if self.opening_entry_score_min < self.direction_entry_score_min:
            raise ScannerError("CONFIG_INVALID", "opening_entry_score_min must be >= direction_entry_score_min")
        if self.opening_strong_price_override_score < self.opening_entry_score_min:
            raise ScannerError("CONFIG_INVALID", "opening_strong_price_override_score must be >= opening_entry_score_min")
        if self.post_t1_min_no_progress_bars < 1 or self.post_t1_supportive_oi_extra_bars < 0:
            raise ScannerError("CONFIG_INVALID", "post-T1 runner bar counts are invalid")
        if self.opening_min_1m_bars < 4 or self.opening_min_3m_bars < 2:
            raise ScannerError("CONFIG_INVALID", "opening discovery requires at least 4 one-minute bars and 2 three-minute bars")
        if self.opening_warmup_minutes < 3:
            raise ScannerError("CONFIG_INVALID", "opening_warmup_minutes must be at least 3")
        if not math.isfinite(float(self.min_entry_minutes_to_close)) or self.min_entry_minutes_to_close < 0:
            raise ScannerError("CONFIG_INVALID", "min_entry_minutes_to_close must be finite and nonnegative")
        for name, value in {
            "t1_partial_exit_pct": self.t1_partial_exit_pct,
            "max_premium_loss_pct": self.max_premium_loss_pct,
            "premium_trailing_drawdown_pct": self.premium_trailing_drawdown_pct,
            "premium_decay_min_loss_pct": self.premium_decay_min_loss_pct,
            "post_t1_base_peak_drawdown_pct": self.post_t1_base_peak_drawdown_pct,
            "post_t1_expiry_afternoon_drawdown_pct": self.post_t1_expiry_afternoon_drawdown_pct,
        }.items():
            if not math.isfinite(float(value)) or not 0.0 <= float(value) <= 100.0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be between 0 and 100")
        if not 0.0 < self.t1_partial_exit_pct < 100.0:
            raise ScannerError("CONFIG_INVALID", "T1_PARTIAL_EXIT_PCT must be greater than 0 and less than 100")
        if self.post_t1_expiry_afternoon_drawdown_pct > self.post_t1_base_peak_drawdown_pct:
            raise ScannerError("CONFIG_INVALID", "POST_T1_EXPIRY_AFTERNOON_DRAWDOWN_PCT must not exceed POST_T1_BASE_PEAK_DRAWDOWN_PCT")

    @property
    def email_configured(self) -> bool:
        return all((self.smtp_host, self.email_sender, self.email_receiver, self.email_password))

    @classmethod
    def from_env(cls) -> "Config":
        token = os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip() or os.getenv("UPSTOX_ACCESS_TOKEN", "").strip()
        if not token:
            raise ScannerError("CONFIG_TOKEN_MISSING", "Set UPSTOX_ANALYTICS_TOKEN in GitHub Secrets.")

        def int_env(name: str, default: int) -> int:
            try:
                value = int(os.getenv(name, str(default)))
                if value < 0:
                    raise ValueError
                return value
            except ValueError as exc:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a nonnegative integer") from exc

        def float_env(name: str, default: float) -> float:
            try:
                value = float(os.getenv(name, str(default)))
                if not math.isfinite(value) or value < 0:
                    raise ValueError
                return value
            except ValueError as exc:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite nonnegative number") from exc

        def bool_env(name: str, default: bool = False) -> bool:
            raw = os.getenv(name)
            if raw is None or not raw.strip():
                return default
            normalized = raw.strip().lower()
            if normalized in {"1", "true", "yes", "on"}:
                return True
            if normalized in {"0", "false", "no", "off"}:
                return False
            raise ScannerError("CONFIG_INVALID", f"{name} must be one of true/false, 1/0, yes/no, or on/off")

        expiry_raw = os.getenv("OPTION_EXPIRY", "").strip()
        try:
            expiry = date.fromisoformat(expiry_raw) if expiry_raw else None
        except ValueError as exc:
            raise ScannerError("CONFIG_INVALID", "OPTION_EXPIRY must be YYYY-MM-DD") from exc

        return cls(
            token=token,
            state_file=Path(os.getenv("STATE_FILE", "state/market_state_v109.json")),
            audit_dir=Path(os.getenv("AUDIT_DIR", "audit")),
            instrument_cache=Path(os.getenv("INSTRUMENT_CACHE_FILE", ".cache/upstox_nse.json.gz")),
            explicit_expiry=expiry,
            request_timeout=float_env("REQUEST_TIMEOUT_SECONDS", 12.0),
            max_retries=int_env("API_MAX_RETRIES", 2),
            instrument_cache_hours=int_env("INSTRUMENT_CACHE_HOURS", 12),
            oi_material_threshold_pct=float_env("OI_MATERIAL_THRESHOLD_PCT", 2.0) or 2.0,
            max_oi_age_seconds=int_env("MAX_OI_AGE_SECONDS", 720),
            expected_oi_interval_seconds=max(30, int_env("EXPECTED_OI_INTERVAL_SECONDS", 180)),
            max_quote_age_seconds=int_env("MAX_QUOTE_AGE_SECONDS", 30),
            max_candle_age_seconds=int_env("MAX_CANDLE_AGE_SECONDS", 150),
            direction_entry_score_min=float_env("DIRECTION_ENTRY_SCORE_MIN", 0.44),
            opening_entry_score_min=float_env("OPENING_ENTRY_SCORE_MIN", 0.52),
            opening_strong_price_override_score=float_env("OPENING_STRONG_PRICE_OVERRIDE_SCORE", 0.70),
            direction_reversal_score_min=float_env("DIRECTION_REVERSAL_SCORE_MIN", 0.52),
            min_1m_execution_confidence=float_env("MIN_1M_EXECUTION_CONFIDENCE", 0.42),
            min_3m_execution_confidence=float_env("MIN_3M_EXECUTION_CONFIDENCE", 0.46),
            opening_min_1m_bars=max(4, int_env("OPENING_MIN_1M_BARS", 6)),
            opening_min_3m_bars=max(2, int_env("OPENING_MIN_3M_BARS", 2)),
            opening_warmup_minutes=max(3, int_env("OPENING_WARMUP_MINUTES", 6)),
            min_entry_minutes_to_close=float_env("MIN_ENTRY_MINUTES_TO_CLOSE", 20.0),
            max_entry_extension_atr=float_env("MAX_ENTRY_EXTENSION_ATR", 0.80),
            setup_max_age_minutes=int_env("SETUP_MAX_AGE_MINUTES", 8),
            setup_state_ttl_minutes=int_env("SETUP_STATE_TTL_MINUTES", 8),
            thesis_break_buffer_atr=float_env("THESIS_BREAK_BUFFER_ATR", 0.25),
            thesis_test_zone_atr=float_env("THESIS_TEST_ZONE_ATR", 0.45),
            thesis_min_level_strength=float_env("THESIS_MIN_LEVEL_STRENGTH", 1.80),
            thesis_oi_support_score_min=float_env("THESIS_OI_SUPPORT_SCORE_MIN", 0.45),
            thesis_oi_break_score_min=float_env("THESIS_OI_BREAK_SCORE_MIN", 0.55),
            min_underlying_rr=float_env("MIN_UNDERLYING_RR", 1.25) or 1.25,
            minimum_stop_points=float_env("MINIMUM_STOP_POINTS", 6.0),
            min_initial_stop_atr=float_env("MIN_INITIAL_STOP_ATR", 0.75),
            max_initial_stop_points=float_env("MAX_INITIAL_STOP_POINTS", 30.0),
            max_stop_atr=float_env("MAX_STOP_ATR", 2.25),
            stop_buffer_atr_fraction=float_env("STOP_BUFFER_ATR_FRACTION", 0.10),
            target_grid_points=float_env("TARGET_GRID_POINTS", 50.0),
            target1_min_points=float_env("TARGET1_MIN_POINTS", 12.0),
            target1_max_points=float_env("TARGET1_MAX_POINTS", 65.0),
            target2_max_points=float_env("TARGET2_MAX_POINTS", 115.0),
            trend_target_min_points=float_env("TREND_TARGET_MIN_POINTS", 25.0),
            trend_target1_max_points=float_env("TREND_TARGET1_MAX_POINTS", 85.0),
            trend_target2_max_points=float_env("TREND_TARGET2_MAX_POINTS", 135.0),
            preferred_abs_delta=float_env("PREFERRED_ABS_DELTA", 0.58),
            min_abs_delta=float_env("MIN_ABS_DELTA", 0.30),
            max_abs_delta=float_env("MAX_ABS_DELTA", 0.85),
            max_spread_pct=float_env("MAX_SPREAD_PCT", 3.0),
            min_bid_qty=float_env("MIN_BID_QTY", 1.0),
            min_ask_qty=float_env("MIN_ASK_QTY", 1.0),
            min_option_volume=float_env("MIN_OPTION_VOLUME", 1.0),
            expected_hold_minutes=float_env("EXPECTED_HOLD_MINUTES", 12.0),
            t1_partial_exit_pct=float_env("T1_PARTIAL_EXIT_PCT", 50.0),
            max_premium_loss_pct=float_env("MAX_PREMIUM_LOSS_PCT", 18.0),
            premium_trailing_drawdown_pct=float_env("PREMIUM_TRAILING_DRAWDOWN_PCT", 22.0),
            premium_decay_review_minutes=float_env("PREMIUM_DECAY_REVIEW_MINUTES", 8.0),
            premium_decay_min_loss_pct=float_env("PREMIUM_DECAY_MIN_LOSS_PCT", 10.0),
            no_progress_min_spot_move_atr=float_env("NO_PROGRESS_MIN_SPOT_MOVE_ATR", 0.30),
            sideways_exit_minutes=float_env("SIDEWAYS_EXIT_MINUTES", 6.0),
            sideways_max_progress_atr=float_env("SIDEWAYS_MAX_PROGRESS_ATR", 0.40),
            sideways_consensus_abs_max=float_env("SIDEWAYS_CONSENSUS_ABS_MAX", 0.22),
            pre_t1_trail_min_progress_atr=float_env("PRE_T1_TRAIL_MIN_PROGRESS_ATR", 0.75),
            post_t1_base_peak_drawdown_pct=float_env("POST_T1_BASE_PEAK_DRAWDOWN_PCT", 13.0),
            post_t1_expiry_afternoon_drawdown_pct=float_env("POST_T1_EXPIRY_AFTERNOON_DRAWDOWN_PCT", 9.0),
            post_t1_min_no_progress_bars=max(1, int_env("POST_T1_MIN_NO_PROGRESS_BARS", 2)),
            post_t1_supportive_oi_extra_bars=int_env("POST_T1_SUPPORTIVE_OI_EXTRA_BARS", 1),
            post_t1_min_progress_atr=float_env("POST_T1_MIN_PROGRESS_ATR", 0.25),
            post_t1_theta_fraction_limit=float_env("POST_T1_THETA_FRACTION_LIMIT", 0.04),
            email_sender=(os.getenv("EMAIL_SENDER", "").strip() or os.getenv("EMAIL_FROM", "").strip()),
            email_receiver=(os.getenv("EMAIL_RECEIVER", "").strip() or os.getenv("EMAIL_TO", "").strip()),
            email_password=os.getenv("EMAIL_PASSWORD", "").strip(),
            email_username=os.getenv("EMAIL_USERNAME", "").strip(),
            smtp_host=os.getenv("SMTP_HOST", "smtp.gmail.com").strip() or "smtp.gmail.com",
            smtp_port=int_env("SMTP_PORT", 465),
            debug_audit=bool_env("SCANNER_DEBUG_AUDIT", False),
        )


# ---------- Time, JSON and atomic state helpers ----------

def now_ist() -> datetime:
    return datetime.now(IST)


def parse_datetime(value: Any) -> Optional[datetime]:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        # Milliseconds are the convention in Upstox candle/quote timestamps.
        seconds = float(value) / (1000.0 if abs(float(value)) > 10**11 else 1.0)
        return datetime.fromtimestamp(seconds, tz=UTC).astimezone(IST)
    if not isinstance(value, str):
        return None
    try:
        dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if dt.tzinfo is None or dt.utcoffset() is None:
            return None
        return dt.astimezone(IST)
    except ValueError:
        return None


def parse_expiry(value: Any) -> Optional[date]:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        parsed = parse_datetime(value)
        return parsed.date() if parsed else None
    try:
        return date.fromisoformat(str(value)[:10])
    except ValueError:
        return None


def json_safe(value: Any) -> Any:
    if isinstance(value, datetime):
        return value.astimezone(IST).isoformat()
    if isinstance(value, date):
        return value.isoformat()
    if isinstance(value, Path):
        return str(value)
    if hasattr(value, "__dataclass_fields__"):
        return json_safe(asdict(value))
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [json_safe(v) for v in value]
    if isinstance(value, float) and not math.isfinite(value):
        return None
    return value


def _reject_non_finite(value: Any, path: str = "$") -> None:
    """Reject NaN/Infinity before persistence; silently converting them hides bugs."""
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError(f"Non-finite numeric value at {path}")
    if hasattr(value, "__dataclass_fields__"):
        _reject_non_finite(asdict(value), path)
    elif isinstance(value, Mapping):
        for key, child in value.items():
            _reject_non_finite(child, f"{path}.{key}")
    elif isinstance(value, (list, tuple, set)):
        for index, child in enumerate(value):
            _reject_non_finite(child, f"{path}[{index}]")


def atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    _reject_non_finite(payload)
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(json_safe(dict(payload)), separators=(",", ":"), sort_keys=True, allow_nan=False).encode("utf-8")
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except Exception:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        raise


def _migrate_state_payload(state: Mapping[str, Any], source: Path) -> dict[str, Any]:
    """Migrate compatible durable state into schema 109.

    Schema 108 is structurally compatible with v109 position identity and
    notification state, so open positions can continue to be managed. Older
    schemas retain the conservative reconciliation behavior used previously.
    """
    try:
        old_schema = int(state.get("schema_version", 0) or 0)
    except (TypeError, ValueError):
        old_schema = 0
    if old_schema not in {102, 103, 104, 105, 106, 107, 108}:
        raise ScannerError("STATE_SCHEMA_UNSUPPORTED", f"Cannot safely migrate schema {old_schema} from {source}")
    migrated = dict(state)
    migrated["schema_version"] = SCHEMA_VERSION
    migrated["scanner_version"] = VERSION
    migrated["migration_note"] = f"migrated_schema_{old_schema}_to_{SCHEMA_VERSION}"
    migrated.setdefault("position_history", [])
    migrated.setdefault("setup_watch", None)
    migrated.setdefault("position_entry_block_after", None)
    migrated.setdefault("last_position_exit", None)
    migrated.setdefault("last_position_event_key", None)
    migrated.setdefault("market_thesis", None)
    migrated.setdefault("thesis_history", [])
    active_for_migration = migrated.get("active_position")
    if old_schema == 108 and not isinstance(migrated.get("market_thesis"), Mapping) and isinstance(active_for_migration, Mapping) and active_for_migration.get("status") == "OPEN":
        active_direction = str(active_for_migration.get("direction") or "").upper()
        if active_direction in {"BULLISH", "BEARISH"}:
            migrated["market_thesis"] = {
                "direction": active_direction,
                "state": "BULL_TREND" if active_direction == "BULLISH" else "BEAR_TREND",
                "confidence": 0.55,
                "established_at": active_for_migration.get("opened_at"),
                "updated_at": active_for_migration.get("opened_at"),
                "anchor_support": None, "anchor_resistance": None,
                "break_confirmed": False, "broken_level": None,
                "reason": "BOOTSTRAPPED_FROM_OPEN_V108_POSITION",
            }
    if old_schema <= 106 and not isinstance(migrated.get("active_position"), Mapping):
        migrated["active_position"] = None
        migrated["position_reconciliation_required"] = True
        migrated["position_reconciliation_reason"] = "LEGACY_STATE_HAS_NO_ACTIVE_POSITION_RECORD"
    else:
        migrated.setdefault("position_reconciliation_required", False)
    snapshots = migrated.get("chain_snapshots")
    migrated["chain_snapshots"] = [x for x in snapshots if isinstance(x, Mapping)][-16:] if isinstance(snapshots, list) else []
    legacy_pending = migrated.get("pending_notifications")
    if old_schema <= 106 and isinstance(legacy_pending, list):
        migrated["pending_notifications"] = [
            {**dict(item), "status": "LEGACY_UNCERTAIN", "claim_token": None,
             "migration_note": "Not automatically resent; delivery may already have occurred"}
            for item in legacy_pending if isinstance(item, Mapping)
        ]
    allowed = {
        "schema_version", "scanner_version", "migration_note", "session_date", "expiry",
        "chain_snapshots", "session_oi_baseline", "last_successful_snapshot_at",
        "latest_oi_evidence", "oi_evidence_history", "last_processed_candle",
        "setup_watch", "seen_signal_keys", "pending_notifications",
        "delivered_signal_keys", "notification_history", "last_signal", "last_decision", "instrument_cache_version",
        "active_position", "position_history", "position_reconciliation_required", "position_reconciliation_reason",
        "last_position_exit", "last_position_event_key", "position_entry_block_after",
        "market_thesis", "thesis_history",
    }
    return {key: value for key, value in migrated.items() if key in allowed}


def read_state(path: Path) -> dict[str, Any]:
    """Load schema-109 state or safely migrate compatible historical state."""
    source = path if path.exists() else None
    if source is None:
        candidates = [
            path.parent / "market_state_v108.json",
            path.parent / "market_state_v107.json",
            path.parent / "market_state_v106.json",
            path.parent / "market_state_v105.json",
            path.parent / "market_state_v104.json",
            path.parent / "market_state_v103.json",
            path.parent / "market_state_v102.json",
        ]
        source = next((candidate for candidate in candidates if candidate.exists()), None)

    if source is None:
        return {"schema_version": SCHEMA_VERSION, "scanner_version": VERSION}

    try:
        raw = source.read_bytes()
        if len(raw) > 2_000_000:
            raise ScannerError("STATE_TOO_LARGE", f"State file exceeds 2 MB: {source}")
        state = json.loads(raw.decode("utf-8"))
        if not isinstance(state, dict):
            raise ValueError("state root is not an object")
        _reject_non_finite(state)
        schema_raw = state.get("schema_version")
        try:
            schema = int(schema_raw) if schema_raw is not None else None
        except (TypeError, ValueError):
            schema = None
        if schema == SCHEMA_VERSION:
            state["schema_version"] = SCHEMA_VERSION
            state["scanner_version"] = VERSION
            return state
        if schema in {102, 103, 104, 105, 106, 107, 108}:
            migrated = _migrate_state_payload(state, source)
            LOG.warning("Migrated durable state schema %s to %s from %s", schema, SCHEMA_VERSION, source)
            return migrated
        old_schema = str(schema if schema is not None else "unknown")
        backup = source.with_name(source.name + f".schema-{old_schema}.backup")
        if backup.exists():
            backup = source.with_name(source.name + f".schema-{old_schema}." + datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + ".backup")
        try:
            shutil.copy2(source, backup)
        except OSError as exc:
            raise ScannerError("STATE_BACKUP_FAILED", f"Cannot preserve incompatible state before reset: {exc}") from exc
        LOG.warning("State schema %r is incompatible with v%s; old state copied to %s; starting clean state.", old_schema, VERSION, backup)
        return {
            "schema_version": SCHEMA_VERSION,
            "scanner_version": VERSION,
            "migration_note": "incompatible_state_not_reused",
            "migration_backup": str(backup),
        }
    except ScannerError:
        raise
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ScannerError("STATE_READ_FAILED", f"Could not safely read state file: {exc}") from exc

def append_jsonl(path: Path, record: Mapping[str, Any]) -> None:
    _reject_non_finite(record)
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(json_safe(dict(record)), separators=(",", ":"), sort_keys=True, allow_nan=False) + "\n"
    with path.open("a", encoding="utf-8") as stream:
        stream.write(line)
        stream.flush()
        os.fsync(stream.fileno())

# Routine logs deliberately retain decision-critical information while omitting
# repeated strike-zone permutations and per-contract feature rows. Full evidence
# is written to a separate diagnostics JSONL only for exceptions, qualified
# signals, OI reversal watches, or explicitly enabled debug sessions.
def _picked_fields(value: Any, fields: Sequence[str]) -> Optional[dict[str, Any]]:
    if not isinstance(value, Mapping):
        return None
    return {key: value[key] for key in fields if key in value}


def compact_audit_record(record: Mapping[str, Any]) -> dict[str, Any]:
    """Return a bounded, decision-complete audit/CLI representation."""
    root_fields = (
        "scanner_version", "schema_version", "timestamp", "evaluation_timestamp",
        "session_date", "expiry", "underlying_key", "decision", "reason_code", "result_type",
        "error_type", "message", "spot", "oi_label", "oi_state", "oi_raw_label",
        "option_chain_status", "option_chain_error", "regime", "market_scenario", "setup_age_seconds",
        "setup_direction", "setup_kind", "signal_key", "notification_status",
        "notification_error", "candidate_offsets_allowed", "audit_persistence",
        "event_type", "position_id", "original_signal_key", "position_status",
        "remaining_pct", "t1_hit", "premium_bid", "exit_spot", "exit_reason",
        "position_event_details", "active_position_summary", "position_reconciliation_required",
        "direction_consensus", "shadow_option_selection", "entry_timing_status",
        "market_thesis", "oi_structure", "candle_freshness", "local_reversal_watch",
        "entry_gate_diagnostics", "position_exit", "early_oi_reversal", "v111_evidence",
    )
    compact = {key: record[key] for key in root_fields if key in record}

    oi = record.get("oi") if isinstance(record.get("oi"), Mapping) else {}
    oi_fields = (
        "label", "raw_label", "transition_status", "score", "directional_balance",
        "bull_score", "bear_score", "confidence", "score_margin",
        "snapshot_time", "snapshot_interval_seconds", "snapshot_status",
        "source_refresh_status", "source_refresh_error", "oi_age_seconds",
        "compared_to_previous_successful_snapshot", "contracts_compared",
        "contributing_contract_count", "material_contract_count", "persistence_count",
        "previous_directional_label", "oi_horizons", "multi_horizon_direction",
        "multi_horizon_balance", "multi_horizon_alignment", "multi_horizon_vote_count",
        "average_abs_delta_oi_pct", "average_abs_premium_change_pct",
        "aggregate_delta_call_oi_snapshot", "aggregate_delta_put_oi_snapshot",
        "aggregate_delta_call_oi_pct_snapshot", "aggregate_delta_put_oi_pct_snapshot",
        "aggregate_pe_minus_ce_delta_oi", "session_baseline_contracts_matched",
        "session_delta_call_oi_nearby", "session_delta_put_oi_nearby", "nearby_pcr",
        "oi_activity_factor", "premium_activity_factor", "breadth_factor", "interval_factor",
        "premium_mid_comparison_count", "premium_ltp_fallback_count",
        "premium_source_mismatch_count", "current_snapshot_delta_available",
    )
    oi_compact = _picked_fields(oi, oi_fields) or {}
    oi_compact.setdefault("label", record.get("oi_label", "MISSING"))
    oi_compact.setdefault("raw_label", record.get("oi_raw_label", oi_compact.get("label")))
    # Two largest walls per side are enough for the routine summary; the full
    # three-wall list and all eight positional/metric zones stay in diagnostics.
    for key in ("call_oi_walls", "put_oi_walls"):
        walls = oi.get(key, [])
        if isinstance(walls, list):
            oi_compact[key] = [
                _picked_fields(wall, ("strike", "oi", "relative_strength", "side"))
                for wall in walls[:2] if isinstance(wall, Mapping)
            ]
    compact["oi"] = oi_compact

    structure = _picked_fields(record.get("structure"), (
        "regime", "higher_timeframe_bias", "higher_timeframe_confidence",
        "higher_timeframe_status", "execution_direction", "execution_confidence",
        "execution_status", "execution_3m_direction", "execution_3m_confidence",
        "market_context_15m_bias", "market_context_15m_confidence", "market_context_15m_status",
        "reason", "atr_1m", "atr_3m", "atr_15m", "atr_5m", "efficiency_ratio", "efficiency_3m",
        "opening_minutes_elapsed", "ema_fast_1m",
        "momentum_3m_points", "completed_1m_contiguous_count", "completed_3m_contiguous_count",
        "completed_15m_contiguous_count", "completed_5m_contiguous_count", "duplicate_1m_candle_count",
        "duplicate_3m_candle_count", "duplicate_15m_candle_count", "duplicate_5m_candle_count",
        "ema8_1m", "ema5_3m", "ema9_3m", "ema3_15m", "ema5_15m",
        "market_thesis_state", "market_thesis_direction", "market_thesis_support", "market_thesis_resistance",
    ))
    if structure is not None:
        compact["structure"] = structure

    spot_context = _picked_fields(record.get("spot_context"), (
        "spot", "spot_quote_timestamp", "spot_quote_received_at", "spot_quote_age_seconds",
        "spot_quote_clock_skew_seconds", "spot_quote_timestamp_status",
        "latest_completed_candle_time", "latest_candle_close", "spot_minus_last_close_points",
    ))
    if spot_context is not None:
        compact["spot_context"] = spot_context

    levels = _picked_fields(record.get("levels"), (
        "nearest_resistance", "nearest_support", "resistance_count", "support_count",
    ))
    if levels is not None:
        compact["levels"] = levels

    futures = _picked_fields(record.get("futures"), (
        "instrument_key", "trading_symbol", "expiry", "price", "quote_timestamp",
        "quote_age_seconds", "quote_status", "basis_points", "basis_points_value",
        "vwap", "vwap_valid", "vwap_status", "latest_candle_age_seconds",
        "futures_oi_signal", "futures_oi_delta", "futures_oi_delta_pct", "futures_price_delta_points",
    ))
    if futures is not None:
        compact["futures"] = futures

    setup = _picked_fields(record.get("setup"), (
        "direction", "kind", "confirmed_at", "trigger", "invalidation",
        "source_level", "source", "price_confidence",
    ))
    if setup is not None:
        compact["setup"] = setup

    # Trade-qualified records retain the selected instrument and full spot risk plan.
    for key in ("risk_plan", "selected_contract"):
        value = record.get(key)
        if isinstance(value, Mapping):
            compact[key] = dict(value)
    return json_safe(compact)


def detailed_audit_triggers(record: Mapping[str, Any], debug_enabled: bool = False) -> list[str]:
    triggers: list[str] = []
    if debug_enabled:
        triggers.append("DEBUG_ENABLED")
    if record.get("decision") == "QUALIFIED":
        triggers.append("QUALIFIED_SIGNAL")
    if record.get("error_type") or is_operational_failure(record.get("reason_code")):
        triggers.append("SCANNER_ERROR")
    oi = record.get("oi") if isinstance(record.get("oi"), Mapping) else {}
    state = str(record.get("oi_state") or "")
    if oi.get("transition_status") == "REVERSAL_WATCH" or state.startswith("REVERSAL_WATCH"):
        triggers.append("OI_REVERSAL_WATCH")
    return list(dict.fromkeys(triggers))


def persist_audit_records(
    config: Config,
    session_date: date,
    record: Mapping[str, Any],
    *,
    oi_diagnostics: Optional[Mapping[str, Any]] = None,
) -> dict[str, str]:
    """Write compact routine audit and conditional detailed diagnostics.

    Audit failures are reported to the workflow log but never rewrite a
    completed trading decision or turn an already-delivered signal into NO_TRADE.
    """
    routine_path = config.audit_dir / f"market_scan_{session_date.isoformat()}.jsonl"
    result = {"routine": "FAILED", "diagnostics": "NOT_REQUIRED"}
    compact = compact_audit_record(record)
    try:
        append_jsonl(routine_path, compact)
        result["routine"] = "WRITTEN"
    except Exception as exc:
        LOG.error("Routine audit write failed (%s): %s", type(exc).__name__, routine_path)

    triggers = detailed_audit_triggers(record, config.debug_audit)
    if not triggers:
        return result

    detail_path = config.audit_dir / f"market_scan_diagnostics_{session_date.isoformat()}.jsonl"
    oi_full = dict(oi_diagnostics) if isinstance(oi_diagnostics, Mapping) else {}
    if not oi_full and isinstance(record.get("oi"), Mapping):
        oi_full = dict(record["oi"])
    oi_without_features = {key: value for key, value in oi_full.items() if key != "features"}
    diagnostic_record = {
        "diagnostic_schema_version": 1,
        "scanner_version": VERSION,
        "timestamp": record.get("timestamp"),
        "triggers": triggers,
        "decision_summary": compact_audit_record(record),
        "oi_diagnostics": json_safe(oi_without_features),
        "per_contract_features": json_safe(oi_full.get("features", [])),
    }
    try:
        append_jsonl(detail_path, diagnostic_record)
        result["diagnostics"] = "WRITTEN"
    except Exception as exc:
        result["diagnostics"] = "FAILED"
        LOG.error("Detailed diagnostics write failed (%s): %s", type(exc).__name__, detail_path)
    return result


def persisted_oi_evidence(oi: Mapping[str, Any]) -> dict[str, Any]:
    """Keep only fields needed to reuse the last OI context after refresh failure."""
    return {key: value for key, value in oi.items() if key not in {"features", "oi_zones_above_below_spot"}}


# ---------- HTTP client: bounded retry, no hidden auth behaviour ----------

class UpstoxClient:
    def __init__(self, token: str, timeout: float = 12.0, max_retries: int = 2, opener: Any = None):
        self.token = token
        self.timeout = timeout
        self.max_retries = max_retries
        self.opener = opener or urllib.request.urlopen

    def get_bytes(self, url: str, *, authenticated: bool = False) -> bytes:
        headers = {"Accept": "application/json", "User-Agent": f"NiftyMarketScanner/{VERSION}"}
        if authenticated:
            headers["Authorization"] = f"Bearer {self.token}"
        last_error: Optional[Exception] = None
        for attempt in range(self.max_retries + 1):
            request = urllib.request.Request(url, headers=headers, method="GET")
            try:
                with self.opener(request, timeout=self.timeout) as response:
                    status = getattr(response, "status", 200)
                    body = response.read()
                    if status >= 400:
                        raise ScannerError(f"API_HTTP_{status}", f"HTTP {status} from {urllib.parse.urlparse(url).path}")
                    return body
            except urllib.error.HTTPError as exc:
                body = ""
                try:
                    body = exc.read(600).decode("utf-8", errors="replace")
                except Exception:
                    pass
                if exc.code == 429 or 500 <= exc.code < 600:
                    last_error = ScannerError("API_RATE_LIMIT" if exc.code == 429 else "API_SERVER_ERROR", f"HTTP {exc.code} from {urllib.parse.urlparse(url).path}: {body[:240]}", retryable=True)
                    if attempt < self.max_retries:
                        retry_after = exc.headers.get("Retry-After", "") if exc.headers else ""
                        try:
                            delay = min(max(float(retry_after), 0.25), 3.0)
                        except (TypeError, ValueError):
                            delay = min(0.5 * (2 ** attempt) + random.random() * 0.2, 3.0)
                        time.sleep(delay)
                        continue
                    break
                if exc.code in (401, 403):
                    code = "API_AUTH_FAILED" if exc.code == 401 else "API_PERMISSION_DENIED"
                    raise ScannerError(code, f"HTTP {exc.code} from {urllib.parse.urlparse(url).path}: {body[:300]}") from exc
                raise ScannerError("API_HTTP_ERROR", f"HTTP {exc.code} from {urllib.parse.urlparse(url).path}: {body[:300]}") from exc
            except (urllib.error.URLError, TimeoutError, OSError) as exc:
                last_error = ScannerError("API_NETWORK_ERROR", f"Network error calling {urllib.parse.urlparse(url).path}: {exc}", retryable=True)
                if attempt < self.max_retries:
                    time.sleep(min(0.5 * (2 ** attempt) + random.random() * 0.2, 3.0))
                    continue
                break
        raise last_error or ScannerError("API_REQUEST_FAILED", "API request failed")

    def get_json(self, url: str) -> dict[str, Any]:
        raw = self.get_bytes(url, authenticated=True)
        try:
            data = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ScannerError("API_INVALID_JSON", f"Invalid JSON from {urllib.parse.urlparse(url).path}") from exc
        if not isinstance(data, dict):
            raise ScannerError("API_INVALID_RESPONSE", f"Expected JSON object from {urllib.parse.urlparse(url).path}")
        if data.get("status") == "error":
            errors = data.get("errors") or data.get("error") or "provider returned status=error"
            raise ScannerError("API_PROVIDER_ERROR", f"API provider error: {str(errors)[:300]}")
        return data


# ---------- Official instrument master ----------

class InstrumentMaster:
    def __init__(self, client: UpstoxClient, cache_path: Path, cache_hours: int = 12):
        self.client = client
        self.cache_path = cache_path
        self.cache_seconds = max(60, cache_hours * 3600)
        self.rows: list[dict[str, Any]] = []

    def load(self, now: datetime) -> list[dict[str, Any]]:
        cached_content: Optional[bytes] = None
        cache_is_fresh = False
        try:
            if self.cache_path.exists():
                cached_content = self.cache_path.read_bytes()
                cache_is_fresh = now.timestamp() - self.cache_path.stat().st_mtime <= self.cache_seconds
        except OSError:
            cached_content = None
            cache_is_fresh = False
        content: Optional[bytes] = cached_content if cache_is_fresh else None
        if content is None:
            try:
                downloaded = self.client.get_bytes(INSTRUMENTS_URL, authenticated=False)
            except ScannerError:
                # Use a stale cache only as a metadata fallback; expiry resolution
                # still validates the requested date and refuses a silent monthly roll.
                if cached_content is None:
                    raise
                LOG.warning("Official instrument master download failed; using stale cached metadata subject to expiry validation")
                content = cached_content
            else:
                try:
                    decompressed = gzip.decompress(downloaded)
                except (OSError, EOFError) as exc:
                    raise ScannerError("INSTRUMENT_MASTER_INVALID", "Official instrument master was not a valid gzip file") from exc
                parsed = self._decode_rows(decompressed)
                if len(parsed) < 100:
                    raise ScannerError("INSTRUMENT_MASTER_INVALID", "Official instrument master unexpectedly contains fewer than 100 rows")
                self.cache_path.parent.mkdir(parents=True, exist_ok=True)
                tmp_fd, tmp_name = tempfile.mkstemp(prefix=self.cache_path.name + ".", dir=str(self.cache_path.parent))
                try:
                    with os.fdopen(tmp_fd, "wb") as out:
                        out.write(downloaded)
                        out.flush()
                        os.fsync(out.fileno())
                    os.replace(tmp_name, self.cache_path)
                except Exception:
                    try:
                        os.unlink(tmp_name)
                    except OSError:
                        pass
                    raise
                self.rows = parsed
                return parsed
        if content is not None:
            try:
                decompressed = gzip.decompress(content)
            except (OSError, EOFError):
                raise ScannerError("INSTRUMENT_MASTER_INVALID", "Cached instrument master is corrupt")
            self.rows = self._decode_rows(decompressed)
            if len(self.rows) < 100:
                raise ScannerError("INSTRUMENT_MASTER_INVALID", "Cached instrument master is incomplete")
            return self.rows
        raise ScannerError("INSTRUMENT_MASTER_UNAVAILABLE", "No usable official instrument master")

    @staticmethod
    def _decode_rows(raw: bytes) -> list[dict[str, Any]]:
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ScannerError("INSTRUMENT_MASTER_INVALID", "Instrument master JSON is malformed") from exc
        rows = payload if isinstance(payload, list) else payload.get("data") if isinstance(payload, dict) else None
        if not isinstance(rows, list):
            raise ScannerError("INSTRUMENT_MASTER_INVALID", "Instrument master does not contain a list of instruments")
        return [item for item in rows if isinstance(item, dict)]

    def resolve_index(self) -> dict[str, Any]:
        """Resolve the NSE NIFTY 50 index by exact instrument-master identity.

        The previous implementation concatenated several display fields and
        searched for the substring ``nifty 50``. That also matched related
        indices (for example NIFTY 50 Equal Weight / Value 20) and produced a
        false ambiguity. Upstox documents separate ``name``,
        ``trading_symbol`` and unique ``instrument_key`` fields for index rows.

        Ranking is deterministic and based only on exact source metadata:
        exact display name plus exact key suffix, then exact display name,
        then exact key suffix, then exact full trading symbol. Duplicate rows
        for the same instrument_key are collapsed. Two distinct
        keys at the same best rank still fail closed with diagnostic candidates.
        """
        def norm(value: Any) -> str:
            return " ".join(str(value or "").strip().casefold().split())

        eligible: list[tuple[int, dict[str, Any]]] = []
        for row in self.rows:
            if norm(row.get("segment")) != "nse_index":
                continue
            if norm(row.get("instrument_type")) != "index":
                continue
            exchange = norm(row.get("exchange"))
            if exchange and exchange != "nse":
                continue

            key = str(row.get("instrument_key") or "").strip()
            if not key or not key.upper().startswith("NSE_INDEX|"):
                continue

            name = norm(row.get("name"))
            trading_symbol = norm(row.get("trading_symbol"))
            key_suffix = norm(key.split("|", 1)[1] if "|" in key else "")

            # Exact identity only. Do not substring-match related NIFTY indices.
            exact_name = name in {"nifty 50", "nifty fifty"}
            exact_key = key_suffix in {"nifty 50", "nifty fifty"}
            if exact_name and exact_key:
                rank = 0
            elif exact_name:
                rank = 1
            elif exact_key:
                rank = 2
            elif trading_symbol in {"nifty 50", "nifty fifty"}:
                rank = 3
            else:
                continue
            eligible.append((rank, row))

        if not eligible:
            raise ScannerError(
                "NIFTY_INSTRUMENT_NOT_FOUND",
                "No exact NSE NIFTY 50 index identity was found in the official instrument master; related indices were intentionally excluded.",
            )

        best_rank = min(rank for rank, _ in eligible)
        best_rows = [row for rank, row in eligible if rank == best_rank]
        by_key: dict[str, dict[str, Any]] = {}
        for row in best_rows:
            key = str(row["instrument_key"]).strip()
            existing = by_key.get(key)
            if existing is None:
                by_key[key] = row
            else:
                # Same key means same Upstox instrument. Prefer the row with
                # more populated documented identity fields, without changing key.
                quality = lambda item: sum(bool(str(item.get(field) or "").strip()) for field in ("name", "exchange", "trading_symbol", "exchange_token"))
                if quality(row) > quality(existing):
                    by_key[key] = row

        if len(by_key) != 1:
            details = [
                {
                    "instrument_key": key,
                    "name": str(row.get("name", ""))[:80],
                    "trading_symbol": str(row.get("trading_symbol", ""))[:40],
                    "exchange": str(row.get("exchange", ""))[:12],
                }
                for key, row in sorted(by_key.items())
            ]
            raise ScannerError(
                "NIFTY_INSTRUMENT_AMBIGUOUS",
                "Multiple distinct exact NSE NIFTY 50 instrument identities remain at the same priority; refusing to guess. Candidates=" + json.dumps(details, separators=(",", ":")),
            )
        return next(iter(by_key.values()))

    def _options_for_index(self, index_key: str, asof: date) -> list[dict[str, Any]]:
        result = []
        for row in self.rows:
            if str(row.get("segment", "")).upper() != "NSE_FO":
                continue
            if str(row.get("instrument_type", "")).upper() not in {"CE", "PE"}:
                continue
            if str(row.get("underlying_key", "")) != index_key:
                continue
            expiry = parse_expiry(row.get("expiry"))
            if expiry is None or expiry < asof:
                continue
            if not isinstance(row.get("strike_price"), (int, float)) or not row.get("instrument_key"):
                continue
            item = dict(row)
            item["_expiry_date"] = expiry
            item["_weekly"] = row.get("weekly") is True or str(row.get("weekly", "")).casefold() == "true"
            result.append(item)
        return result

    def resolve_expiry(self, index_key: str, asof: date, explicit_expiry: Optional[date]) -> date:
        contracts = self._options_for_index(index_key, asof)
        expiries = sorted({r["_expiry_date"] for r in contracts})
        if explicit_expiry:
            if explicit_expiry < asof or explicit_expiry not in expiries:
                raise ScannerError("EXPIRY_NOT_FOUND", f"Configured expiry {explicit_expiry} is not an eligible NIFTY option expiry in instrument master")
            return explicit_expiry
        weekly = sorted({r["_expiry_date"] for r in contracts if r["_weekly"]})
        if not weekly:
            raise ScannerError("WEEKLY_EXPIRY_NOT_FOUND", "No eligible weekly NIFTY option expiry is identified in current instrument metadata; refusing to silently choose monthly")
        return weekly[0]

    def resolve_future(self, index_key: str, asof: date) -> Optional[dict[str, Any]]:
        futures = []
        for row in self.rows:
            if str(row.get("segment", "")).upper() != "NSE_FO" or str(row.get("instrument_type", "")).upper() != "FUT":
                continue
            if str(row.get("underlying_key", "")) != index_key:
                continue
            underlying = str(row.get("underlying_symbol", row.get("name", ""))).casefold()
            if "nifty" not in underlying:
                continue
            exp = parse_expiry(row.get("expiry"))
            if exp is None or exp < asof:
                continue
            if row.get("instrument_key"):
                futures.append((exp, row))
        if not futures:
            return None
        futures.sort(key=lambda item: item[0])
        return dict(futures[0][1])

    def option_instruments(self, index_key: str, expiry: date) -> list[dict[str, Any]]:
        options = self._options_for_index(index_key, expiry)
        chosen = [r for r in options if r["_expiry_date"] == expiry]
        if not chosen:
            raise ScannerError("OPTION_CONTRACTS_NOT_FOUND", f"No current NIFTY contracts for expiry {expiry}")
        return chosen


# ---------- Normalized domain models ----------

@dataclass(frozen=True)
class Candle:
    start: datetime
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0
    oi: float = 0.0

    def __post_init__(self) -> None:
        if self.start.tzinfo is None or self.start.utcoffset() is None:
            raise ValueError("Candle timestamp must be timezone-aware")
        vals = (self.open, self.high, self.low, self.close, self.volume, self.oi)
        if not all(math.isfinite(float(v)) for v in vals):
            raise ValueError("Candle values must be finite")
        if self.low > min(self.open, self.close) or self.high < max(self.open, self.close) or self.low > self.high:
            raise ValueError("Invalid OHLC ordering")
        if self.volume < 0 or self.oi < 0:
            raise ValueError("Negative volume/OI is invalid")

    @property
    def close_time(self) -> datetime:
        return self.start + timedelta(minutes=1)

    def to_dict(self) -> dict[str, Any]:
        return {"timestamp": self.start.isoformat(), "open": self.open, "high": self.high, "low": self.low, "close": self.close, "volume": self.volume, "oi": self.oi}


@dataclass(frozen=True)
class OptionRecord:
    instrument_key: str
    expiry: date
    strike: float
    side: str
    ltp: float
    oi: float
    volume: float
    previous_session_oi: Optional[float]
    chain_bid: float
    chain_ask: float
    chain_bid_qty: float
    chain_ask_qty: float
    delta: Optional[float]
    gamma: Optional[float]
    theta: Optional[float]
    vega: Optional[float]
    iv: Optional[float]

    def to_dict(self) -> dict[str, Any]:
        return json_safe(asdict(self))


@dataclass(frozen=True)
class OptionQuote:
    instrument_key: str
    timestamp: Optional[datetime]
    ltp: float
    bid: float
    ask: float
    bid_qty: float
    ask_qty: float
    volume: float
    oi: float
    strike: float
    side: str
    expiry: date
    delta: Optional[float]
    gamma: Optional[float]
    theta: Optional[float]
    vega: Optional[float]
    iv: Optional[float]

    @property
    def mid(self) -> float:
        return (self.bid + self.ask) / 2 if self.bid > 0 and self.ask >= self.bid else 0.0

    @property
    def spread_pct(self) -> float:
        return (self.ask - self.bid) / self.mid * 100 if self.mid > 0 else math.inf


@dataclass(frozen=True)
class PriceLevel:
    price: float
    side: str  # SUPPORT or RESISTANCE
    source: str
    strength: float


@dataclass(frozen=True)
class Setup:
    kind: str
    direction: str  # BULLISH or BEARISH
    trigger: float
    invalidation: float
    confirmed_at: datetime
    source_level: Optional[float]
    source: str
    price_confidence: float


# ---------- Candle/chain/quote API normalization ----------

def instrument_path_key(key: str) -> str:
    return urllib.parse.quote(key, safe="")


def fetch_candles(client: UpstoxClient, instrument_key: str, now: datetime, *, minutes: int = 1) -> list[Candle]:
    url = f"{API_BASE}/v3/historical-candle/intraday/{instrument_path_key(instrument_key)}/minutes/{minutes}"
    payload = client.get_json(url)
    data = payload.get("data") or {}
    raw_candles = data.get("candles") if isinstance(data, dict) else None
    if not isinstance(raw_candles, list):
        raise ScannerError("CANDLE_DATA_MISSING", f"No candle list returned for {instrument_key}")
    result: list[Candle] = []
    seen: set[datetime] = set()
    for row in raw_candles:
        if not isinstance(row, (list, tuple)) or len(row) < 5:
            continue
        ts = parse_datetime(row[0])
        if ts is None:
            continue
        if ts.astimezone(IST).date() != now.astimezone(IST).date():
            continue
        try:
            candle = Candle(ts, float(row[1]), float(row[2]), float(row[3]), float(row[4]), float(row[5] or 0) if len(row) > 5 else 0.0, float(row[6] or 0) if len(row) > 6 else 0.0)
        except (TypeError, ValueError, OverflowError):
            continue
        # A candle stamped at 12:57 represents 12:57–12:58; never use it before it closes.
        if candle.close_time > now.astimezone(IST):
            continue
        if candle.start in seen:
            continue
        seen.add(candle.start)
        result.append(candle)
    result.sort(key=lambda c: c.start)
    if not result:
        raise ScannerError("CANDLE_DATA_MISSING", f"No completed intraday candles returned for {instrument_key}")
    return result


def fetch_daily_candles(client: UpstoxClient, instrument_key: str, now: datetime) -> list[Candle]:
    to_date = now.astimezone(IST).date() - timedelta(days=1)
    from_date = to_date - timedelta(days=20)
    path = f"{API_BASE}/v3/historical-candle/{instrument_path_key(instrument_key)}/days/1/{to_date.isoformat()}/{from_date.isoformat()}"
    try:
        payload = client.get_json(path)
    except ScannerError as exc:
        LOG.warning("Prior-session daily candles unavailable (%s); prior-session levels will be omitted", exc.code)
        return []
    raw = (payload.get("data") or {}).get("candles")
    if not isinstance(raw, list):
        return []
    candles: list[Candle] = []
    for row in raw:
        if not isinstance(row, (list, tuple)) or len(row) < 5:
            continue
        ts = parse_datetime(row[0])
        if not ts or ts.date() >= now.astimezone(IST).date():
            continue
        try:
            candles.append(Candle(ts, float(row[1]), float(row[2]), float(row[3]), float(row[4]), float(row[5] or 0) if len(row) > 5 else 0.0, float(row[6] or 0) if len(row) > 6 else 0.0))
        except (TypeError, ValueError):
            continue
    candles.sort(key=lambda c: c.start)
    return candles


def parse_option_chain(payload: Mapping[str, Any], expiry: date, fetched_at: datetime) -> tuple[float, list[OptionRecord]]:
    raw = payload.get("data")
    if not isinstance(raw, list) or not raw:
        raise ScannerError("OPTION_CHAIN_EMPTY", "Upstox returned an empty option chain")
    spot_candidates = []
    records: list[OptionRecord] = []
    for row in raw:
        if not isinstance(row, dict):
            continue
        row_exp = parse_expiry(row.get("expiry"))
        if row_exp is not None and row_exp != expiry:
            continue
        spot = row.get("underlying_spot_price")
        if isinstance(spot, (int, float)) and math.isfinite(float(spot)) and float(spot) > 0:
            spot_candidates.append(float(spot))
        strike_raw = row.get("strike_price")
        try:
            strike = float(strike_raw)
        except (TypeError, ValueError):
            continue
        if not math.isfinite(strike) or strike <= 0:
            continue
        for side, node_name in (("CE", "call_options"), ("PE", "put_options")):
            node = row.get(node_name)
            if not isinstance(node, dict) or not node.get("instrument_key"):
                continue
            md = node.get("market_data") or {}
            gr = node.get("option_greeks") or {}
            try:
                ltp = float(md.get("ltp") or 0)
                oi = float(md.get("oi") or 0)
                volume = float(md.get("volume") or 0)
                bid = float(md.get("bid_price") or 0)
                ask = float(md.get("ask_price") or 0)
                bid_qty = float(md.get("bid_qty") or 0)
                ask_qty = float(md.get("ask_qty") or 0)
                prev_oi_raw = md.get("prev_oi")
                prev_oi = float(prev_oi_raw) if prev_oi_raw is not None else None
                if prev_oi is not None and (not math.isfinite(prev_oi) or prev_oi < 0):
                    prev_oi = None
            except (TypeError, ValueError):
                continue
            if any(not math.isfinite(x) for x in (ltp, oi, volume, bid, ask, bid_qty, ask_qty)) or min(ltp, oi, volume, bid, ask, bid_qty, ask_qty) < 0:
                continue
            def greek(name: str) -> Optional[float]:
                try:
                    val = gr.get(name)
                    value = float(val) if val is not None else None
                    return value if value is not None and math.isfinite(value) else None
                except (TypeError, ValueError):
                    return None
            records.append(OptionRecord(str(node["instrument_key"]), expiry, strike, side, ltp, oi, volume, prev_oi, bid, ask, bid_qty, ask_qty, greek("delta"), greek("gamma"), greek("theta"), greek("vega"), greek("iv")))
    if not spot_candidates or not records:
        raise ScannerError("OPTION_CHAIN_INVALID", "Option chain lacks a valid spot price or option rows")
    spot = median(spot_candidates)
    records = [r for r in records if r.expiry == expiry]
    return spot, records


def parse_full_quotes(payload: Mapping[str, Any], requested: Sequence[str]) -> dict[str, dict[str, Any]]:
    data = payload.get("data")
    if not isinstance(data, dict):
        raise ScannerError("MARKET_QUOTES_INVALID", "Full Market Quotes response has no data object")
    normalize = lambda s: str(s).replace(":", "|").strip().casefold()
    want = {normalize(key): key for key in requested}
    result: dict[str, dict[str, Any]] = {}
    for response_key, quote in data.items():
        if not isinstance(quote, dict):
            continue
        instrument_key = quote.get("instrument_token") or quote.get("instrument_key") or response_key
        normalized = normalize(instrument_key)
        target = want.get(normalized)
        if not target:
            # Some versions return the resolved trading symbol as dictionary key; try normalized response key too.
            target = want.get(normalize(response_key))
        if target:
            result[target] = quote
    return result


def get_full_quotes(client: UpstoxClient, instrument_keys: Sequence[str]) -> dict[str, dict[str, Any]]:
    keys = sorted(set(key for key in instrument_keys if key))
    if not keys:
        raise ScannerError("MARKET_QUOTES_INVALID", "No instrument keys supplied to quote endpoint")
    if len(keys) > 500:
        raise ScannerError("MARKET_QUOTES_LIMIT", "Full Market Quotes supports at most 500 instruments per request")
    query = urllib.parse.urlencode({"instrument_key": ",".join(keys)})
    payload = client.get_json(f"{API_BASE}/v3/market-quote/quotes?{query}")
    return parse_full_quotes(payload, keys)


# ---------- OI computation: raw deltas are never clipped ----------

def _snapshot_rows(records: Sequence[OptionRecord], spot: float, width_steps: int = 16) -> list[dict[str, Any]]:
    strikes = sorted({r.strike for r in records})
    if not strikes:
        return []
    atm = min(strikes, key=lambda strike: abs(strike - spot))
    i = strikes.index(atm)
    selected_strikes = set(strikes[max(0, i - width_steps): min(len(strikes), i + width_steps + 1)])
    return [r.to_dict() for r in records if r.strike in selected_strikes]


def _lookup_records(records: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    return {str(r.get("instrument_key")): r for r in records if r.get("instrument_key")}


def _weighted_direction(oi_delta: float, oi_pct: Optional[float], premium_pct: Optional[float], side: str, threshold: float) -> tuple[float, str]:
    """Classify the four OI/premium signatures and return a signed hypothesis.

    The premium input is the Greek-adjusted residual percentage where possible.
    This is an inference about positioning, not identification of participants.
    Positive is bullish; negative is bearish.
    """
    if oi_pct is None or premium_pct is None or abs(oi_delta) < 0.5 or abs(premium_pct) < 0.025:
        return 0.0, "INSUFFICIENT_CHANGE"
    oi_up = oi_delta > 0
    premium_up = premium_pct > 0
    if side == "CE":
        if oi_up and premium_up:
            label, bullish = "CALL_LONG_BUILDUP_LIKELY", True
        elif oi_up and not premium_up:
            label, bullish = "CALL_WRITING_LIKELY", False
        elif not oi_up and premium_up:
            label, bullish = "CALL_SHORT_COVERING_LIKELY", True
        else:
            label, bullish = "CALL_LONG_UNWINDING_LIKELY", False
    else:
        if oi_up and premium_up:
            label, bullish = "PUT_LONG_BUILDUP_LIKELY", False
        elif oi_up and not premium_up:
            label, bullish = "PUT_WRITING_LIKELY", True
        elif not oi_up and premium_up:
            label, bullish = "PUT_SHORT_COVERING_LIKELY", False
        else:
            label, bullish = "PUT_LONG_UNWINDING_LIKELY", True
    # Keep the observed OI percentage untouched; cap only the score input.
    oi_strength = min(abs(oi_pct) / max(threshold, 1e-9), 1.5) / 1.5
    premium_strength = min(abs(premium_pct) / 0.75, 1.0)
    position_strength = 1.0 if oi_up else 0.78
    return (1.0 if bullish else -1.0) * oi_strength * premium_strength * position_strength, label


def _chain_premium_proxy(ltp: Any, bid: Any, ask: Any) -> tuple[Optional[float], str, float]:
    """Prefer a valid two-sided chain midpoint; use LTP only as lower-confidence fallback."""
    try:
        last = float(ltp)
        bid_value = float(bid)
        ask_value = float(ask)
    except (TypeError, ValueError, OverflowError):
        return None, "UNAVAILABLE", 0.0
    if not all(math.isfinite(x) for x in (last, bid_value, ask_value)):
        return None, "UNAVAILABLE", 0.0
    if bid_value > 0 and ask_value >= bid_value and ask_value > 0:
        mid = (bid_value + ask_value) / 2.0
        spread_pct = (ask_value - bid_value) / mid * 100.0 if mid > 0 else math.inf
        # Very wide books are poor premium-change proxies; mark fallback explicitly.
        if mid > 0 and spread_pct <= 15.0:
            return mid, "CHAIN_MID", 1.0
    if last > 0:
        return last, "LTP_FALLBACK_NO_EVENT_TIMESTAMP", 0.60
    return None, "UNAVAILABLE", 0.0

def _greek_adjusted_premium_change(
    current: OptionRecord, previous: Mapping[str, Any], previous_spot: Optional[float],
    current_spot: float, elapsed_seconds: float,
) -> tuple[Optional[float], Optional[float], str, float]:
    """Return raw and Greek-adjusted premium % changes.

    The adjustment removes estimated delta/gamma exposure to spot, elapsed theta
    and IV/vega effects where both snapshots contain the required Greeks. Theta
    is treated as a daily premium change and Vega as premium change per IV point,
    consistent with the Upstox option-Greek field convention. When a required
    Greek is missing, raw premium change is returned with sharply lower quality.
    """
    cur_premium, cur_source, cur_quality = _chain_premium_proxy(current.ltp, current.chain_bid, current.chain_ask)
    prev_premium, prev_source, prev_quality = _chain_premium_proxy(
        previous.get("ltp", 0), previous.get("chain_bid", 0), previous.get("chain_ask", 0)
    )
    if cur_premium is None or prev_premium is None or prev_premium <= 0 or cur_source != prev_source:
        return None, None, "SOURCE_MISMATCH" if cur_source != prev_source else "UNAVAILABLE", 0.0
    raw_pct = 100.0 * (cur_premium - prev_premium) / prev_premium
    prev_delta = previous.get("delta")
    prev_gamma = previous.get("gamma")
    prev_theta = previous.get("theta")
    prev_vega = previous.get("vega")
    prev_iv = previous.get("iv")
    greek_values = (current.delta, current.gamma, current.theta, current.vega, current.iv,
                    prev_delta, prev_gamma, prev_theta, prev_vega, prev_iv)
    try:
        vals = [float(x) for x in greek_values]
        if not all(math.isfinite(x) for x in vals) or previous_spot is None or previous_spot <= 0:
            raise ValueError
        delta_now, gamma_now, theta_now, vega_now, iv_now, delta_prev, gamma_prev, theta_prev, vega_prev, iv_prev = vals
        spot_move = current_spot - previous_spot
        avg_delta = (delta_now + delta_prev) / 2.0
        avg_gamma = (gamma_now + gamma_prev) / 2.0
        avg_theta = (theta_now + theta_prev) / 2.0
        avg_vega = (vega_now + vega_prev) / 2.0
        iv_move = iv_now - iv_prev
        elapsed_days = max(0.0, elapsed_seconds) / 86400.0
        expected_change = avg_delta * spot_move + 0.5 * avg_gamma * spot_move * spot_move
        expected_change += avg_theta * elapsed_days + avg_vega * iv_move
        residual = (cur_premium - prev_premium) - expected_change
        residual_pct = 100.0 * residual / prev_premium
        if not math.isfinite(residual_pct):
            raise ValueError
        quality = min(cur_quality, prev_quality) * 1.0
        return raw_pct, residual_pct, "GREEK_ADJUSTED_CHAIN_MID" if cur_source == "CHAIN_MID" else "GREEK_ADJUSTED_LTP", quality
    except (TypeError, ValueError, OverflowError):
        # LTP/midpoint change without complete Greeks is only a weak proxy.
        quality = min(cur_quality, prev_quality) * (0.45 if cur_source == "CHAIN_MID" else 0.25)
        return raw_pct, raw_pct, "RAW_PREMIUM_FALLBACK_LOW_CONFIDENCE", quality


def calculate_oi_evidence(
    current_records: Sequence[OptionRecord],
    previous_snapshot: Optional[Mapping[str, Any]],
    session_baseline: Optional[Mapping[str, Any]],
    spot: float,
    fetched_at: datetime,
    config: Config,
    snapshot_history: Optional[Sequence[Mapping[str, Any]]] = None,
) -> dict[str, Any]:
    """Directional OI evidence with four-way flow classification.

    Computes true consecutive-snapshot deltas, session-baseline deltas, and
    compact strike-level walls. No interpolated OI observations are generated.
    """
    current_session = fetched_at.astimezone(IST).date().isoformat()
    current_expiry = current_records[0].expiry.isoformat() if current_records else None
    previous_rows = _lookup_records(previous_snapshot.get("rows", [])) if previous_snapshot else {}
    baseline_rows = _lookup_records(session_baseline.get("rows", [])) if session_baseline else {}
    previous_time = parse_datetime(previous_snapshot.get("fetched_at")) if previous_snapshot else None
    previous_spot = None
    try:
        previous_spot = float(previous_snapshot.get("spot")) if previous_snapshot else None
    except (TypeError, ValueError, OverflowError):
        previous_spot = None
    previous_same = bool(
        current_records and previous_snapshot and previous_time and previous_time < fetched_at
        and previous_snapshot.get("session_date") == current_session
        and previous_snapshot.get("expiry") == current_expiry
    )
    baseline_same = bool(
        current_records and session_baseline
        and session_baseline.get("session_date") == current_session
        and session_baseline.get("expiry") == current_expiry
    )
    if not previous_same:
        previous_rows = {}
    if not baseline_same:
        baseline_rows = {}

    strikes = sorted({r.strike for r in current_records})
    step_values = [round(b - a, 6) for a, b in zip(strikes, strikes[1:]) if b > a]
    step = median(step_values) if step_values else 50.0
    current_near = [r for r in current_records if abs(r.strike - spot) <= step * 15]
    if not current_near:
        current_near = list(current_records)

    per_contract: list[dict[str, Any]] = []
    weighted_sum = total_direction_weight = 0.0
    activity_oi_pct: list[tuple[float, float]] = []
    activity_premium_pct: list[tuple[float, float]] = []
    contributing_contract_count = paired_contract_count = 0
    aggregate_delta_ce = aggregate_prev_ce = aggregate_delta_pe = aggregate_prev_pe = 0.0
    session_delta_call = session_delta_put = 0.0
    session_baseline_count = 0
    pcr_rows_call = pcr_rows_put = 0.0
    call_oi_by_strike: dict[float, float] = defaultdict(float)
    put_oi_by_strike: dict[float, float] = defaultdict(float)
    call_delta_by_strike: dict[float, float] = defaultdict(float)
    put_delta_by_strike: dict[float, float] = defaultdict(float)
    call_prev_by_strike: dict[float, float] = defaultdict(float)
    put_prev_by_strike: dict[float, float] = defaultdict(float)
    flow_abs_by_strike: dict[tuple[str, float], float] = defaultdict(float)
    writer_abs_by_strike: dict[tuple[str, float], float] = defaultdict(float)
    support_flow_abs_by_strike: dict[tuple[str, float], float] = defaultdict(float)
    opposing_flow_abs_by_strike: dict[tuple[str, float], float] = defaultdict(float)
    flow_labels_by_strike: dict[tuple[str, float], Counter[str]] = defaultdict(Counter)

    # Larger absolute OI changes should carry somewhat more influence than tiny
    # changes with the same percentage. The bounded weight preserves percentage
    # change as the primary test while respecting material strike-level activity.
    # CE and PE are normalised independently.
    max_abs_delta_by_side: dict[str, float] = {"CE": 0.0, "PE": 0.0}
    for candidate in current_near:
        old = previous_rows.get(candidate.instrument_key)
        if not old or not previous_same or old.get("expiry") != candidate.expiry.isoformat() or old.get("side") != candidate.side:
            continue
        try:
            old_oi_value = float(old.get("oi", 0) or 0)
            old_strike_value = float(old.get("strike", -1))
            if old_oi_value >= 0 and old_strike_value == candidate.strike and math.isfinite(old_oi_value):
                max_abs_delta_by_side[candidate.side] = max(
                    max_abs_delta_by_side[candidate.side], abs(candidate.oi - old_oi_value)
                )
        except (TypeError, ValueError, OverflowError):
            continue

    for rec in current_near:
        prev = previous_rows.get(rec.instrument_key)
        base = baseline_rows.get(rec.instrument_key)
        delta_oi = delta_pct = delta_volume = raw_premium_pct = residual_premium_pct = None
        premium_change_source = "UNAVAILABLE"
        premium_source_quality = 0.0
        prev_oi_value: Optional[float] = None
        if (prev and previous_same and prev.get("expiry") == rec.expiry.isoformat()
                and prev.get("side") == rec.side and float(prev.get("strike", -1)) == rec.strike):
            try:
                prev_oi_value = float(prev.get("oi", 0) or 0)
                prev_volume = float(prev.get("volume", 0) or 0)
            except (TypeError, ValueError, OverflowError):
                prev_oi_value = None
            if prev_oi_value is not None and math.isfinite(prev_oi_value) and prev_oi_value >= 0:
                delta_oi = rec.oi - prev_oi_value
                delta_pct = 100.0 * delta_oi / prev_oi_value if prev_oi_value > 0 else None
                elapsed = (fetched_at - previous_time).total_seconds() if previous_time else 0.0
                raw_premium_pct, residual_premium_pct, premium_change_source, premium_source_quality = _greek_adjusted_premium_change(
                    rec, prev, previous_spot, spot, elapsed
                )
                if math.isfinite(prev_volume) and prev_volume >= 0:
                    delta_volume = rec.volume - prev_volume if rec.volume >= prev_volume else None
                paired_contract_count += 1
                if rec.side == "CE":
                    aggregate_delta_ce += delta_oi
                    aggregate_prev_ce += prev_oi_value
                    call_delta_by_strike[rec.strike] += delta_oi
                    call_prev_by_strike[rec.strike] += prev_oi_value
                else:
                    aggregate_delta_pe += delta_oi
                    aggregate_prev_pe += prev_oi_value
                    put_delta_by_strike[rec.strike] += delta_oi
                    put_prev_by_strike[rec.strike] += prev_oi_value

        previous_session_delta = previous_session_delta_pct = None
        if rec.previous_session_oi is not None:
            try:
                prev_session_oi = float(rec.previous_session_oi)
                if math.isfinite(prev_session_oi) and prev_session_oi >= 0:
                    previous_session_delta = rec.oi - prev_session_oi
                    previous_session_delta_pct = 100.0 * previous_session_delta / prev_session_oi if prev_session_oi > 0 else None
            except (TypeError, ValueError, OverflowError):
                pass

        session_delta = None
        if (base and baseline_same and base.get("expiry") == rec.expiry.isoformat()
                and base.get("side") == rec.side and float(base.get("strike", -1)) == rec.strike):
            try:
                baseline_oi = float(base.get("oi", 0) or 0)
                if math.isfinite(baseline_oi) and baseline_oi >= 0:
                    session_delta = rec.oi - baseline_oi
                    session_baseline_count += 1
                    if rec.side == "CE":
                        session_delta_call += session_delta
                    else:
                        session_delta_put += session_delta
            except (TypeError, ValueError, OverflowError):
                session_delta = None

        contribution = 0.0
        flow_label = "FIRST_SNAPSHOT_OR_NO_PREVIOUS_BASELINE"
        if delta_oi is not None and delta_pct is not None and residual_premium_pct is not None:
            contribution, flow_label = _weighted_direction(
                delta_oi, delta_pct, residual_premium_pct, rec.side, config.oi_material_threshold_pct
            )
            distance_steps = abs(rec.strike - spot) / max(step, 1e-6)
            proximity_weight = 1.0 / (1.0 + 0.18 * distance_steps)
            volume_weight = 1.05 if delta_volume is not None and delta_volume > 0 else 0.90
            max_side_delta = max_abs_delta_by_side.get(rec.side, 0.0)
            oi_change_weight = 0.55 + 0.45 * math.sqrt(abs(delta_oi) / max_side_delta) if max_side_delta > 0 else 0.55
            effective = contribution * proximity_weight * volume_weight * premium_source_quality * oi_change_weight
            weighted_sum += effective
            total_direction_weight += abs(effective)
            if abs(effective) > 1e-9:
                contributing_contract_count += 1
                activity_oi_pct.append((abs(delta_pct), proximity_weight))
                activity_premium_pct.append((abs(residual_premium_pct), proximity_weight * premium_source_quality))
                key = (rec.side, rec.strike)
                flow_abs_by_strike[key] += abs(delta_oi)
                flow_labels_by_strike[key][flow_label] += abs(delta_oi)
                if flow_label in {"CALL_WRITING_LIKELY", "PUT_WRITING_LIKELY"}:
                    writer_abs_by_strike[key] += abs(delta_oi)
                # A wall is strengthened specifically by writing at that
                # strike. Long unwinding can be directionally bearish/bullish,
                # but it reduces the open-interest wall and must not be counted
                # as fresh resistance/support. Other buyer/covering flows also
                # reduce confidence that the existing wall will hold.
                supportive_labels = (
                    {"CALL_WRITING_LIKELY"} if rec.side == "CE" else {"PUT_WRITING_LIKELY"}
                )
                opposing_labels = (
                    {"CALL_LONG_BUILDUP_LIKELY", "CALL_SHORT_COVERING_LIKELY", "CALL_LONG_UNWINDING_LIKELY"}
                    if rec.side == "CE" else
                    {"PUT_LONG_BUILDUP_LIKELY", "PUT_SHORT_COVERING_LIKELY", "PUT_LONG_UNWINDING_LIKELY"}
                )
                if flow_label in supportive_labels:
                    support_flow_abs_by_strike[key] += abs(delta_oi)
                elif flow_label in opposing_labels:
                    opposing_flow_abs_by_strike[key] += abs(delta_oi)

        per_contract.append({
            "instrument_key": rec.instrument_key, "expiry": rec.expiry.isoformat(), "strike": rec.strike,
            "side": rec.side, "oi": rec.oi, "delta_oi_snapshot": delta_oi,
            "delta_oi_pct_snapshot": delta_pct, "delta_oi_session": session_delta,
            "delta_oi_vs_prev_session": previous_session_delta,
            "delta_oi_vs_prev_session_pct": previous_session_delta_pct,
            "delta_volume_snapshot": delta_volume, "premium_change_pct_snapshot": raw_premium_pct,
            "premium_residual_change_pct_snapshot": residual_premium_pct,
            "premium_change_source": premium_change_source,
            "oi_change_weight": oi_change_weight if delta_oi is not None else 0.0,
            "material_oi_change": delta_pct is not None and abs(delta_pct) >= config.oi_material_threshold_pct,
            "flow_interpretation": flow_label, "directional_contribution": contribution,
            "distance_from_spot_points": rec.strike - spot,
        })
        if abs(rec.strike - spot) <= step * 10:
            if rec.side == "CE":
                pcr_rows_call += rec.oi
            else:
                pcr_rows_put += rec.oi
        if rec.side == "CE":
            call_oi_by_strike[rec.strike] += rec.oi
        else:
            put_oi_by_strike[rec.strike] += rec.oi

    directional_balance = weighted_sum / total_direction_weight if total_direction_weight > 1e-9 else 0.0
    def weighted_average(items: Sequence[tuple[float, float]]) -> Optional[float]:
        denominator = sum(weight for _, weight in items)
        return sum(value * weight for value, weight in items) / denominator if denominator > 0 else None

    average_abs_oi_pct = weighted_average(activity_oi_pct)
    average_abs_premium_pct = weighted_average(activity_premium_pct)
    oi_activity_factor = min(1.0, (average_abs_oi_pct or 0.0) / max(config.oi_material_threshold_pct, 1e-9))
    premium_activity_factor = min(1.0, (average_abs_premium_pct or 0.0) / 0.75)
    breadth_factor = min(1.0, contributing_contract_count / 5.0)
    interval_seconds = (fetched_at - previous_time).total_seconds() if previous_same and previous_time else None
    expected_interval = max(30, config.expected_oi_interval_seconds)
    interval_factor = min(1.0, expected_interval / max(interval_seconds, float(expected_interval))) if interval_seconds and interval_seconds > 0 else 0.0
    activity_factor = math.sqrt(max(0.0, oi_activity_factor * premium_activity_factor)) * breadth_factor * interval_factor
    confidence = abs(directional_balance) * activity_factor
    score = directional_balance * activity_factor
    bull_score, bear_score = max(0.0, score), max(0.0, -score)
    margin = abs(directional_balance)
    if not previous_same:
        label = "MISSING"
    elif contributing_contract_count < 3 or confidence < config.min_oi_direction_confidence or margin < config.min_oi_score_margin:
        label = "MIXED"
    else:
        label = "BULLISH" if directional_balance > 0 else "BEARISH"

    def aggregate_pct(delta: float, baseline_oi: float) -> Optional[float]:
        return 100.0 * delta / baseline_oi if baseline_oi > 0 else None

    def walls(source: Mapping[float, float], side: str) -> list[dict[str, Any]]:
        ordered = sorted(source.items(), key=lambda pair: pair[1], reverse=True)
        max_oi = ordered[0][1] if ordered else 0.0
        return [{"strike": strike, "oi": value, "relative_strength": value / max_oi if max_oi else 0.0, "side": side}
                for strike, value in ordered[:5] if value > 0 and max_oi > 0]

    max_call = max(call_oi_by_strike.values(), default=0.0)
    max_put = max(put_oi_by_strike.values(), default=0.0)
    oi_levels: list[dict[str, Any]] = []
    for strike in strikes:
        call_oi = call_oi_by_strike.get(strike, 0.0)
        put_oi = put_oi_by_strike.get(strike, 0.0)
        call_key, put_key = ("CE", strike), ("PE", strike)
        call_flow_count = flow_abs_by_strike.get(call_key, 0.0)
        put_flow_count = flow_abs_by_strike.get(put_key, 0.0)
        call_writer = writer_abs_by_strike.get(call_key, 0.0) / call_flow_count if call_flow_count > 0 else 0.0
        put_writer = writer_abs_by_strike.get(put_key, 0.0) / put_flow_count if put_flow_count > 0 else 0.0
        call_support_flow = support_flow_abs_by_strike.get(call_key, 0.0) / call_flow_count if call_flow_count > 0 else 0.0
        put_support_flow = support_flow_abs_by_strike.get(put_key, 0.0) / put_flow_count if put_flow_count > 0 else 0.0
        call_opposing_flow = opposing_flow_abs_by_strike.get(call_key, 0.0) / call_flow_count if call_flow_count > 0 else 0.0
        put_opposing_flow = opposing_flow_abs_by_strike.get(put_key, 0.0) / put_flow_count if put_flow_count > 0 else 0.0
        call_labels = flow_labels_by_strike.get(call_key, Counter())
        put_labels = flow_labels_by_strike.get(put_key, Counter())
        call_flow = call_labels.most_common(1)[0][0] if call_labels else "NO_FLOW_EVIDENCE"
        put_flow = put_labels.most_common(1)[0][0] if put_labels else "NO_FLOW_EVIDENCE"
        call_delta = call_delta_by_strike.get(strike, 0.0)
        put_delta = put_delta_by_strike.get(strike, 0.0)
        oi_levels.append({
            "strike": strike, "call_oi": call_oi, "put_oi": put_oi,
            "call_relative_oi": call_oi / max_call if max_call > 0 else 0.0,
            "put_relative_oi": put_oi / max_put if max_put > 0 else 0.0,
            "call_delta_oi_snapshot": call_delta, "put_delta_oi_snapshot": put_delta,
            "call_delta_oi_pct_snapshot": aggregate_pct(call_delta, call_prev_by_strike.get(strike, 0.0)),
            "put_delta_oi_pct_snapshot": aggregate_pct(put_delta, put_prev_by_strike.get(strike, 0.0)),
            "oi_material_threshold_pct": config.oi_material_threshold_pct,
            "call_writer_strength": call_writer, "put_writer_strength": put_writer,
            "call_resistance_flow_strength": call_support_flow,
            "put_support_flow_strength": put_support_flow,
            "call_bullish_flow_strength": call_opposing_flow,
            "put_bearish_flow_strength": put_opposing_flow,
            "call_flow": call_flow, "put_flow": put_flow,
        })

    oi_zones = {}
    for option_side, source, deltas in (("CE", call_oi_by_strike, call_delta_by_strike), ("PE", put_oi_by_strike, put_delta_by_strike)):
        for position in ("ABOVE", "BELOW"):
            candidates = [(k, v) for k, v in source.items() if (k > spot if position == "ABOVE" else k < spot)]
            oi_zones[f"highest_{'call' if option_side == 'CE' else 'put'}_oi_{position.casefold()}_spot"] = [
                {"strike": k, "oi": v, "delta_oi_snapshot": deltas.get(k), "option_side": option_side,
                 "position_vs_spot": position, "relative_strength": v / max(source.values(), default=1.0)}
                for k, v in sorted(candidates, key=lambda x: x[1], reverse=True)[:3]
            ]
            oi_zones[f"fastest_{'call' if option_side == 'CE' else 'put'}_oi_change_{position.casefold()}_spot"] = [
                {"strike": k, "oi": source.get(k), "delta_oi_snapshot": deltas.get(k), "option_side": option_side,
                 "position_vs_spot": position, "relative_strength": abs(deltas.get(k, 0.0)) / max((abs(x) for x in deltas.values()), default=1.0)}
                for k, _ in sorted(candidates, key=lambda x: abs(deltas.get(x[0], 0.0)), reverse=True)[:3]
            ]

    horizons: dict[str, Any] = {}
    history = [x for x in (snapshot_history or []) if isinstance(x, Mapping)
               and x.get("session_date") == current_session and x.get("expiry") == current_expiry]
    history.sort(key=lambda x: parse_datetime(x.get("fetched_at")) or datetime.min.replace(tzinfo=IST))
    current_by_id = {r.instrument_key: r for r in current_near}
    for horizon in (5, 15, 30):
        target_time = fetched_at - timedelta(minutes=horizon)
        candidates = [x for x in history if (parse_datetime(x.get("fetched_at")) or fetched_at) <= target_time]
        base_snapshot = candidates[-1] if candidates else None
        base_time = parse_datetime(base_snapshot.get("fetched_at")) if base_snapshot else None
        if not base_snapshot or not base_time:
            horizons[f"{horizon}m"] = {"available": False, "raw_label": "MISSING", "reason": "INSUFFICIENT_SNAPSHOT_HISTORY"}
            continue
        base_rows = _lookup_records(base_snapshot.get("rows", []))
        try:
            base_spot = float(base_snapshot.get("spot"))
        except (TypeError, ValueError, OverflowError):
            base_spot = 0.0
        call_delta_h = put_delta_h = call_base_h = put_base_h = 0.0
        matched_h = contributing_h = 0
        horizon_weighted = horizon_total_weight = 0.0
        max_abs_delta_h_by_side: dict[str, float] = {"CE": 0.0, "PE": 0.0}
        for candidate_key, candidate in current_by_id.items():
            old = base_rows.get(candidate_key)
            if not old or old.get("expiry") != current_expiry or old.get("side") != candidate.side:
                continue
            try:
                old_oi = float(old.get("oi", 0) or 0)
                old_strike = float(old.get("strike", -1))
                if old_oi >= 0 and old_strike == candidate.strike and math.isfinite(old_oi):
                    max_abs_delta_h_by_side[candidate.side] = max(
                        max_abs_delta_h_by_side[candidate.side], abs(candidate.oi - old_oi)
                    )
            except (TypeError, ValueError, OverflowError):
                continue
        horizon_oi_activity: list[tuple[float, float]] = []
        horizon_premium_activity: list[tuple[float, float]] = []
        for instrument_key, rec in current_by_id.items():
            old = base_rows.get(instrument_key)
            if not old or old.get("expiry") != current_expiry or old.get("side") != rec.side:
                continue
            try:
                old_strike = float(old.get("strike", -1))
                old_oi = float(old.get("oi", 0) or 0)
            except (TypeError, ValueError, OverflowError):
                continue
            if old_strike != rec.strike or not math.isfinite(old_oi) or old_oi < 0:
                continue
            matched_h += 1
            delta_h = rec.oi - old_oi
            pct_h = 100.0 * delta_h / old_oi if old_oi > 0 else None
            if rec.side == "CE":
                call_delta_h += delta_h
                call_base_h += old_oi
            else:
                put_delta_h += delta_h
                put_base_h += old_oi
            raw_h, residual_h, _, quality_h = _greek_adjusted_premium_change(
                rec, old, base_spot if base_spot > 0 else None, spot,
                max(0.0, (fetched_at - base_time).total_seconds()),
            )
            if pct_h is None or residual_h is None:
                continue
            contribution_h, _ = _weighted_direction(delta_h, pct_h, residual_h, rec.side, config.oi_material_threshold_pct)
            if abs(contribution_h) <= 1e-9:
                continue
            proximity_h = 1.0 / (1.0 + 0.18 * abs(rec.strike - spot) / max(step, 1e-6))
            volume_h = 1.0
            max_side_delta_h = max_abs_delta_h_by_side.get(rec.side, 0.0)
            oi_change_weight_h = 0.55 + 0.45 * math.sqrt(abs(delta_h) / max_side_delta_h) if max_side_delta_h > 0 else 0.55
            effective_h = contribution_h * proximity_h * volume_h * quality_h * oi_change_weight_h
            horizon_weighted += effective_h
            horizon_total_weight += abs(effective_h)
            contributing_h += 1
            horizon_oi_activity.append((abs(pct_h), proximity_h))
            horizon_premium_activity.append((abs(residual_h), proximity_h * quality_h))
        balance_h = horizon_weighted / horizon_total_weight if horizon_total_weight > 1e-9 else 0.0
        def horizon_average(items: Sequence[tuple[float, float]]) -> Optional[float]:
            denom = sum(weight for _, weight in items)
            return sum(value * weight for value, weight in items) / denom if denom > 0 else None
        oi_factor_h = min(1.0, (horizon_average(horizon_oi_activity) or 0.0) / max(config.oi_material_threshold_pct, 1e-9))
        premium_factor_h = min(1.0, (horizon_average(horizon_premium_activity) or 0.0) / 0.75)
        breadth_h = min(1.0, contributing_h / 5.0)
        elapsed_h = max(0.0, (fetched_at - base_time).total_seconds())
        interval_h = min(1.0, (horizon * 60.0) / max(elapsed_h, horizon * 60.0))
        activity_h = math.sqrt(max(0.0, oi_factor_h * premium_factor_h)) * breadth_h * interval_h
        confidence_h = abs(balance_h) * activity_h
        margin_h = abs(balance_h)
        if matched_h < 10 or contributing_h < 3 or confidence_h < config.min_oi_direction_confidence or margin_h < config.min_oi_score_margin:
            label_h = "MIXED"
        else:
            label_h = "BULLISH" if balance_h > 0 else "BEARISH"
        horizons[f"{horizon}m"] = {
            "available": matched_h >= 10,
            "matched_contracts": matched_h,
            "contributing_contracts": contributing_h,
            "actual_elapsed_seconds": elapsed_h,
            "call_delta_oi": call_delta_h if matched_h >= 10 else None,
            "put_delta_oi": put_delta_h if matched_h >= 10 else None,
            "call_delta_oi_pct": aggregate_pct(call_delta_h, call_base_h) if matched_h >= 10 else None,
            "put_delta_oi_pct": aggregate_pct(put_delta_h, put_base_h) if matched_h >= 10 else None,
            "directional_balance": balance_h if matched_h >= 10 else None,
            "confidence": confidence_h if matched_h >= 10 else None,
            "raw_label": label_h if matched_h >= 10 else "MISSING",
            "reason": None if matched_h >= 10 else "INSUFFICIENT_MATCHED_CONTRACTS",
        }

    # Multi-horizon direction is a separately reported context vote. The latest
    # snapshot remains the immediate signal; longer horizons never overwrite it.
    horizon_weights = {5: 0.45, 15: 0.35, 30: 0.20}
    horizon_votes = []
    for horizon, weight in horizon_weights.items():
        item = horizons.get(f"{horizon}m", {})
        label_h = item.get("raw_label")
        conf_h = float(item.get("confidence") or 0.0)
        if item.get("available") and label_h in {"BULLISH", "BEARISH"} and conf_h > 0:
            horizon_votes.append((1.0 if label_h == "BULLISH" else -1.0, weight * min(1.0, conf_h / 0.65), label_h))
    if len(horizon_votes) >= 2:
        vote_weight = sum(weight for _, weight, _ in horizon_votes)
        horizon_balance = sum(direction * weight for direction, weight, _ in horizon_votes) / vote_weight if vote_weight else 0.0
        multi_horizon_direction = "BULLISH" if horizon_balance > 0.10 else "BEARISH" if horizon_balance < -0.10 else "MIXED"
        current_direction = "BULLISH" if directional_balance > 0 else "BEARISH" if directional_balance < 0 else "MIXED"
        horizon_alignment = sum(weight for direction, weight, _ in horizon_votes if (direction > 0 and current_direction == "BULLISH") or (direction < 0 and current_direction == "BEARISH")) / vote_weight if vote_weight and current_direction != "MIXED" else 0.0
    else:
        horizon_balance = None
        multi_horizon_direction = "INSUFFICIENT_HORIZONS" if horizon_votes else "UNAVAILABLE"
        horizon_alignment = None

    return {
        "label": label, "score": score, "directional_balance": directional_balance,
        "bull_score": bull_score, "bear_score": bear_score, "confidence": confidence,
        "score_margin": margin, "snapshot_time": fetched_at.isoformat(),
        "snapshot_interval_seconds": interval_seconds,
        "snapshot_status": "FETCH_TIME_USED_SOURCE_EVENT_TIME_NOT_PROVIDED_BY_CHAIN_RESPONSE",
        "compared_to_previous_successful_snapshot": previous_same,
        "contracts_compared": paired_contract_count,
        "contributing_contract_count": contributing_contract_count,
        "material_contract_count": sum(1 for r in per_contract if r["material_oi_change"]),
        "average_abs_delta_oi_pct": average_abs_oi_pct,
        "average_abs_premium_change_pct": average_abs_premium_pct,
        "premium_mid_comparison_count": sum(1 for r in per_contract if "CHAIN_MID" in r["premium_change_source"]),
        "premium_ltp_fallback_count": sum(1 for r in per_contract if "LTP" in r["premium_change_source"]),
        "premium_source_mismatch_count": sum(1 for r in per_contract if r["premium_change_source"] in {"SOURCE_MISMATCH", "UNAVAILABLE"}),
        "oi_activity_factor": oi_activity_factor, "premium_activity_factor": premium_activity_factor,
        "breadth_factor": breadth_factor, "interval_factor": interval_factor,
        "aggregate_delta_call_oi_snapshot": aggregate_delta_ce if previous_same else None,
        "aggregate_delta_put_oi_snapshot": aggregate_delta_pe if previous_same else None,
        "aggregate_delta_call_oi_pct_snapshot": aggregate_pct(aggregate_delta_ce, aggregate_prev_ce) if previous_same else None,
        "aggregate_delta_put_oi_pct_snapshot": aggregate_pct(aggregate_delta_pe, aggregate_prev_pe) if previous_same else None,
        "aggregate_pe_minus_ce_delta_oi": (aggregate_delta_pe - aggregate_delta_ce) if previous_same else None,
        "session_baseline_contracts_matched": session_baseline_count,
        "session_delta_call_oi_nearby": session_delta_call if session_baseline_count else None,
        "session_delta_put_oi_nearby": session_delta_put if session_baseline_count else None,
        "nearby_pcr": pcr_rows_put / pcr_rows_call if pcr_rows_call > 0 else None,
        "call_oi_walls": walls(call_oi_by_strike, "CALL_OI_POTENTIAL_RESISTANCE"),
        "put_oi_walls": walls(put_oi_by_strike, "PUT_OI_POTENTIAL_SUPPORT"),
        "oi_levels": oi_levels, "oi_horizons": horizons,
        "multi_horizon_direction": multi_horizon_direction,
        "multi_horizon_balance": horizon_balance,
        "multi_horizon_alignment": horizon_alignment,
        "multi_horizon_vote_count": len(horizon_votes),
        "oi_zones_above_below_spot": oi_zones, "features": per_contract,
    }


# ---------- Price structure and regimes ----------

def true_ranges(candles: Sequence[Candle]) -> list[float]:
    result: list[float] = []
    previous_close: Optional[float] = None
    for candle in candles:
        tr = candle.high - candle.low
        if previous_close is not None:
            tr = max(tr, abs(candle.high - previous_close), abs(candle.low - previous_close))
        result.append(max(0.0, tr))
        previous_close = candle.close
    return result


def atr(candles: Sequence[Candle], period: int = 14) -> Optional[float]:
    trs = true_ranges(candles)
    if len(trs) < period:
        return median(trs) if trs else None
    value = sum(trs[:period]) / period
    for tr in trs[period:]:
        value = (value * (period - 1) + tr) / period
    return value if value > 0 else None


def ema(values: Sequence[float], period: int) -> Optional[float]:
    if not values:
        return None
    alpha = 2.0 / (period + 1.0)
    value = float(values[0])
    for item in values[1:]:
        value = alpha * float(item) + (1.0 - alpha) * value
    return value


def aggregate_candles(candles: Sequence[Candle], size_minutes: int, now: datetime) -> list[Candle]:
    groups: dict[datetime, list[Candle]] = defaultdict(list)
    for c in candles:
        minute = c.start.astimezone(IST).replace(second=0, microsecond=0)
        bucket_minute = minute.minute - (minute.minute % size_minutes)
        bucket = minute.replace(minute=bucket_minute)
        if bucket + timedelta(minutes=size_minutes) <= now.astimezone(IST):
            groups[bucket].append(c)
    bars: list[Candle] = []
    for bucket, items in sorted(groups.items()):
        items.sort(key=lambda x: x.start)
        # Do not aggregate incomplete/gapped buckets into synthetic bars.
        expected = [bucket + timedelta(minutes=i) for i in range(size_minutes)]
        timestamps = [item.start.astimezone(IST) for item in items]
        if timestamps != expected:
            continue
        bars.append(Candle(bucket, items[0].open, max(x.high for x in items), min(x.low for x in items), items[-1].close, sum(x.volume for x in items), items[-1].oi))
    return bars


def _contiguous_tail(candles: Sequence[Candle], interval_minutes: int) -> list[Candle]:
    """Return the chronologically ordered, duplicate-free contiguous tail.

    Gaps are not forward-filled. A gap shortens the usable lookback so an
    indicator cannot accidentally bridge missing market observations.
    """
    if not candles:
        return []
    ordered = sorted(candles, key=lambda c: c.start)
    unique: list[Candle] = []
    for candle in ordered:
        if unique and candle.start == unique[-1].start:
            # Keep the last provider record for a duplicate timestamp; count is
            # reported separately by price_regime so this is never invisible.
            unique[-1] = candle
        else:
            unique.append(candle)
    tail = [unique[-1]]
    expected = timedelta(minutes=interval_minutes)
    for candle in reversed(unique[:-1]):
        if tail[0].start - candle.start != expected:
            break
        tail.insert(0, candle)
    return tail


def _timeframe_direction(bars: Sequence[Candle], *, fast_period: int, slow_period: int,
                         atr_value: Optional[float], minimum_bars: int) -> tuple[str, float, Optional[float], Optional[float], float]:
    """Return direction/confidence/fast-EMA/slow-EMA/efficiency for one timeframe."""
    if len(bars) < minimum_bars:
        return "UNKNOWN", 0.0, None, None, 0.0
    closes = [float(c.close) for c in bars]
    recent = closes[-min(6, len(closes)):]
    net = recent[-1] - recent[0]
    path = sum(abs(b - a) for a, b in zip(recent, recent[1:]))
    efficiency = abs(net) / path if path > 0 else 0.0
    fast = ema(closes[-max(fast_period * 3, fast_period):], fast_period)
    slow = ema(closes[-max(slow_period * 3, slow_period):], slow_period) if len(closes) >= slow_period else None
    diffs = [b - a for a, b in zip(recent, recent[1:])]
    up = sum(x > 0 for x in diffs)
    down = sum(x < 0 for x in diffs)
    share = max(up, down) / max(1, len(diffs))
    scale = max(float(atr_value or 0.0), 1.0)
    magnitude = min(1.0, abs(net) / max(scale * 0.75, 1.0))
    if fast is None:
        return "UNKNOWN", 0.0, None, slow, efficiency
    bullish_stack = closes[-1] > fast and (slow is None or fast >= slow)
    bearish_stack = closes[-1] < fast and (slow is None or fast <= slow)
    threshold = max(0.18 * scale, 0.75)
    if net > threshold and bullish_stack and up >= max(2, len(diffs) // 2):
        direction = "BULLISH"
    elif net < -threshold and bearish_stack and down >= max(2, len(diffs) // 2):
        direction = "BEARISH"
    elif efficiency <= 0.24 and abs(net) <= max(0.45 * scale, 1.0):
        direction = "SIDEWAYS"
    else:
        direction = "MIXED"
    confidence = 0.0 if direction == "UNKNOWN" else min(1.0, 0.34 * share + 0.36 * magnitude + 0.30 * min(1.0, efficiency / 0.65))
    if direction == "SIDEWAYS":
        confidence = max(0.45, min(1.0, 1.0 - efficiency))
    if direction == "MIXED":
        confidence = min(confidence, 0.55)
    return direction, round(confidence, 4), fast, slow, efficiency


def _opening_1m_direction(one: Sequence[Candle], atr1: Optional[float], minimum_bars: int) -> tuple[str, float, Optional[float], Optional[float]]:
    """Fast but bounded opening read from completed 1m bars.

    This is intentionally less lagging than the normal EMA8 logic but requires
    a minimum six-minute sample by default and caps confidence because the
    opening auction/first prints are noisier than mature intraday structure.
    """
    if len(one) < minimum_bars:
        return "UNKNOWN", 0.0, None, None
    closes = [float(c.close) for c in one]
    recent = closes[-min(6, len(closes)):]
    ema_fast = ema(recent, 5)
    if ema_fast is None or len(recent) < 4:
        return "UNKNOWN", 0.0, ema_fast, None
    momentum = recent[-1] - recent[-4]
    diffs = [b - a for a, b in zip(recent, recent[1:])]
    up = sum(x > 0 for x in diffs)
    down = sum(x < 0 for x in diffs)
    scale = max(float(atr1 or 0.0), 1.0)
    latest = one[-1]
    body = float(latest.close - latest.open)
    if closes[-1] > float(ema_fast) and momentum > 0.12 * scale and up >= 3 and body > 0:
        direction = "BULLISH"
    elif closes[-1] < float(ema_fast) and momentum < -0.12 * scale and down >= 3 and body < 0:
        direction = "BEARISH"
    else:
        direction = "MIXED"
    consistency = max(up, down) / max(1, len(diffs))
    momentum_strength = min(1.0, abs(momentum) / max(scale * 0.70, 1.0))
    ema_distance = min(1.0, abs(closes[-1] - float(ema_fast)) / max(scale * 0.50, 1.0))
    confidence = min(0.82, 0.42 * consistency + 0.38 * momentum_strength + 0.20 * ema_distance)
    if direction == "MIXED":
        confidence = min(confidence, 0.48)
    return direction, round(confidence, 4), ema_fast, momentum


def _opening_3m_direction(three: Sequence[Candle], atr3: Optional[float], minimum_bars: int) -> tuple[str, float, Optional[float], Optional[float], float]:
    """Opening 3m confirmation using two or three *completed* bars only.

    No synthetic bars and no slow EMA are used before enough history exists.
    Direction instead requires net progress, directional candle bodies and a
    strong close location, which is more appropriate for opening discovery.
    """
    if len(three) < minimum_bars:
        return "UNKNOWN", 0.0, None, None, 0.0
    bars = list(three[-min(3, len(three)):])
    closes = [float(c.close) for c in bars]
    net = closes[-1] - closes[0]
    path = sum(abs(b - a) for a, b in zip(closes, closes[1:]))
    efficiency = abs(net) / path if path > 0 else 0.0
    scale = max(float(atr3 or 0.0), 1.0)
    bullish_bodies = sum(c.close > c.open for c in bars)
    bearish_bodies = sum(c.close < c.open for c in bars)
    latest = bars[-1]
    rng = max(float(latest.high - latest.low), 1e-9)
    close_location = (float(latest.close) - float(latest.low)) / rng
    minimum_move = max(0.12 * scale, 1.0)
    needed_bodies = max(1, (len(bars) + 1) // 2)
    if net > minimum_move and bullish_bodies >= needed_bodies and close_location >= 0.58:
        direction = "BULLISH"
    elif net < -minimum_move and bearish_bodies >= needed_bodies and close_location <= 0.42:
        direction = "BEARISH"
    elif efficiency <= 0.20 and abs(net) <= max(0.35 * scale, 1.0):
        direction = "SIDEWAYS"
    else:
        direction = "MIXED"
    body_share = max(bullish_bodies, bearish_bodies) / max(1, len(bars))
    magnitude = min(1.0, abs(net) / max(scale * 0.65, 1.0))
    location_strength = abs(close_location - 0.5) * 2.0
    cap = 0.72 if len(bars) == 2 else 0.84
    confidence = min(cap, 0.36 * body_share + 0.38 * magnitude + 0.26 * location_strength)
    if direction == "SIDEWAYS":
        confidence = max(0.45, min(cap, 1.0 - efficiency))
    if direction == "MIXED":
        confidence = min(confidence, 0.50)
    fast = ema(closes, min(3, len(closes)))
    return direction, round(confidence, 4), fast, None, efficiency


def _developing_15m_context(fifteen: Sequence[Candle], atr15: Optional[float]) -> tuple[str, float, Optional[float], Optional[float], float, str]:
    """Use the first completed 15m bar immediately as low-confidence context.

    One/two bars are deliberately provisional; from three bars onward the
    normal multi-bar direction model takes over. Missing 15m context never
    counts against an otherwise valid 1m/3m trade.
    """
    n = len(fifteen)
    if n == 0:
        return "UNKNOWN", 0.0, None, None, 0.0, "NO_COMPLETED_15M_BAR"
    if n >= 3:
        direction, confidence, fast, slow, efficiency = _timeframe_direction(
            fifteen, fast_period=3, slow_period=5, atr_value=atr15, minimum_bars=3
        )
        status = "DEVELOPING_CONTEXT" if n < 5 else "MATURE_CONTEXT"
        return direction, confidence, fast, slow, efficiency, status

    bars = list(fifteen[-n:])
    scale = max(float(atr15 or 0.0), 1.0)
    if n == 1:
        bar = bars[0]
        rng = max(float(bar.high - bar.low), 1e-9)
        body = float(bar.close - bar.open)
        close_location = (float(bar.close) - float(bar.low)) / rng
        body_strength = min(1.0, abs(body) / max(0.55 * scale, 1.0))
        if body > max(0.10 * scale, 1.0) and close_location >= 0.60:
            direction = "BULLISH"
        elif body < -max(0.10 * scale, 1.0) and close_location <= 0.40:
            direction = "BEARISH"
        elif abs(body) <= max(0.18 * scale, 1.0):
            direction = "SIDEWAYS"
        else:
            direction = "MIXED"
        confidence = min(0.48, 0.24 + 0.16 * body_strength + 0.08 * abs(close_location - 0.5) * 2.0)
        return direction, round(confidence, 4), float(bar.close), None, 0.0, "PROVISIONAL_1BAR_CONTEXT"

    first, second = bars[-2], bars[-1]
    net = float(second.close - first.close)
    path = abs(float(second.close - first.close))
    efficiency = 1.0 if path > 0 else 0.0
    latest_range = max(float(second.high - second.low), 1e-9)
    close_location = (float(second.close) - float(second.low)) / latest_range
    body_votes_bull = sum(c.close > c.open for c in bars)
    body_votes_bear = sum(c.close < c.open for c in bars)
    minimum_move = max(0.10 * scale, 1.0)
    if net > minimum_move and body_votes_bull >= 1 and close_location >= 0.55:
        direction = "BULLISH"
    elif net < -minimum_move and body_votes_bear >= 1 and close_location <= 0.45:
        direction = "BEARISH"
    elif abs(net) <= max(0.22 * scale, 1.0):
        direction = "SIDEWAYS"
    else:
        direction = "MIXED"
    magnitude = min(1.0, abs(net) / max(0.70 * scale, 1.0))
    confidence = min(0.62, 0.34 + 0.20 * magnitude + 0.08 * abs(close_location - 0.5) * 2.0)
    if direction == "MIXED":
        confidence = min(confidence, 0.46)
    return direction, round(confidence, 4), ema([first.close, second.close], 2), None, efficiency, "DEVELOPING_2BAR_CONTEXT"


def price_regime(candles_1m: Sequence[Candle], candles_3m: Sequence[Candle], candles_15m: Sequence[Candle], config: Optional[Config] = None) -> dict[str, Any]:
    """v109 market structure: 1m trigger, 3m execution confirmation, 15m context.

    The 15-minute layer supplies regime/support-resistance context and never
    forces the entry engine to wait for repeated five-minute confirmations.
    """
    one = _contiguous_tail(candles_1m, 1)
    three = _contiguous_tail(candles_3m, 3)
    fifteen = _contiguous_tail(candles_15m, 15)
    duplicate_1m = max(0, len(candles_1m) - len({c.start for c in candles_1m}))
    duplicate_3m = max(0, len(candles_3m) - len({c.start for c in candles_3m}))
    duplicate_15m = max(0, len(candles_15m) - len({c.start for c in candles_15m}))
    atr1 = atr(one, 14)
    atr3 = atr(three, 10)
    atr15 = atr(fifteen, 8)

    cfg_open_1m = int(config.opening_min_1m_bars) if config is not None else 6
    cfg_open_3m = int(config.opening_min_3m_bars) if config is not None else 2
    warmup_minutes = int(config.opening_warmup_minutes) if config is not None else 6
    session_open = datetime.combine(one[-1].start.astimezone(IST).date(), dtime(9, 15), tzinfo=IST) if one else None
    latest_close_time = one[-1].close_time.astimezone(IST) if one else None
    opening_minutes_elapsed = ((latest_close_time - session_open).total_seconds() / 60.0) if session_open and latest_close_time else 0.0
    before_0930 = bool(latest_close_time and latest_close_time.time() <= dtime(9, 30))

    execution_1m = "UNKNOWN"
    execution_1m_conf = 0.0
    ema8_1 = None
    ema_fast_1m = None
    momentum_3m = None
    execution_status = "INSUFFICIENT_CONTIGUOUS_1M_HISTORY"
    if before_0930 and len(one) >= cfg_open_1m:
        execution_1m, execution_1m_conf, ema_fast_1m, momentum_3m = _opening_1m_direction(one, atr1, cfg_open_1m)
        ema8_1 = ema([c.close for c in one[-min(8, len(one)):]], min(8, len(one)))
        execution_status = "OPENING_READY" if execution_1m in {"BULLISH", "BEARISH"} else "OPENING_MIXED_PRICE_ACTION"
    elif len(one) >= 8:
        closes = [c.close for c in one]
        ema8_1 = ema(closes[-18:], 8)
        ema_fast_1m = ema8_1
        prev_ema = ema(closes[-19:-1], 8) if len(closes) >= 9 else None
        momentum_3m = closes[-1] - closes[-4]
        recent = closes[-5:]
        diffs = [b - a for a, b in zip(recent, recent[1:])]
        up = sum(x > 0 for x in diffs)
        down = sum(x < 0 for x in diffs)
        scale = max(float(atr1 or 0.0), 1.0)
        if closes[-1] > float(ema8_1) and momentum_3m > 0.12 * scale and up >= 2 and (prev_ema is None or ema8_1 >= prev_ema):
            execution_1m = "BULLISH"
        elif closes[-1] < float(ema8_1) and momentum_3m < -0.12 * scale and down >= 2 and (prev_ema is None or ema8_1 <= prev_ema):
            execution_1m = "BEARISH"
        else:
            execution_1m = "MIXED"
        consistency = max(up, down) / max(1, len(diffs))
        momentum_strength = min(1.0, abs(momentum_3m) / max(scale * 0.65, 1.0))
        ema_distance = min(1.0, abs(closes[-1] - float(ema8_1)) / max(scale * 0.45, 1.0))
        execution_1m_conf = round(0.40 * consistency + 0.38 * momentum_strength + 0.22 * ema_distance, 4)
        execution_status = "READY" if execution_1m in {"BULLISH", "BEARISH"} else "MIXED_PRICE_ACTION"

    if before_0930 and len(three) >= cfg_open_3m and len(three) < 4:
        direction_3m, confidence_3m, ema5_3m, ema9_3m, efficiency_3m = _opening_3m_direction(three, atr3, cfg_open_3m)
    else:
        direction_3m, confidence_3m, ema5_3m, ema9_3m, efficiency_3m = _timeframe_direction(
            three, fast_period=5, slow_period=9, atr_value=atr3, minimum_bars=4
        )
    context_15m, confidence_15m, ema3_15m, ema5_15m, efficiency_15m, context_status = _developing_15m_context(fifteen, atr15)

    if opening_minutes_elapsed < warmup_minutes:
        regime = "OPENING_WARMUP"
    elif execution_1m == "UNKNOWN" or direction_3m == "UNKNOWN":
        regime = "EARLY_SESSION"
    elif before_0930 and execution_1m == direction_3m == "BULLISH":
        regime = "OPENING_DISCOVERY_BULLISH"
    elif before_0930 and execution_1m == direction_3m == "BEARISH":
        regime = "OPENING_DISCOVERY_BEARISH"
    elif context_15m == "SIDEWAYS":
        regime = "SIDEWAYS"
    elif execution_1m == direction_3m == "BULLISH":
        if context_15m == "BEARISH":
            regime = "REVERSAL_BEAR_TO_BULL"
        elif context_15m == "BULLISH":
            regime = "TREND_BULLISH"
        else:
            regime = "MOMENTUM_BULLISH"
    elif execution_1m == direction_3m == "BEARISH":
        if context_15m == "BULLISH":
            regime = "REVERSAL_BULL_TO_BEAR"
        elif context_15m == "BEARISH":
            regime = "TREND_BEARISH"
        else:
            regime = "MOMENTUM_BEARISH"
    elif direction_3m == "SIDEWAYS" or execution_1m == "MIXED":
        regime = "SIDEWAYS_TRANSITION"
    else:
        regime = "TRANSITION"

    return {
        "regime": regime,
        "execution_direction": execution_1m,
        "execution_status": execution_status,
        "execution_confidence": execution_1m_conf,
        "execution_3m_direction": direction_3m,
        "execution_3m_confidence": confidence_3m,
        "market_context_15m_bias": context_15m,
        "market_context_15m_confidence": confidence_15m,
        "market_context_15m_status": context_status,
        # Compatibility aliases used by the rest of the scanner and emails.
        "higher_timeframe_bias": context_15m,
        "higher_timeframe_confidence": confidence_15m,
        "higher_timeframe_status": context_status,
        "atr_1m": atr1,
        "atr_3m": atr3,
        "atr_15m": atr15,
        "atr_5m": atr3,
        "momentum_3m_points": momentum_3m,
        "ema8_1m": ema8_1,
        "ema_fast_1m": ema_fast_1m,
        "opening_minutes_elapsed": opening_minutes_elapsed,
        "ema5_3m": ema5_3m,
        "ema9_3m": ema9_3m,
        "ema3_15m": ema3_15m,
        "ema5_15m": ema5_15m,
        "efficiency_ratio": efficiency_15m,
        "efficiency_3m": efficiency_3m,
        "completed_1m_contiguous_count": len(one),
        "completed_3m_contiguous_count": len(three),
        "completed_15m_contiguous_count": len(fifteen),
        "completed_5m_contiguous_count": len(three),
        "duplicate_1m_candle_count": duplicate_1m,
        "duplicate_3m_candle_count": duplicate_3m,
        "duplicate_15m_candle_count": duplicate_15m,
        "duplicate_5m_candle_count": duplicate_3m,
        "reason": "1M_TRIGGER_3M_CONFIRMATION_15M_CONTEXT",
    }

def confirmed_pivots(candles: Sequence[Candle], left: int = 2, right: int = 2) -> tuple[list[tuple[int, float]], list[tuple[int, float]]]:
    lows: list[tuple[int, float]] = []
    highs: list[tuple[int, float]] = []
    # A pivot is used only once the right-side candles have closed.
    for i in range(left, len(candles) - right):
        window = candles[i - left:i + right + 1]
        low = candles[i].low
        high = candles[i].high
        if low <= min(c.low for j, c in enumerate(window) if j != left) and sum(1 for c in window if c.low == low) == 1:
            lows.append((i, low))
        if high >= max(c.high for j, c in enumerate(window) if j != left) and sum(1 for c in window if c.high == high) == 1:
            highs.append((i, high))
    return lows, highs


def valid_futures_vwap(futures_candles: Sequence[Candle]) -> Optional[float]:
    numerator = 0.0
    denominator = 0.0
    for c in futures_candles:
        if c.volume <= 0:
            continue
        typical = (c.high + c.low + c.close) / 3.0
        numerator += typical * c.volume
        denominator += c.volume
    return numerator / denominator if denominator > 0 else None


def build_levels(
    candles: Sequence[Candle], previous_daily: Sequence[Candle], oi_evidence: Mapping[str, Any], futures_vwap: Optional[float],
    atr1: Optional[float], config: Config, *, candles_3m: Sequence[Candle] = (), candles_15m: Sequence[Candle] = (),
) -> list[PriceLevel]:
    """Build local execution levels plus stronger 15m context levels.

    v109 deliberately separates local trade management levels from broader
    context. OI walls remain evidence but no longer dominate entry targets.
    """
    if not candles:
        return []
    levels: list[PriceLevel] = []
    tol = max(0.10, float(atr1 or 0.0) * config.level_cluster_atr_fraction)
    latest = candles[-1]
    day = latest.start.astimezone(IST).date()
    session = [c for c in candles if c.start.astimezone(IST).date() == day]
    if session:
        prior_session = session[:-1]
        if prior_session:
            levels.append(PriceLevel(min(c.low for c in prior_session), "SUPPORT", "SESSION_LOW", 2.1))
            levels.append(PriceLevel(max(c.high for c in prior_session), "RESISTANCE", "SESSION_HIGH", 2.1))
        opening15 = [c for c in session if c.start.astimezone(IST).time() < dtime(9, 30)]
        if len(opening15) >= 15:
            levels.extend([
                PriceLevel(min(c.low for c in opening15), "SUPPORT", "OPENING_RANGE_15M_LOW", 2.0),
                PriceLevel(max(c.high for c in opening15), "RESISTANCE", "OPENING_RANGE_15M_HIGH", 2.0),
            ])
    if previous_daily:
        prev = max((c for c in previous_daily if c.start.astimezone(IST).date() < day), key=lambda c: c.start, default=None)
        if prev:
            levels.extend([
                PriceLevel(prev.high, "RESISTANCE", "PREVIOUS_SESSION_HIGH", 2.2),
                PriceLevel(prev.low, "SUPPORT", "PREVIOUS_SESSION_LOW", 2.2),
                PriceLevel(prev.close, "SUPPORT" if prev.close <= latest.close else "RESISTANCE", "PREVIOUS_SESSION_CLOSE", 1.4),
            ])

    # Fast local pivots are useful for stops and first objectives.
    lows1, highs1 = confirmed_pivots(candles, config.pivot_left, config.pivot_right)
    for idx, value in lows1[-8:]:
        levels.append(PriceLevel(value, "SUPPORT", f"1M_SWING_LOW_{candles[idx].start.astimezone(IST).strftime('%H%M')}", 1.45))
    for idx, value in highs1[-8:]:
        levels.append(PriceLevel(value, "RESISTANCE", f"1M_SWING_HIGH_{candles[idx].start.astimezone(IST).strftime('%H%M')}", 1.45))

    # 3m pivots are the primary execution structure for entries/targets.
    if len(candles_3m) >= 3:
        lows3, highs3 = confirmed_pivots(candles_3m, 1, 1)
        for idx, value in lows3[-6:]:
            levels.append(PriceLevel(value, "SUPPORT", f"3M_SWING_LOW_{candles_3m[idx].start.astimezone(IST).strftime('%H%M')}", 1.9))
        for idx, value in highs3[-6:]:
            levels.append(PriceLevel(value, "RESISTANCE", f"3M_SWING_HIGH_{candles_3m[idx].start.astimezone(IST).strftime('%H%M')}", 1.9))

    # 15m context becomes useful from the first completed bar. One/two bars
    # contribute developing range boundaries; confirmed pivots take over once
    # sufficient bars exist. This improves early support/resistance without
    # making 15m a timing gate.
    if candles_15m:
        context_tail = list(candles_15m[-min(2, len(candles_15m)):])
        context_strength = 1.75 if len(candles_15m) == 1 else 2.05
        levels.append(PriceLevel(min(c.low for c in context_tail), "SUPPORT", "15M_CONTEXT_RANGE_LOW", context_strength))
        levels.append(PriceLevel(max(c.high for c in context_tail), "RESISTANCE", "15M_CONTEXT_RANGE_HIGH", context_strength))
    if len(candles_15m) >= 3:
        lows15, highs15 = confirmed_pivots(candles_15m, 1, 1)
        for idx, value in lows15[-4:]:
            levels.append(PriceLevel(value, "SUPPORT", f"15M_CONTEXT_LOW_{candles_15m[idx].start.astimezone(IST).strftime('%H%M')}", 2.6))
        for idx, value in highs15[-4:]:
            levels.append(PriceLevel(value, "RESISTANCE", f"15M_CONTEXT_HIGH_{candles_15m[idx].start.astimezone(IST).strftime('%H%M')}", 2.6))

    # NIFTY trades around 50-point landmarks. Keep nearby grid levels visible as
    # actionable objectives; they are not treated as proof of support/resistance.
    grid = float(config.target_grid_points)
    if grid > 0:
        center = round(latest.close / grid) * grid
        for n in range(-4, 5):
            level = center + n * grid
            if level <= 0 or abs(level - latest.close) > config.target2_max_points + grid:
                continue
            side = "SUPPORT" if level < latest.close else "RESISTANCE" if level > latest.close else "SUPPORT"
            levels.append(PriceLevel(level, side, "NIFTY_50_GRID", 1.25))
            if abs(level - latest.close) < 1e-6:
                levels.append(PriceLevel(level, "RESISTANCE", "NIFTY_50_GRID", 1.25))

    if futures_vwap is not None and math.isfinite(futures_vwap):
        levels.append(PriceLevel(futures_vwap, "SUPPORT" if futures_vwap <= latest.close else "RESISTANCE", "FUTURES_VWAP_CONTEXT_ONLY", 0.75))

    # OI walls are context/confirmation. Their strength is capped below 15m
    # structural levels so OI cannot force a distant target by itself.
    for wall in oi_evidence.get("oi_levels", []):
        try:
            strike = float(wall.get("strike"))
            put_rel = float(wall.get("put_relative_oi") or 0.0)
            call_rel = float(wall.get("call_relative_oi") or 0.0)
            put_flow = float(wall.get("put_support_flow_strength") or wall.get("put_writer_strength") or 0.0)
            call_flow = float(wall.get("call_resistance_flow_strength") or wall.get("call_writer_strength") or 0.0)
        except (TypeError, ValueError, OverflowError):
            continue
        if strike < latest.close and put_rel >= 0.18:
            strength = min(2.1, 0.9 + 0.75 * put_rel + 0.45 * put_flow)
            levels.append(PriceLevel(strike, "SUPPORT", "OI_PUT_CONTEXT", strength))
        elif strike > latest.close and call_rel >= 0.18:
            strength = min(2.1, 0.9 + 0.75 * call_rel + 0.45 * call_flow)
            levels.append(PriceLevel(strike, "RESISTANCE", "OI_CALL_CONTEXT", strength))

    out: list[PriceLevel] = []
    for side in ("SUPPORT", "RESISTANCE"):
        items = sorted((x for x in levels if x.side == side), key=lambda x: x.price)
        clusters: list[list[PriceLevel]] = []
        for item in items:
            if clusters and abs(item.price - median([v.price for v in clusters[-1]])) <= tol:
                clusters[-1].append(item)
            else:
                clusters.append([item])
        for cluster in clusters:
            total = sum(max(0.01, x.strength) for x in cluster)
            price = sum(x.price * max(0.01, x.strength) for x in cluster) / total
            strength = min(5.0, sum(x.strength for x in cluster))
            sources = "+".join(dict.fromkeys(x.source for x in cluster))
            out.append(PriceLevel(price, side, sources, strength))
    return sorted(out, key=lambda x: x.price)

def _level_has_structural_provenance(level: PriceLevel) -> bool:
    """Only structural evidence may define a hard T1 barrier.

    Futures VWAP and OI walls are useful context, but cannot by themselves be
    promoted to guaranteed support/resistance. A clustered level remains valid
    when at least one non-context source independently supports it.
    """
    context_only = {
        "FUTURES_VWAP_CONTEXT_ONLY",
        "OI_PUT_WALL_POTENTIAL_ONLY",
        "OI_CALL_WALL_POTENTIAL_ONLY",
        "OI_PUT_CONTEXT",
        "OI_CALL_CONTEXT",
        "NIFTY_50_GRID",
    }
    sources = {part.strip() for part in level.source.split("+") if part.strip()}
    return bool(sources - context_only)

def _thesis_level_quality(level: PriceLevel) -> float:
    """Rank levels for durable session-thesis support/resistance.

    15m and 3m structure outrank one-minute noise. OI may strengthen a clustered
    level but an OI-only wall is never allowed to become the sole thesis anchor.
    """
    source = str(level.source)
    score = float(level.strength)
    if "15M_CONTEXT" in source:
        score += 1.00
    if "3M_SWING" in source:
        score += 0.70
    if "OPENING_RANGE_15M" in source:
        score += 0.65
    if "SESSION_LOW" in source or "SESSION_HIGH" in source:
        score += 0.45
    if "OI_" in source and _level_has_structural_provenance(level):
        score += 0.25
    if "1M_SWING" in source and "3M_SWING" not in source and "15M_CONTEXT" not in source:
        score -= 0.30
    return score


def _best_thesis_level(
    levels: Sequence[PriceLevel], side: str, spot: float, config: Config,
    *, max_distance: Optional[float] = None,
) -> Optional[PriceLevel]:
    side = side.upper()
    if side not in {"SUPPORT", "RESISTANCE"}:
        return None
    max_distance = float(max_distance if max_distance is not None else max(config.trend_target2_max_points, 135.0))
    candidates: list[PriceLevel] = []
    for level in levels:
        if level.side != side or level.strength < config.thesis_min_level_strength:
            continue
        if not _level_has_structural_provenance(level):
            continue
        distance = (spot - level.price) if side == "SUPPORT" else (level.price - spot)
        if distance < -2.0 or distance > max_distance:
            continue
        candidates.append(level)
    if not candidates:
        return None
    # Prefer the closest durable level; quality breaks ties and avoids promoting
    # a weak one-minute pivot over a nearby 3m/15m cluster.
    return min(candidates, key=lambda level: (
        max(0.0, (spot - level.price) if side == "SUPPORT" else (level.price - spot)),
        -_thesis_level_quality(level),
    ))


def build_oi_structure_context(oi: Mapping[str, Any], spot: float, config: Config) -> dict[str, Any]:
    """Translate strike OI into location-aware support/resistance evidence.

    A global bullish/bearish OI score is not enough for NIFTY. The important
    question is *where* writers are active relative to current price and to the
    support/resistance that the market is testing. This helper intentionally
    separates support strength from break pressure.
    """
    raw_levels = oi.get("oi_levels") if isinstance(oi.get("oi_levels"), list) else []
    levels = [x for x in raw_levels if isinstance(x, Mapping)]
    strikes = sorted({float(x.get("strike")) for x in levels if x.get("strike") is not None})
    diffs = [b - a for a, b in zip(strikes, strikes[1:]) if b > a]
    step = median(diffs) if diffs else float(config.target_grid_points or 50.0)
    near = [x for x in levels if abs(float(x.get("strike") or 0.0) - spot) <= max(step * 1.55, 75.0)]

    def finite(value: Any, default: float = 0.0) -> float:
        try:
            number = float(value)
            return number if math.isfinite(number) else default
        except (TypeError, ValueError, OverflowError):
            return default

    support_rows: list[dict[str, Any]] = []
    resistance_rows: list[dict[str, Any]] = []
    bearish_break_rows: list[dict[str, Any]] = []
    bullish_break_rows: list[dict[str, Any]] = []
    source_status = str(oi.get("source_refresh_status") or "SUCCESS").upper()
    current_delta_available = oi.get("current_snapshot_delta_available")
    try:
        oi_age = float(oi.get("oi_age_seconds") or 0.0)
    except (TypeError, ValueError, OverflowError):
        oi_age = float(config.max_oi_age_seconds + 1)
    fresh = (
        bool(oi.get("compared_to_previous_successful_snapshot"))
        and source_status == "SUCCESS"
        and current_delta_available is not False
        and oi_age <= config.max_oi_age_seconds
    )

    for row in near:
        strike = finite(row.get("strike"))
        if strike <= 0:
            continue
        put_rel = _clamp(finite(row.get("put_relative_oi")), 0.0, 1.0)
        call_rel = _clamp(finite(row.get("call_relative_oi")), 0.0, 1.0)
        put_writer = _clamp(finite(row.get("put_writer_strength") or row.get("put_support_flow_strength")), 0.0, 1.0)
        call_writer = _clamp(finite(row.get("call_writer_strength") or row.get("call_resistance_flow_strength")), 0.0, 1.0)
        put_delta_pct = finite(row.get("put_delta_oi_pct_snapshot"))
        call_delta_pct = finite(row.get("call_delta_oi_pct_snapshot"))
        put_flow = str(row.get("put_flow") or "NO_FLOW_EVIDENCE")
        call_flow = str(row.get("call_flow") or "NO_FLOW_EVIDENCE")
        proximity = max(0.0, 1.0 - abs(strike - spot) / max(step * 1.6, 1.0))

        if strike <= spot + 0.35 * step:
            support_score = _clamp((0.52 * put_rel + 0.48 * put_writer) * (0.75 + 0.25 * proximity), 0.0, 1.0)
            support_rows.append({"strike": strike, "score": support_score, "put_relative_oi": put_rel,
                                 "put_writer_strength": put_writer, "put_flow": put_flow,
                                 "put_delta_oi_pct": put_delta_pct})
            if fresh:
                call_write_component = max(call_writer, min(1.0, max(call_delta_pct, 0.0) / max(config.oi_material_threshold_pct * 2.5, 1e-9)))
                put_unwind_component = min(1.0, max(-put_delta_pct, 0.0) / max(config.oi_material_threshold_pct * 2.5, 1e-9))
                bearish_break = _clamp((0.58 * call_write_component + 0.42 * put_unwind_component) * (0.70 + 0.30 * proximity), 0.0, 1.0)
                bearish_break_rows.append({"strike": strike, "score": bearish_break,
                                           "call_writer_strength": call_writer, "call_delta_oi_pct": call_delta_pct,
                                           "put_delta_oi_pct": put_delta_pct, "call_flow": call_flow, "put_flow": put_flow})

        if strike >= spot - 0.35 * step:
            resistance_score = _clamp((0.52 * call_rel + 0.48 * call_writer) * (0.75 + 0.25 * proximity), 0.0, 1.0)
            resistance_rows.append({"strike": strike, "score": resistance_score, "call_relative_oi": call_rel,
                                    "call_writer_strength": call_writer, "call_flow": call_flow,
                                    "call_delta_oi_pct": call_delta_pct})
            if fresh:
                put_write_component = max(put_writer, min(1.0, max(put_delta_pct, 0.0) / max(config.oi_material_threshold_pct * 2.5, 1e-9)))
                call_unwind_component = min(1.0, max(-call_delta_pct, 0.0) / max(config.oi_material_threshold_pct * 2.5, 1e-9))
                bullish_break = _clamp((0.58 * put_write_component + 0.42 * call_unwind_component) * (0.70 + 0.30 * proximity), 0.0, 1.0)
                bullish_break_rows.append({"strike": strike, "score": bullish_break,
                                           "put_writer_strength": put_writer, "put_delta_oi_pct": put_delta_pct,
                                           "call_delta_oi_pct": call_delta_pct, "call_flow": call_flow, "put_flow": put_flow})

    best_support = max(support_rows, key=lambda x: x["score"], default=None)
    best_resistance = max(resistance_rows, key=lambda x: x["score"], default=None)
    bear_break = max(bearish_break_rows, key=lambda x: x["score"], default=None)
    bull_break = max(bullish_break_rows, key=lambda x: x["score"], default=None)
    return {
        "strike_step": step,
        "directional_raw": str(oi.get("raw_label") or oi.get("label") or "MISSING").upper(),
        "directional_confidence": float(oi.get("confidence") or 0.0),
        "support": best_support,
        "resistance": best_resistance,
        "supportive_bullish_score": round(float((best_support or {}).get("score") or 0.0), 5),
        "supportive_bearish_score": round(float((best_resistance or {}).get("score") or 0.0), 5),
        "bearish_break_pressure": round(float((bear_break or {}).get("score") or 0.0), 5),
        "bullish_break_pressure": round(float((bull_break or {}).get("score") or 0.0), 5),
        "bearish_break_detail": bear_break,
        "bullish_break_detail": bull_break,
        "fresh_snapshot": fresh,
    }


def _futures_direction_signal(futures: Mapping[str, Any]) -> float:
    return {
        "LONG_BUILDUP_BULLISH": 1.0,
        "SHORT_COVERING_BULLISH": 0.75,
        "SHORT_BUILDUP_BEARISH": -1.0,
        "LONG_UNWINDING_BEARISH": -0.80,
    }.get(str(futures.get("futures_oi_signal") or "").upper(), 0.0)


def update_market_thesis(
    previous: Optional[Mapping[str, Any]], spot: float, structure: Mapping[str, Any],
    levels: Sequence[PriceLevel], oi_structure: Mapping[str, Any], futures: Mapping[str, Any],
    bars_3m: Sequence[Candle], now: datetime, config: Config,
) -> dict[str, Any]:
    """Maintain a persistent session thesis that changes only on structural evidence.

    Short-term opposite momentum is a pullback/support test until a defended
    support/resistance is actually accepted through. This is the central v109
    change that prevents buying PE into intact support (and vice versa).
    """
    now = now.astimezone(IST)
    d1 = str(structure.get("execution_direction") or "UNKNOWN").upper()
    d3 = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    c1 = _clamp(float(structure.get("execution_confidence") or 0.0), 0.0, 1.0)
    c3 = _clamp(float(structure.get("execution_3m_confidence") or 0.0), 0.0, 1.0)
    d15 = str(structure.get("market_context_15m_bias") or "UNKNOWN").upper()
    c15 = _clamp(float(structure.get("market_context_15m_confidence") or 0.0), 0.0, 1.0)
    atr1 = max(float(structure.get("atr_1m") or 0.0), 1.0)
    buffer = max(3.0, config.thesis_break_buffer_atr * atr1)
    test_zone = max(5.0, config.thesis_test_zone_atr * atr1)
    futures_signal = _futures_direction_signal(futures)
    raw_oi = str((oi_structure or {}).get("raw_label") or "").upper()

    existing = dict(previous) if isinstance(previous, Mapping) else {}
    existing_direction = str(existing.get("direction") or "").upper()
    if existing_direction not in {"BULLISH", "BEARISH"}:
        existing_direction = ""

    support = _best_thesis_level(levels, "SUPPORT", spot, config)
    resistance = _best_thesis_level(levels, "RESISTANCE", spot, config)

    def level_payload(level: Optional[PriceLevel]) -> tuple[Optional[float], Optional[str], Optional[float]]:
        if level is None:
            return None, None, None
        return float(level.price), str(level.source), float(level.strength)

    # Establish the first directional thesis from price plus one independent
    # derivative/context input. This allows the 09:21 opening discovery without
    # requiring a mature 15-minute candle.
    if not existing_direction:
        aligned = d1 if d1 == d3 and d1 in {"BULLISH", "BEARISH"} else ""
        if aligned:
            sign = _direction_sign(aligned)
            oi_raw = str((oi_structure or {}).get("directional_raw") or "").upper()
            independent = futures_signal * sign > 0.35 or oi_raw == aligned or d15 == aligned
            strong_price = min(c1, c3) >= 0.68
            if independent or strong_price:
                state_name = "BULL_TREND" if aligned == "BULLISH" else "BEAR_TREND"
                sup_p, sup_s, sup_strength = level_payload(support)
                res_p, res_s, res_strength = level_payload(resistance)
                return {
                    "direction": aligned, "state": state_name,
                    "confidence": round(_clamp(0.44 * c1 + 0.46 * c3 + 0.10 * (c15 if d15 == aligned else 0.0), 0.0, 1.0), 4),
                    "established_at": now.isoformat(), "updated_at": now.isoformat(),
                    "anchor_support": sup_p, "anchor_support_source": sup_s, "anchor_support_strength": sup_strength,
                    "anchor_resistance": res_p, "anchor_resistance_source": res_s, "anchor_resistance_strength": res_strength,
                    "break_pending_at": None, "break_confirmed": False, "broken_level": None,
                    "reason": "OPENING_OR_FRESH_PRICE_STRUCTURE_WITH_INDEPENDENT_CONFIRMATION",
                    "reclaim_confirmed": False,
                }
        return {
            "direction": "RANGE", "state": "RANGE", "confidence": 0.0,
            "established_at": existing.get("established_at") or now.isoformat(), "updated_at": now.isoformat(),
            "anchor_support": float(support.price) if support else None,
            "anchor_support_source": support.source if support else None,
            "anchor_support_strength": support.strength if support else None,
            "anchor_resistance": float(resistance.price) if resistance else None,
            "anchor_resistance_source": resistance.source if resistance else None,
            "anchor_resistance_strength": resistance.strength if resistance else None,
            "break_pending_at": None, "break_confirmed": False, "broken_level": None,
            "reason": "NO_DURABLE_DIRECTIONAL_THESIS_YET", "reclaim_confirmed": False,
        }

    direction = existing_direction
    state_before = str(existing.get("state") or ("BULL_TREND" if direction == "BULLISH" else "BEAR_TREND"))
    anchor_support = existing.get("anchor_support")
    anchor_resistance = existing.get("anchor_resistance")
    anchor_support_source = existing.get("anchor_support_source")
    anchor_resistance_source = existing.get("anchor_resistance_source")
    anchor_support_strength = existing.get("anchor_support_strength")
    anchor_resistance_strength = existing.get("anchor_resistance_strength")

    # Ratchet thesis anchors only in the direction of progress; never loosen a
    # bullish support downward or bearish resistance upward during the same thesis.
    if support is not None and (anchor_support is None or float(support.price) > float(anchor_support) + max(1.0, 0.08 * atr1)):
        anchor_support, anchor_support_source, anchor_support_strength = float(support.price), support.source, support.strength
    if resistance is not None and (anchor_resistance is None or float(resistance.price) < float(anchor_resistance) - max(1.0, 0.08 * atr1)):
        anchor_resistance, anchor_resistance_source, anchor_resistance_strength = float(resistance.price), resistance.source, resistance.strength

    latest3 = bars_3m[-1] if bars_3m else None
    prev3 = bars_3m[-2] if len(bars_3m) >= 2 else None
    break_pending_at = existing.get("break_pending_at")
    broken_level = None
    break_confirmed = False
    reclaim_confirmed = False
    reason = "THESIS_PERSISTS"

    if direction == "BULLISH":
        support_level = float(anchor_support) if anchor_support is not None else None
        near_support = support_level is not None and spot <= support_level + test_zone
        hard_break = bool(support_level is not None and latest3 is not None and latest3.close < support_level - buffer and spot < support_level - 0.50 * buffer)
        accepted = bool(hard_break and prev3 is not None and prev3.close < support_level - 0.50 * buffer)
        derivatives_break = (
            hard_break
            and float(oi_structure.get("bearish_break_pressure") or 0.0) >= config.thesis_oi_break_score_min
            and futures_signal <= -0.50
        )
        if hard_break and not (accepted or derivatives_break):
            break_pending_at = (latest3.start + timedelta(minutes=3)).isoformat() if latest3 else now.isoformat()
        elif not hard_break:
            break_pending_at = None
        if accepted or derivatives_break:
            break_confirmed = True
            broken_level = support_level
            direction = "BEARISH"
            state = "REVERSAL_PENDING_BEAR"
            reason = "BULL_SUPPORT_ACCEPTED_BELOW" if accepted else "BULL_SUPPORT_BROKEN_WITH_OI_FUTURES_MIGRATION"
            anchor_resistance = support_level
            anchor_resistance_source = f"BROKEN_SUPPORT|{anchor_support_source or 'STRUCTURE'}"
            anchor_resistance_strength = max(float(anchor_support_strength or 0.0), config.thesis_min_level_strength)
            # Start the new bearish thesis with the nearest lower support as objective context.
            new_support = _best_thesis_level(levels, "SUPPORT", spot, config)
            if new_support is not None:
                anchor_support, anchor_support_source, anchor_support_strength = new_support.price, new_support.source, new_support.strength
        else:
            if state_before in {"BULL_SUPPORT_TEST", "BULL_PULLBACK"} and d1 == d3 == "BULLISH":
                reclaim_confirmed = True
            if hard_break:
                state = "BULL_SUPPORT_TEST"
                reason = "SUPPORT_BREAK_PENDING_CONFIRMATION"
            elif near_support and d1 in {"BEARISH", "MIXED"}:
                state = "BULL_SUPPORT_TEST"
                reason = "BEARISH_OR_MIXED_PRICE_ACTION_AT_INTACT_SUPPORT"
            elif d1 == d3 == "BEARISH":
                state = "BULL_PULLBACK"
                reason = "OPPOSITE_1M_3M_IS_PULLBACK_UNTIL_SUPPORT_BREAKS"
            elif d1 == d3 == "BULLISH":
                state = "BULL_TREND"
                reason = "BULL_STRUCTURE_RESUMED" if reclaim_confirmed else "BULL_STRUCTURE_CONTINUES"
            else:
                state = "BULL_PULLBACK" if d3 == "BEARISH" else "BULL_TREND"
    else:
        resistance_level = float(anchor_resistance) if anchor_resistance is not None else None
        near_resistance = resistance_level is not None and spot >= resistance_level - test_zone
        hard_break = bool(resistance_level is not None and latest3 is not None and latest3.close > resistance_level + buffer and spot > resistance_level + 0.50 * buffer)
        accepted = bool(hard_break and prev3 is not None and prev3.close > resistance_level + 0.50 * buffer)
        derivatives_break = (
            hard_break
            and float(oi_structure.get("bullish_break_pressure") or 0.0) >= config.thesis_oi_break_score_min
            and futures_signal >= 0.50
        )
        if hard_break and not (accepted or derivatives_break):
            break_pending_at = (latest3.start + timedelta(minutes=3)).isoformat() if latest3 else now.isoformat()
        elif not hard_break:
            break_pending_at = None
        if accepted or derivatives_break:
            break_confirmed = True
            broken_level = resistance_level
            direction = "BULLISH"
            state = "REVERSAL_PENDING_BULL"
            reason = "BEAR_RESISTANCE_ACCEPTED_ABOVE" if accepted else "BEAR_RESISTANCE_BROKEN_WITH_OI_FUTURES_MIGRATION"
            anchor_support = resistance_level
            anchor_support_source = f"BROKEN_RESISTANCE|{anchor_resistance_source or 'STRUCTURE'}"
            anchor_support_strength = max(float(anchor_resistance_strength or 0.0), config.thesis_min_level_strength)
            new_resistance = _best_thesis_level(levels, "RESISTANCE", spot, config)
            if new_resistance is not None:
                anchor_resistance, anchor_resistance_source, anchor_resistance_strength = new_resistance.price, new_resistance.source, new_resistance.strength
        else:
            if state_before in {"BEAR_RESISTANCE_TEST", "BEAR_PULLBACK"} and d1 == d3 == "BEARISH":
                reclaim_confirmed = True
            if hard_break:
                state = "BEAR_RESISTANCE_TEST"
                reason = "RESISTANCE_BREAK_PENDING_CONFIRMATION"
            elif near_resistance and d1 in {"BULLISH", "MIXED"}:
                state = "BEAR_RESISTANCE_TEST"
                reason = "BULLISH_OR_MIXED_PRICE_ACTION_AT_INTACT_RESISTANCE"
            elif d1 == d3 == "BULLISH":
                state = "BEAR_PULLBACK"
                reason = "OPPOSITE_1M_3M_IS_PULLBACK_UNTIL_RESISTANCE_BREAKS"
            elif d1 == d3 == "BEARISH":
                state = "BEAR_TREND"
                reason = "BEAR_STRUCTURE_RESUMED" if reclaim_confirmed else "BEAR_STRUCTURE_CONTINUES"
            else:
                state = "BEAR_PULLBACK" if d3 == "BULLISH" else "BEAR_TREND"

    aligned_conf = (c1 + c3) / 2.0 if d1 == d3 and d1 in {"BULLISH", "BEARISH"} else max(c15 * 0.65, 0.35)
    return {
        "direction": direction, "state": state, "previous_state": state_before,
        "confidence": round(_clamp(aligned_conf, 0.0, 1.0), 4),
        "established_at": existing.get("established_at") or now.isoformat(), "updated_at": now.isoformat(),
        "anchor_support": anchor_support, "anchor_support_source": anchor_support_source,
        "anchor_support_strength": anchor_support_strength,
        "anchor_resistance": anchor_resistance, "anchor_resistance_source": anchor_resistance_source,
        "anchor_resistance_strength": anchor_resistance_strength,
        "break_pending_at": break_pending_at, "break_confirmed": break_confirmed,
        "broken_level": broken_level, "reason": reason, "reclaim_confirmed": reclaim_confirmed,
        "break_buffer_points": buffer, "test_zone_points": test_zone,
    }



def candle_freshness(candles: Sequence[Candle], now: datetime) -> dict[str, Any]:
    """Compare with the last minute fully elapsed at scan start, in exchange time."""
    now = now.astimezone(IST)
    expected = now.replace(second=0, microsecond=0) - timedelta(minutes=1)
    latest = candles[-1].start.astimezone(IST) if candles else None
    return {"expected_start": expected.isoformat(),
            "latest_start": latest.isoformat() if latest else None,
            "latest_expected_available": latest == expected,
            "missing_latest_minutes": max(0, int((expected - latest).total_seconds() // 60)) if latest else None}


def local_reversal_watch(candles: Sequence[Candle], levels: Sequence[PriceLevel],
                         structure: Mapping[str, Any], thesis: Mapping[str, Any]) -> dict[str, Any]:
    """Diagnostic local level rejection; never authorizes or backdates a trade."""
    if len(candles) < 3:
        return {"status": "INSUFFICIENT_CANDLES"}
    current, previous = candles[-1], candles[-2]
    atr1 = float(structure.get("atr_1m") or 0.0)
    if not math.isfinite(atr1) or atr1 <= 0:
        return {"status": "ATR_UNAVAILABLE"}
    band = max(2.0, 0.2 * atr1)
    recent = candles[-6:]
    candidates = []
    for level in levels:
        if level.strength < 1.0 or "FUTURES_VWAP_CONTEXT_ONLY" in level.source:
            continue
        if level.side == "RESISTANCE":
            touched = any(abs(c.high - level.price) <= band for c in recent)
            rejected = current.close < current.open and current.close < previous.low and current.close < level.price - 0.08 * atr1
            direction = "BEARISH"
            invalidation = max(c.high for c in recent) + max(1.0, 0.08 * atr1)
        elif level.side == "SUPPORT":
            touched = any(abs(c.low - level.price) <= band for c in recent)
            rejected = current.close > current.open and current.close > previous.high and current.close > level.price + 0.08 * atr1
            direction = "BULLISH"
            invalidation = min(c.low for c in recent) - max(1.0, 0.08 * atr1)
        else:
            continue
        if touched and rejected:
            candidates.append((abs(current.close - level.price), level, direction, invalidation))
    if not candidates:
        return {"status": "NO_LOCAL_REJECTION"}
    _, level, direction, invalidation = min(candidates, key=lambda x: x[0])
    return {"status": "SHADOW_ONLY", "direction": direction, "level": level.price,
            "level_source": level.source, "trigger": current.close,
            "invalidation_reference": invalidation, "confirmed_at": current.close_time.isoformat(),
            "thesis_direction": thesis.get("direction"),
            "note": "Research candidate only; not an entry or trade recommendation"}


def evaluate_early_oi_reversal(candles: Sequence[Candle], levels: Sequence[PriceLevel],
                               structure: Mapping[str, Any], thesis: Mapping[str, Any],
                               oi: Mapping[str, Any], oi_structure: Mapping[str, Any],
                               futures: Mapping[str, Any]) -> tuple[Optional[Setup], dict[str, Any]]:
    """Local reversal hypothesis: causal price rejection plus fresh strike OI.

    Thresholds are provisional research parameters, not calibrated probabilities.
    Candidates are recomputed on every run and never carried forward as watches.
    """
    if len(_contiguous_tail(candles, 1)) < 6:
        return None, {"status": "BLOCKED", "reason": "RECENT_CANDLE_GAP_OR_INSUFFICIENT"}
    watch = local_reversal_watch(candles, levels, structure, thesis)
    out = {"status": "BLOCKED", "reason": "NO_PRICE_REJECTION", "price_watch": watch}
    if watch.get("status") != "SHADOW_ONLY":
        return None, out
    direction = str(watch["direction"])
    out["direction"] = direction
    if not oi_structure.get("fresh_snapshot"):
        out["reason"] = "OI_SNAPSHOT_NOT_FRESH"
        return None, out
    if str(structure.get("execution_direction") or "") != direction:
        out["reason"] = "ONE_MINUTE_DIRECTION_NOT_ALIGNED"
        return None, out
    if float(structure.get("execution_confidence") or 0.0) < 0.55:
        out["reason"] = "ONE_MINUTE_CONFIDENCE_WEAK"
        return None, out
    fsignal = _futures_direction_signal(futures)
    if fsignal * _direction_sign(direction) < -0.35:
        out["reason"] = "FUTURES_OPPOSE"
        return None, out
    raw = str(oi.get("raw_label") or "MISSING")
    if raw in {"BULLISH", "BEARISH"} and raw != direction and float(oi.get("confidence") or 0) >= 0.80:
        out["reason"] = "STRONG_GLOBAL_OI_OPPOSES"
        return None, out
    rows = [r for r in oi.get("oi_levels", []) if isinstance(r, Mapping) and r.get("strike") is not None]
    if not rows:
        out["reason"] = "STRIKE_OI_UNAVAILABLE"
        return None, out
    level = float(watch["level"])
    row = min(rows, key=lambda r: abs(float(r["strike"]) - level))
    step = float(oi_structure.get("strike_step") or 50.0)
    if not math.isfinite(step) or step <= 0 or abs(float(row["strike"]) - level) > step * 0.55:
        out["reason"] = "NO_OI_AT_REJECTION_LEVEL"
        return None, out
    prefix = "call" if direction == "BEARISH" else "put"
    try:
        delta = float(row.get(prefix + "_delta_oi_pct_snapshot"))
        writer = float(row.get(prefix + "_writer_strength") or 0)
        relative = float(row.get(prefix + "_relative_oi") or 0)
    except (TypeError, ValueError, OverflowError):
        out["reason"] = "STRIKE_OI_INCOMPLETE"
        return None, out
    out["strike_evidence"] = {"strike": row["strike"], "oi_change_pct": delta,
                              "writer_strength": writer, "relative_oi": relative,
                              "flow": row.get(prefix + "_flow")}
    if not all(math.isfinite(x) for x in (delta, writer, relative)) or delta <= 0 or writer < 0.35 or relative < 0.25:
        out["reason"] = "STRIKE_WRITING_NOT_CONFIRMED"
        return None, out
    out.update(status="CANDIDATE", reason="PRICE_REJECTION_WITH_FRESH_STRIKE_OI")
    setup = Setup(kind="EARLY_OI_LEVEL_REVERSAL", direction=direction,
                  trigger=float(watch["trigger"]), invalidation=float(watch["invalidation_reference"]),
                  confirmed_at=candles[-1].close_time, source_level=level,
                  source=str(watch["level_source"]) + "|FRESH_STRIKE_OI",
                  price_confidence=min(0.95, max(0.55, float(structure.get("execution_confidence") or 0))))
    return setup, out


def validate_early_target_room(setup: Setup, spot: float, plan: Mapping[str, Any],
                               levels: Sequence[PriceLevel], config: Config) -> None:
    """Do not project through the nearest meaningful opposing structural level."""
    side = "SUPPORT" if setup.direction == "BEARISH" else "RESISTANCE"
    nearby = [x for x in levels if x.side == side and x.strength >= max(config.min_level_strength, 1.5)
              and _level_has_structural_provenance(x)
              and ((x.price < spot) if setup.direction == "BEARISH" else (x.price > spot))]
    if not nearby:
        raise ScannerError("EARLY_TARGET_STRUCTURE_UNAVAILABLE", "No meaningful opposing price structure available for early reversal target")
    nearest = min(nearby, key=lambda x: abs(x.price - spot))
    distance = abs(nearest.price - spot)
    risk = float(plan["risk_points"])
    if distance / risk < config.min_underlying_rr:
        raise ScannerError("EARLY_TARGET_ROOM_INSUFFICIENT", f"Nearest opposing structure offers only {distance/risk:.2f}R")
    if abs(float(plan["t1_underlying"]) - spot) > distance + 1e-6:
        raise ScannerError("EARLY_TARGET_BEYOND_STRUCTURE", "Planned target is beyond nearest opposing structural level")


def v111_price_candidate(candles: Sequence[Candle], levels: Sequence[PriceLevel],
                          structure: Mapping[str, Any], thesis: Mapping[str, Any]) -> tuple[Optional[Setup], dict[str, Any]]:
    """Generate a current-candle hypothesis without making a trade decision."""
    recent = _contiguous_tail(candles, 1)
    if len(recent) < 6:
        return None, {"reason": "INSUFFICIENT_CONTIGUOUS_CANDLES"}
    atr1 = float(structure.get("atr_1m") or 0)
    if not math.isfinite(atr1) or atr1 <= 0:
        return None, {"reason": "ATR_UNAVAILABLE"}
    current, previous = recent[-1], recent[-2]
    # Use the prior five bars for the test; exclude the signal candle to avoid
    # promoting a level touched for the first time by the signal itself.
    prior = recent[-6:-1]
    band = max(2.0, 0.20 * atr1)
    buffer = max(1.0, 0.08 * atr1)
    hypotheses: list[Setup] = []
    for level in levels:
        if level.strength < 1.0 or "FUTURES_VWAP_CONTEXT_ONLY" in level.source:
            continue
        if level.side == "RESISTANCE" and any(abs(c.high-level.price) <= band for c in prior):
            if current.close < current.open and current.close < previous.low and current.close < level.price - buffer:
                hypotheses.append(Setup("V111_REVERSAL", "BEARISH", current.close,
                                        max(c.high for c in recent[-6:]) + buffer, current.close_time,
                                        level.price, level.source, 0.65))
        if level.side == "SUPPORT" and any(abs(c.low-level.price) <= band for c in prior):
            if current.close > current.open and current.close > previous.high and current.close > level.price + buffer:
                hypotheses.append(Setup("V111_REVERSAL", "BULLISH", current.close,
                                        min(c.low for c in recent[-6:]) - buffer, current.close_time,
                                        level.price, level.source, 0.65))
    d1 = str(structure.get("execution_direction") or "")
    d3 = str(structure.get("execution_3m_direction") or "")
    d3conf = float(structure.get("execution_3m_confidence") or 0)
    thesis_direction = str(thesis.get("direction") or "")
    for direction in ("BEARISH", "BULLISH"):
        strong_opposite = d3 in {"BULLISH", "BEARISH"} and d3 != direction and d3conf >= 0.70
        if d1 != direction or strong_opposite:
            continue
        if thesis_direction != direction and d3 != direction:
            continue
        if direction == "BEARISH":
            pullback = any(c.close > c.open for c in recent[-4:-1])
            trigger = current.close < current.open and current.close < previous.low
            invalid = max(c.high for c in recent[-4:]) + buffer
        else:
            pullback = any(c.close < c.open for c in recent[-4:-1])
            trigger = current.close > current.open and current.close > previous.high
            invalid = min(c.low for c in recent[-4:]) - buffer
        if pullback and trigger:
            hypotheses.append(Setup("V111_CONTINUATION", direction, current.close, invalid,
                                    current.close_time, None, "RECENT_1M_PULLBACK", 0.65))
    if not hypotheses:
        return None, {"reason": "NO_PRICE_PATTERN"}
    # Prefer nearest actual reversal zone; otherwise the continuation setup.
    hypotheses.sort(key=lambda q: (q.kind != "V111_REVERSAL", abs((q.source_level or q.trigger) - q.trigger)))
    return hypotheses[0], {"reason": "PRICE_CANDIDATE", "candidates": [json_safe(x) for x in hypotheses[:4]]}


def v111_oi_confirmation(setup: Setup, oi: Mapping[str, Any], oi_structure: Mapping[str, Any],
                         futures: Mapping[str, Any], spot: float) -> dict[str, Any]:
    """Require fresh nearby matched OI and a compatible inferred price/OI pattern."""
    result: dict[str, Any] = {"approved": False, "reason": "OI_SNAPSHOT_NOT_FRESH"}
    if not oi_structure.get("fresh_snapshot") or oi.get("source_refresh_status") != "SUCCESS":
        return result
    direction = setup.direction
    sign = _direction_sign(direction)
    fsignal = _futures_direction_signal(futures)
    if fsignal * sign <= -0.75:
        return {"approved": False, "reason": "FUTURES_STRONGLY_OPPOSE", "futures_signal": fsignal}
    raw = str(oi.get("raw_label") or "MISSING").upper()
    if raw in {"BULLISH", "BEARISH"} and raw != direction and float(oi.get("confidence") or 0) >= 0.80:
        return {"approved": False, "reason": "STRONG_GLOBAL_OI_OPPOSES", "oi_raw": raw}
    permitted = ({"CALL_WRITING_LIKELY", "CALL_LONG_UNWINDING_LIKELY", "PUT_LONG_BUILDUP_LIKELY", "PUT_SHORT_COVERING_LIKELY"}
                 if direction == "BEARISH" else
                 {"PUT_WRITING_LIKELY", "PUT_LONG_UNWINDING_LIKELY", "CALL_LONG_BUILDUP_LIKELY", "CALL_SHORT_COVERING_LIKELY"})
    step = float(oi_structure.get("strike_step") or 50.0)
    if not math.isfinite(step) or step <= 0:
        return {"approved": False, "reason": "INVALID_STRIKE_GRID"}
    reference = float(setup.source_level if setup.source_level is not None else spot)
    matched = []
    for row in oi.get("oi_levels", []):
        if not isinstance(row, Mapping):
            continue
        try:
            strike = float(row.get("strike"))
        except (TypeError, ValueError):
            continue
        if not math.isfinite(strike) or abs(strike-reference) > step * 0.55:
            continue
        for field in ("call_flow", "put_flow"):
            flow = str(row.get(field) or "")
            try:
                delta_pct = float(row.get(field.replace("_flow", "_delta_oi_pct_snapshot")))
            except (TypeError, ValueError, OverflowError):
                continue
            increasing = flow in {"CALL_WRITING_LIKELY", "CALL_LONG_BUILDUP_LIKELY", "PUT_WRITING_LIKELY", "PUT_LONG_BUILDUP_LIKELY"}
            decreasing = flow in {"CALL_LONG_UNWINDING_LIKELY", "CALL_SHORT_COVERING_LIKELY", "PUT_LONG_UNWINDING_LIKELY", "PUT_SHORT_COVERING_LIKELY"}
            signs_match = (increasing and delta_pct > 0) or (decreasing and delta_pct < 0)
            if flow in permitted and math.isfinite(delta_pct) and signs_match:
                matched.append({"strike": strike, "flow": flow, "oi_change_pct": delta_pct})
    if not matched:
        return {"approved": False, "reason": "NO_SUPPORTING_STRIKE_OI_FLOW", "reference_level": reference}
    return {"approved": True, "reason": "PRICE_AND_STRIKE_OI_ALIGNED", "matched_flows": matched,
            "oi_raw": raw, "futures_signal": fsignal, "futures_available": fsignal != 0}


def v111_risk_plan(entry: float, setup: Setup, structure: Mapping[str, Any], levels: Sequence[PriceLevel],
                   config: Config, now: datetime, thesis: Mapping[str, Any]) -> dict[str, Any]:
    """Initial risk capped at the configured maximum and first real opposing obstacle."""
    atr1 = float(structure.get("atr_1m") or 0)
    if not math.isfinite(atr1) or atr1 <= 0:
        raise ScannerError("ATR_UNAVAILABLE", "ATR required for risk plan")
    direction = setup.direction
    raw_risk = (entry-setup.invalidation) if direction == "BULLISH" else (setup.invalidation-entry)
    if raw_risk <= 0 or not math.isfinite(raw_risk):
        raise ScannerError("INVALID_STOP", "Invalidation must remain on the risk side of the current quote")
    buffer = max(1.0, config.stop_buffer_atr_fraction*atr1)
    risk = max(raw_risk + buffer, config.minimum_stop_points, config.min_initial_stop_atr*atr1)
    if risk > config.max_initial_stop_points + 1e-9:
        raise ScannerError("STOP_TOO_WIDE", f"Risk {risk:.2f} exceeds maximum {config.max_initial_stop_points:.2f} NIFTY points")
    stop = entry-risk if direction == "BULLISH" else entry+risk
    side = "RESISTANCE" if direction == "BULLISH" else "SUPPORT"
    obstacles = [x for x in levels if x.side == side and x.strength >= config.min_level_strength
                 and "FUTURES_VWAP_CONTEXT_ONLY" not in x.source
                 and ((x.price > entry) if direction == "BULLISH" else (x.price < entry))]
    obstacles.sort(key=lambda x: abs(x.price-entry))
    if not obstacles:
        raise ScannerError("TARGET_STRUCTURE_UNAVAILABLE", "No opposing level is available for the target")
    t1 = obstacles[0]
    distance = abs(t1.price-entry)
    if distance/risk < config.min_underlying_rr:
        raise ScannerError("TARGET_ROOM_INSUFFICIENT", f"Nearest opposing level offers {distance/risk:.2f}R, below {config.min_underlying_rr:.2f}R")
    t2 = next((x for x in obstacles[1:] if abs(x.price-t1.price) >= max(2.0, 0.2*atr1)), None)
    close_at = datetime.combine(now.astimezone(IST).date(), dtime(15,30), tzinfo=IST)
    left = (close_at-now.astimezone(IST)).total_seconds()/60
    if left < config.min_entry_minutes_to_close:
        raise ScannerError("ENTRY_TOO_CLOSE_TO_MARKET_CLOSE", f"Only {left:.1f} minutes remain")
    return {"entry_underlying": entry, "stop_underlying": stop, "initial_stop_underlying": stop,
            "risk_points": risk, "stop_buffer_points": buffer, "stop_reference_price": setup.invalidation,
            "stop_reference_source": setup.source, "stop_source": "V111_STRUCTURE_AND_ATR_BUFFER",
            "atr_1m": atr1, "atr_3m": structure.get("atr_3m"), "atr_15m": structure.get("atr_15m"),
            "t1_underlying": t1.price, "t1_source": t1.source, "t1_confluence": "NEAREST_OPPOSING_LEVEL",
            "t1_level_strength": t1.strength, "t2_underlying": t2.price if t2 else None,
            "t2_source": t2.source if t2 else None, "t2_confluence": "NEXT_OPPOSING_LEVEL" if t2 else None,
            "underlying_rr": distance/risk, "minutes_to_market_close": left,
            "target_method": "NEAREST_OPPOSING_LEVEL", "targets_fixed_at_entry": True,
            "target1_distance_points": distance, "intermediate_soft_barriers": [],
            "thesis_state_at_entry": thesis.get("state"), "thesis_direction_at_entry": thesis.get("direction")}


def detect_setup(
    candles: Sequence[Candle], levels: Sequence[PriceLevel], structure: Mapping[str, Any],
    config: Config, oi_evidence: Optional[Mapping[str, Any]] = None,
    market_thesis: Optional[Mapping[str, Any]] = None,
) -> Optional[Setup]:
    """Detect a fresh v109 entry from 1m timing inside persistent 3m/15m structure.

    A counter-trend momentum burst into intact thesis support/resistance is not a
    reversal setup. Reversal entries are created only after the thesis engine has
    confirmed a structural break.
    """
    regime = str(structure.get("regime") or "TRANSITION").upper()
    opening_mode = regime.startswith("OPENING_DISCOVERY")
    minimum_1m_bars = config.opening_min_1m_bars if opening_mode else 8
    if len(candles) < minimum_1m_bars:
        return None
    current = candles[-1]
    previous = candles[-2]
    atr1 = float(structure.get("atr_1m") or atr(candles) or 0.0)
    if atr1 <= 0:
        return None
    execution_1m = str(structure.get("execution_direction") or "UNKNOWN").upper()
    direction_3m = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    conf1 = float(structure.get("execution_confidence") or 0.0)
    conf3 = float(structure.get("execution_3m_confidence") or 0.0)
    if execution_1m not in {"BULLISH", "BEARISH"} or direction_3m != execution_1m:
        return None
    if conf1 < config.min_1m_execution_confidence or conf3 < config.min_3m_execution_confidence:
        return None
    direction = execution_1m

    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    thesis_direction = str(thesis.get("direction") or "RANGE").upper()
    thesis_state = str(thesis.get("state") or "RANGE").upper()
    # The thesis engine already decides whether support/resistance has broken.
    # Opposite price momentum alone cannot create a counter-trend entry.
    if thesis_direction == "BULLISH" and direction == "BEARISH":
        return None
    if thesis_direction == "BEARISH" and direction == "BULLISH":
        return None

    body_ok = current.close > current.open if direction == "BULLISH" else current.close < current.open
    progress_ok = current.close >= previous.close if direction == "BULLISH" else current.close <= previous.close
    if not body_ok or not progress_ok:
        return None

    micro_break = current.close > previous.high if direction == "BULLISH" else current.close < previous.low
    recent = list(candles[-4:])
    pullback_seen = any(c.close < c.open for c in recent[:-1]) if direction == "BULLISH" else any(c.close > c.open for c in recent[:-1])
    ema8 = structure.get("ema_fast_1m") if opening_mode else structure.get("ema8_1m")
    resumed_from_ema = False
    try:
        if ema8 is not None:
            ema8f = float(ema8)
            resumed_from_ema = (
                current.close > ema8f and previous.low <= ema8f + 0.25 * atr1
                if direction == "BULLISH"
                else current.close < ema8f and previous.high >= ema8f - 0.25 * atr1
            )
    except (TypeError, ValueError, OverflowError):
        resumed_from_ema = False

    # A support/resistance reclaim is stronger than a generic micro-break and is
    # deliberately allowed early so v109 can capture the 12:24-type CE reclaim.
    reclaim = False
    thesis_anchor = None
    if direction == "BULLISH" and thesis_direction == "BULLISH":
        thesis_anchor = thesis.get("anchor_support")
        try:
            reclaim = bool(thesis.get("reclaim_confirmed")) or (
                thesis_anchor is not None
                and previous.low <= float(thesis_anchor) + max(5.0, config.thesis_test_zone_atr * atr1)
                and current.close > float(thesis_anchor) + max(1.0, 0.08 * atr1)
                and (micro_break or current.close > previous.close)
            )
        except (TypeError, ValueError, OverflowError):
            reclaim = False
    elif direction == "BEARISH" and thesis_direction == "BEARISH":
        thesis_anchor = thesis.get("anchor_resistance")
        try:
            reclaim = bool(thesis.get("reclaim_confirmed")) or (
                thesis_anchor is not None
                and previous.high >= float(thesis_anchor) - max(5.0, config.thesis_test_zone_atr * atr1)
                and current.close < float(thesis_anchor) - max(1.0, 0.08 * atr1)
                and (micro_break or current.close < previous.close)
            )
        except (TypeError, ValueError, OverflowError):
            reclaim = False

    if not (micro_break or (pullback_seen and resumed_from_ema) or reclaim):
        return None

    risk_side = "SUPPORT" if direction == "BULLISH" else "RESISTANCE"
    risk_levels = [
        level for level in levels
        if level.side == risk_side
        and ((level.price < current.close) if direction == "BULLISH" else (level.price > current.close))
        and level.strength >= config.min_level_strength
        and "FUTURES_VWAP_CONTEXT_ONLY" not in level.source
    ]
    nearest = min(risk_levels, key=lambda level: abs(level.price - current.close), default=None)
    recent_low = min(c.low for c in candles[-4:])
    recent_high = max(c.high for c in candles[-4:])
    structural_invalid = recent_low if direction == "BULLISH" else recent_high
    source_level = None
    source = "RECENT_1M_STRUCTURE"

    # For thesis-continuation/reclaim entries, the defended thesis level is the
    # logical invalidation reference if it is closer/more durable than a tiny
    # one-minute swing.
    if thesis_anchor is not None:
        try:
            anchor = float(thesis_anchor)
            if direction == "BULLISH" and anchor < current.close:
                structural_invalid = max(structural_invalid, anchor)
                source_level = anchor
                source = str(thesis.get("anchor_support_source") or "MARKET_THESIS_SUPPORT")
            elif direction == "BEARISH" and anchor > current.close:
                structural_invalid = min(structural_invalid, anchor)
                source_level = anchor
                source = str(thesis.get("anchor_resistance_source") or "MARKET_THESIS_RESISTANCE")
        except (TypeError, ValueError, OverflowError):
            pass
    if nearest is not None:
        if direction == "BULLISH" and nearest.price > structural_invalid:
            structural_invalid, source_level, source = nearest.price, nearest.price, nearest.source
        elif direction == "BEARISH" and nearest.price < structural_invalid:
            structural_invalid, source_level, source = nearest.price, nearest.price, nearest.source

    buffer = max(1.0, 0.08 * atr1)
    invalidation = structural_invalid - buffer if direction == "BULLISH" else structural_invalid + buffer
    if direction == "BULLISH" and invalidation >= current.close:
        invalidation = current.close - max(config.minimum_stop_points, 0.75 * atr1)
    if direction == "BEARISH" and invalidation <= current.close:
        invalidation = current.close + max(config.minimum_stop_points, 0.75 * atr1)

    if thesis_state in {"REVERSAL_PENDING_BULL", "REVERSAL_PENDING_BEAR"}:
        kind = "STRUCTURAL_BREAK_REVERSAL_1M3M"
        context_bonus = 0.11
    elif reclaim:
        kind = "SUPPORT_RECLAIM_1M3M" if direction == "BULLISH" else "RESISTANCE_RECLAIM_1M3M"
        context_bonus = 0.14
    elif thesis_direction == direction:
        kind = "THESIS_CONTINUATION_1M3M"
        context_bonus = 0.12
    else:
        kind = "MOMENTUM_1M3M"
        context_bonus = 0.06
    confidence = min(0.97, 0.42 + 0.24 * conf1 + 0.24 * conf3 + context_bonus + (0.05 if micro_break else 0.0))
    return Setup(
        kind=kind, direction=direction, trigger=float(current.close), invalidation=float(invalidation),
        confirmed_at=current.close_time, source_level=float(source_level) if source_level is not None else None,
        source=f"{source}|1M_3M_THESIS_CONFIRMATION", price_confidence=confidence,
    )

# ---------- Risk planning and option pricing ----------
def option_quote_from_full(record: OptionRecord, raw: Mapping[str, Any]) -> OptionQuote:
    depth = raw.get("depth") or {}
    buys_raw = depth.get("buy") if isinstance(depth, dict) else []
    sells_raw = depth.get("sell") if isinstance(depth, dict) else []

    def valid_levels(values: Any) -> list[dict[str, float]]:
        levels: list[dict[str, float]] = []
        for item in values or []:
            if not isinstance(item, Mapping):
                continue
            try:
                price = float(item.get("price") or 0)
                quantity = float(item.get("quantity") or 0)
            except (TypeError, ValueError, OverflowError):
                continue
            if math.isfinite(price) and math.isfinite(quantity) and price > 0 and quantity > 0:
                levels.append({"price": price, "quantity": quantity})
        return levels

    buys = valid_levels(buys_raw)
    sells = valid_levels(sells_raw)
    bid = max((x["price"] for x in buys), default=0.0)
    ask = min((x["price"] for x in sells), default=0.0)
    bid_qty = sum(x["quantity"] for x in buys if x["price"] == bid) if bid > 0 else 0.0
    ask_qty = sum(x["quantity"] for x in sells if x["price"] == ask) if ask > 0 else 0.0

    def finite_or(value: Any, fallback: float) -> float:
        try:
            number = float(value)
            return number if math.isfinite(number) and number >= 0 else fallback
        except (TypeError, ValueError, OverflowError):
            return fallback

    ltp = finite_or(raw.get("last_price"), record.ltp)
    volume = finite_or(raw.get("volume"), record.volume)
    oi = finite_or(raw.get("oi"), record.oi)
    return OptionQuote(
        record.instrument_key, parse_datetime(raw.get("timestamp")), ltp, bid, ask, bid_qty, ask_qty,
        volume, oi, record.strike, record.side, record.expiry, record.delta, record.gamma,
        record.theta, record.vega, record.iv,
    )


def _strike_offsets_for_regime(direction: str, structure: Mapping[str, Any], config: Config) -> tuple[int, ...]:
    # Fixed ATM / one-ITM universe for all setups.
    return (0, -1) if direction == "BULLISH" else (0, 1)


def select_option_and_risk(
    direction: str, spot: float, spot_quote_time: Optional[datetime], chain_records: Sequence[OptionRecord], full_quotes: Mapping[str, Mapping[str, Any]],
    expiry: date, now: datetime, plan: Mapping[str, Any], structure: Mapping[str, Any], config: Config,
) -> dict[str, Any]:
    """Select one executable contract after direction is decided.

    Reversal/sideways: CE uses ATM-1/ATM-2, PE uses ATM+1/ATM+2 exactly as
    specified. Trend/momentum considers ATM plus one ITM step. OI is retained
    for diagnostics/liquidity context but does not determine the winning strike.
    """
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("DIRECTION_INVALID", "Option selector requires a directional setup")
    strikes = sorted({r.strike for r in chain_records})
    step_values = [b - a for a, b in zip(strikes, strikes[1:]) if b > a]
    if not step_values:
        raise ScannerError("STRIKE_GRID_INVALID", "Cannot infer strike interval from option-chain data")
    strike_step = median(step_values)
    atm = min(strikes, key=lambda value: abs(value - spot))
    side = "CE" if direction == "BULLISH" else "PE"
    offsets = _strike_offsets_for_regime(direction, structure, config)
    candidates: list[dict[str, Any]] = []
    rejections: Counter[str] = Counter()
    local_now = now.astimezone(IST)
    expiry_close = datetime.combine(expiry, dtime(15, 30), tzinfo=IST)
    minutes_to_expiry = max(0.0, (expiry_close - local_now).total_seconds() / 60.0)
    if minutes_to_expiry <= config.expected_hold_minutes:
        raise ScannerError("EXPIRY_TOO_NEAR_FOR_HOLD", f"Only {minutes_to_expiry:.1f} minutes remain to selected expiry; expected hold is {config.expected_hold_minutes:.1f} minutes")

    for offset in offsets:
        target_strike = atm + offset * strike_step
        record = min((r for r in chain_records if r.side == side), key=lambda r: abs(r.strike - target_strike), default=None)
        if record is None or abs(record.strike - target_strike) > max(0.51, strike_step * 0.15):
            rejections["STRIKE_NOT_IN_CHAIN"] += 1
            continue
        raw_quote = full_quotes.get(record.instrument_key)
        if raw_quote is None:
            rejections["QUOTE_MISSING"] += 1
            continue
        quote = option_quote_from_full(record, raw_quote)
        if quote.timestamp is None:
            rejections["QUOTE_TIMESTAMP_MISSING"] += 1
            continue
        try:
            quote_age, quote_clock_skew, quote_timestamp_status = quote_timing(quote.timestamp, local_now, error_code="OPTION_QUOTE_CLOCK_SKEW")
        except ScannerError as timestamp_exc:
            rejections[timestamp_exc.code] += 1
            continue
        if quote_age > config.max_quote_age_seconds:
            rejections["QUOTE_STALE"] += 1
            continue
        if quote.bid <= 0 or quote.ask <= 0 or quote.ask < quote.bid:
            rejections["INVALID_BID_ASK"] += 1
            continue
        if quote.bid_qty < config.min_bid_qty or quote.ask_qty < config.min_ask_qty:
            rejections["INSUFFICIENT_DEPTH"] += 1
            continue
        if quote.volume < config.min_option_volume:
            rejections["LOW_OPTION_VOLUME"] += 1
            continue
        if quote.spread_pct > config.max_spread_pct:
            rejections["SPREAD_TOO_WIDE"] += 1
            continue
        if quote.delta is None or not (config.min_abs_delta <= abs(quote.delta) <= config.max_abs_delta):
            rejections["DELTA_OUT_OF_RANGE"] += 1
            continue
        if quote.iv is None or not math.isfinite(float(quote.iv)) or not (0.1 <= quote.iv <= 500.0):
            rejections["INVALID_IV"] += 1
            continue

        mid = quote.mid
        theta_estimate = abs(quote.theta or 0.0) * config.expected_hold_minutes / 1440.0
        theta_fraction = theta_estimate / mid if mid > 0 else 1.0
        delta_score = max(0.0, 1.0 - abs(abs(quote.delta) - config.preferred_abs_delta) / 0.30)
        spread_score = max(0.0, 1.0 - quote.spread_pct / max(config.max_spread_pct, 1e-9))
        depth_score = min(1.0, math.log1p(quote.bid_qty + quote.ask_qty) / math.log1p(6000.0))
        volume_score = min(1.0, math.log1p(quote.volume) / math.log1p(100000.0))
        decay_score = max(0.0, 1.0 - min(theta_fraction, 1.0))
        gamma_score = min(1.0, max(0.0, abs(float(quote.gamma or 0.0)) / 0.0045))
        itm_steps = (-offset) if side == "CE" else offset
        # Moneyness is a small tie-breaker only; regime restrictions already
        # enforce the user's desired ITM candidates in reversal/sideways.
        moneyness_score = 1.0 if itm_steps == 1 else 0.92 if itm_steps == 0 else 0.88 if itm_steps == 2 else 0.70
        score = (0.29 * delta_score + 0.24 * spread_score + 0.14 * depth_score
                 + 0.13 * volume_score + 0.10 * decay_score + 0.06 * gamma_score
                 + 0.04 * moneyness_score)
        candidates.append({
            "instrument_key": quote.instrument_key, "strike": quote.strike,
            "side": quote.side, "expiry": quote.expiry.isoformat(),
            "trading_offset_from_atm": offset, "atm_strike": atm, "strike_interval": strike_step,
            "reference_entry_ask": quote.ask, "reference_bid": quote.bid,
            "reference_mid": mid, "spread_points": quote.ask - quote.bid,
            "spread_pct": quote.spread_pct, "bid_qty": quote.bid_qty,
            "ask_qty": quote.ask_qty, "quote_timestamp": quote.timestamp.isoformat(),
            "quote_age_seconds": quote_age, "quote_clock_skew_seconds": quote_clock_skew,
            "quote_timestamp_status": quote_timestamp_status, "ltp": quote.ltp,
            "volume": quote.volume, "oi": quote.oi, "delta": quote.delta,
            "gamma": quote.gamma, "theta": quote.theta, "vega": quote.vega,
            "iv_percent": quote.iv, "estimated_theta_decay_points_for_hold": theta_estimate,
            "estimated_theta_decay_fraction_of_mid": theta_fraction,
            "minutes_to_expiry": minutes_to_expiry,
            "selection_score": round(score, 5),
            "delta_score": round(delta_score, 5),
            "moneyness_score": round(moneyness_score, 5),
            "selection_method": "REGIME_LOCKED_EXECUTION_QUALITY_SCORE",
            "selection_regime": str(structure.get("regime") or "TRANSITION"),
            "allowed_offsets": list(offsets),
            "spot_risk_reward": plan.get("underlying_rr"),
            "_rank": (score, -quote.spread_pct, delta_score, volume_score, depth_score),
        })
    if not candidates:
        reason = rejections.most_common(1)[0][0] if rejections else "NO_VALID_OPTION_QUOTES"
        details = ", ".join(f"{key}:{value}" for key, value in rejections.most_common(5))
        raise ScannerError(reason, f"No eligible {side} contract among allowed offsets {list(offsets)}. {details}")
    candidates.sort(key=lambda candidate: candidate["_rank"], reverse=True)
    ranking = [{k: v for k, v in candidate.items() if k != "_rank"} | {"rank": rank}
               for rank, candidate in enumerate(candidates[:5], 1)]
    selected = dict(candidates[0])
    selected.pop("_rank", None)
    selected["candidate_count_passed"] = len(candidates)
    selected["candidate_count_rejected"] = sum(rejections.values())
    selected["rejection_counts"] = dict(rejections)
    selected["spot_quote_timestamp"] = spot_quote_time.isoformat() if spot_quote_time else None
    selected["candidate_ranking"] = ranking
    selected["selection_margin_vs_second"] = (
        round(float(candidates[0]["selection_score"]) - float(candidates[1]["selection_score"]), 5)
        if len(candidates) > 1 else None
    )
    return selected


# ---------- Setup authorization and single decision pipeline ----------

def stabilize_oi_evidence(evidence: dict[str, Any], state: dict[str, Any], session_date: date, expiry: date) -> None:
    """Apply 2-of-3 snapshot persistence without hiding the raw current score.

    A first opposite snapshot is labelled as a transition watch (stable label
    MIXED); two consecutive direction observations are enough to change the
    stable directional label. Raw deltas/scores are never rewritten.
    """
    raw_label = str(evidence.get("label", "MISSING"))
    evidence["raw_label"] = raw_label
    history = [x for x in state.get("oi_evidence_history", [])
               if x.get("session_date") == session_date.isoformat() and x.get("expiry") == expiry.isoformat()]
    prior = [str(x.get("raw_label", x.get("label", "MISSING"))) for x in history[-2:]]
    if raw_label not in {"BULLISH", "BEARISH"} or not evidence.get("compared_to_previous_successful_snapshot"):
        evidence["label"] = "MISSING" if not evidence.get("compared_to_previous_successful_snapshot") else "MIXED"
        evidence["persistence_count"] = 0
        evidence["transition_status"] = "NO_DIRECTIONAL_PERSISTENCE"
    else:
        same_prior = sum(1 for label in prior if label == raw_label)
        evidence["persistence_count"] = 1 + same_prior
        previous_directional = next((x for x in reversed(prior) if x in {"BULLISH", "BEARISH"}), None)
        if same_prior >= 1:
            evidence["label"] = raw_label
            evidence["transition_status"] = "DIRECTION_PERSISTENT"
        else:
            evidence["label"] = "MIXED"
            evidence["transition_status"] = "REVERSAL_WATCH" if previous_directional and previous_directional != raw_label else "WAITING_FOR_SECOND_SNAPSHOT"
        evidence["previous_directional_label"] = previous_directional
    history.append({"timestamp": evidence.get("snapshot_time"), "session_date": session_date.isoformat(), "expiry": expiry.isoformat(), "label": raw_label, "raw_label": raw_label, "stable_label": evidence.get("label"), "score": evidence.get("score"), "confidence": evidence.get("confidence")})
    state["oi_evidence_history"] = history[-5:]


def advance_setup_watch(
    candles: Sequence[Candle], previous_processed: Optional[datetime], previous_daily: Sequence[Candle],
    state: dict[str, Any], config: Config, oi_evidence: Optional[Mapping[str, Any]] = None,
) -> Optional[Setup]:
    """Return only a still-valid recent setup watch.

    v109 does not reconstruct old entries candle-by-candle. A fresh current
    1m/3m setup is detected separately and always takes precedence.
    """
    pending = _setup_from_state(state.get("setup_watch"))
    if pending is None or not candles:
        return None
    now = candles[-1].close_time
    age = (now - pending.confirmed_at).total_seconds()
    latest = candles[-1]
    post_confirmation = [c for c in candles if c.start >= pending.confirmed_at]
    expected = [pending.confirmed_at + timedelta(minutes=i) for i in range(max(0, int(age // 60)))]
    missing_bar = [c.start for c in post_confirmation] != expected
    breached = any((c.low <= pending.invalidation) if pending.direction == "BULLISH" else (c.high >= pending.invalidation) for c in post_confirmation)
    if age < -1 or age > config.setup_state_ttl_minutes * 60 or breached or missing_bar:
        state["setup_watch"] = None
        return None
    return pending


def select_active_setup(
    current: Optional[Setup], tracked: Optional[Setup], spot: float,
    oi: Mapping[str, Any], structure: Mapping[str, Any], now: datetime,
    config: Config,
) -> Optional[Setup]:
    """Prefer the newest valid 1m/3m setup; retain an older watch only briefly."""
    def valid(candidate: Optional[Setup]) -> bool:
        if candidate is None:
            return False
        age = (now - candidate.confirmed_at).total_seconds()
        if age < -1 or age > config.setup_state_ttl_minutes * 60:
            return False
        if candidate.direction == "BEARISH" and spot >= candidate.invalidation:
            return False
        if candidate.direction == "BULLISH" and spot <= candidate.invalidation:
            return False
        return True
    if valid(current):
        return current
    if valid(tracked):
        return tracked
    return None


def _direction_sign(value: Any) -> float:
    label = str(value or "").upper()
    if label == "BULLISH":
        return 1.0
    if label == "BEARISH":
        return -1.0
    return 0.0


def _clamp(value: float, low: float = -1.0, high: float = 1.0) -> float:
    return max(low, min(high, float(value)))



def build_direction_consensus(
    oi: Mapping[str, Any], structure: Mapping[str, Any], futures: Mapping[str, Any],
    setup: Optional[Setup], config: Config, market_thesis: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    """v109 direction score led by price but stabilized by the persistent thesis.

    OI remains low-weight in the global score because strike *location* is handled
    separately by the structural gate. This prevents one noisy OI snapshot from
    flipping a trend while still letting confirmed support/resistance breaks act.
    """
    components: dict[str, dict[str, Any]] = {}
    weighted = 0.0
    used_weight = 0.0

    def add(name: str, signal: float, weight: float, detail: Any = None) -> None:
        nonlocal weighted, used_weight
        try:
            signal = _clamp(float(signal))
        except (TypeError, ValueError, OverflowError):
            return
        if not math.isfinite(signal):
            return
        weighted += signal * weight
        used_weight += weight
        components[name] = {"signal": round(signal, 5), "weight": weight, "detail": detail}

    d1 = str(structure.get("execution_direction") or "UNKNOWN").upper()
    c1 = _clamp(float(structure.get("execution_confidence") or 0.0), 0.0, 1.0)
    if d1 in {"BULLISH", "BEARISH"}:
        add("price_1m", _direction_sign(d1) * c1, 0.22, {"direction": d1, "confidence": c1})

    d3 = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    c3 = _clamp(float(structure.get("execution_3m_confidence") or 0.0), 0.0, 1.0)
    if d3 in {"BULLISH", "BEARISH"}:
        add("price_3m", _direction_sign(d3) * c3, 0.25, {"direction": d3, "confidence": c3})

    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    td = str(thesis.get("direction") or "RANGE").upper()
    tc = _clamp(float(thesis.get("confidence") or 0.0), 0.0, 1.0)
    if td in {"BULLISH", "BEARISH"}:
        add("market_thesis", _direction_sign(td) * max(tc, 0.55), 0.20,
            {"direction": td, "state": thesis.get("state"), "confidence": tc})

    d15 = str(structure.get("market_context_15m_bias") or structure.get("higher_timeframe_bias") or "UNKNOWN").upper()
    c15 = _clamp(float(structure.get("market_context_15m_confidence") or structure.get("higher_timeframe_confidence") or 0.0), 0.0, 1.0)
    if d15 in {"BULLISH", "BEARISH"}:
        add("context_15m", _direction_sign(d15) * c15, 0.12, {"direction": d15, "confidence": c15})

    futures_signal = str(futures.get("futures_oi_signal") or "").upper()
    futures_map = {
        "LONG_BUILDUP_BULLISH": 1.0, "SHORT_COVERING_BULLISH": 0.75,
        "SHORT_BUILDUP_BEARISH": -1.0, "LONG_UNWINDING_BEARISH": -0.80,
    }
    if futures_signal in futures_map:
        add("futures_positioning", futures_map[futures_signal], 0.10, futures_signal)

    if oi.get("compared_to_previous_successful_snapshot"):
        balance = _clamp(float(oi.get("directional_balance") or 0.0))
        confidence = _clamp(float(oi.get("confidence") or 0.0), 0.0, 1.0)
        add("oi_current", balance * confidence, 0.05,
            {"raw": oi.get("raw_label"), "stable": oi.get("label"), "confidence": confidence})
        h15 = ((oi.get("oi_horizons") or {}).get("15m") or {}) if isinstance(oi.get("oi_horizons"), Mapping) else {}
        h15_label = str(h15.get("raw_label") or "MISSING").upper()
        h15_conf = _clamp(float(h15.get("confidence") or 0.0), 0.0, 1.0)
        if h15_label in {"BULLISH", "BEARISH"}:
            add("oi_15m", _direction_sign(h15_label) * h15_conf, 0.03,
                {"direction": h15_label, "confidence": h15_conf})

    if setup is not None:
        add("setup", _direction_sign(setup.direction) * _clamp(setup.price_confidence, 0.0, 1.0),
            0.03, {"direction": setup.direction, "kind": setup.kind})

    score = weighted / used_weight if used_weight > 0 else 0.0
    regime = str(structure.get("regime") or "TRANSITION").upper()
    entry_threshold = config.opening_entry_score_min if regime.startswith("OPENING_DISCOVERY") else config.direction_entry_score_min
    direction = "MIXED"
    if score >= entry_threshold:
        direction = "BULLISH"
    elif score <= -entry_threshold:
        direction = "BEARISH"
    aligned = sum(1 for item in components.values() if item["signal"] * score > 0.02)
    opposed = sum(1 for item in components.values() if item["signal"] * score < -0.02)
    return {
        "direction": direction, "score": round(score, 5), "confidence": round(abs(score), 5),
        "entry_threshold": entry_threshold, "reversal_threshold": config.direction_reversal_score_min,
        "aligned_components": aligned, "opposed_components": opposed, "components": components,
        "architecture": "PERSISTENT_THESIS_1M_TRIGGER_3M_CONFIRMATION_15M_CONTEXT_LOCATION_AWARE_OI",
    }

def choose_setup_with_consensus(
    existing: Optional[Setup],
    candles: Sequence[Candle],
    levels: Sequence[PriceLevel],
    structure: Mapping[str, Any],
    consensus: Mapping[str, Any],
    spot: float,
    now: datetime,
    config: Config,
) -> Optional[Setup]:
    """Keep only a fresh setup that agrees with the current weighted direction."""
    if existing is None:
        return None
    direction = str(consensus.get("direction") or "MIXED").upper()
    if direction not in {"BULLISH", "BEARISH"} or existing.direction != direction:
        return None
    age = (now - existing.confirmed_at).total_seconds()
    if age < -1 or age > config.setup_state_ttl_minutes * 60:
        return None
    invalid = (existing.direction == "BULLISH" and spot <= existing.invalidation) or (existing.direction == "BEARISH" and spot >= existing.invalidation)
    return None if invalid else existing



def authorize_consensus_entry(
    consensus: Mapping[str, Any], setup: Setup, oi: Mapping[str, Any], structure: Mapping[str, Any],
    config: Config, market_thesis: Optional[Mapping[str, Any]] = None,
    oi_structure: Optional[Mapping[str, Any]] = None,
) -> None:
    """Authorize a price-structure entry only if it agrees with the durable thesis.

    v109 explicitly prohibits PE into intact bullish support and CE into intact
    bearish resistance. An opposite trade requires the thesis engine itself to
    have flipped after structural acceptance/break evidence.
    """
    direction = str(consensus.get("direction") or "MIXED").upper()
    score = abs(float(consensus.get("score") or 0.0))
    required_threshold = float(consensus.get("entry_threshold") or config.direction_entry_score_min)
    if direction not in {"BULLISH", "BEARISH"} or score < required_threshold:
        raise ScannerError("DIRECTION_CONSENSUS_WEAK", f"Weighted direction score {float(consensus.get('score') or 0.0):.2f} is below the entry threshold {required_threshold:.2f}")
    if setup.direction != direction:
        raise ScannerError("SETUP_DIRECTION_CONFLICT", f"Setup points {setup.direction}, while weighted consensus points {direction}")

    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    thesis_direction = str(thesis.get("direction") or "RANGE").upper()
    thesis_state = str(thesis.get("state") or "RANGE").upper()
    if thesis_direction in {"BULLISH", "BEARISH"} and setup.direction != thesis_direction:
        reason = "COUNTERTREND_SUPPORT_INTACT" if thesis_direction == "BULLISH" else "COUNTERTREND_RESISTANCE_INTACT"
        raise ScannerError(reason, f"{setup.direction} setup conflicts with persistent {thesis_direction} thesis ({thesis_state}); structural invalidation has not flipped the thesis")

    d1 = str(structure.get("execution_direction") or "UNKNOWN").upper()
    d3 = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    c1 = float(structure.get("execution_confidence") or 0.0)
    c3 = float(structure.get("execution_3m_confidence") or 0.0)
    if d1 != direction or d3 != direction:
        raise ScannerError("PRICE_1M_3M_NOT_ALIGNED", f"Entry requires aligned 1m/3m price direction; got {d1}/{d3}")
    if c1 < config.min_1m_execution_confidence or c3 < config.min_3m_execution_confidence:
        raise ScannerError("PRICE_CONFIRMATION_WEAK", f"1m/3m confidence {c1:.2f}/{c3:.2f} is below configured thresholds")

    regime = str(structure.get("regime") or "TRANSITION").upper()
    if regime.startswith("OPENING_DISCOVERY"):
        components = consensus.get("components") if isinstance(consensus.get("components"), Mapping) else {}
        direction_sign = _direction_sign(direction)
        independent_aligned = False
        for name in ("futures_positioning", "oi_current"):
            item = components.get(name) if isinstance(components, Mapping) else None
            if isinstance(item, Mapping) and float(item.get("signal") or 0.0) * direction_sign >= 0.08:
                independent_aligned = True
                break
        if not independent_aligned and score < config.opening_strong_price_override_score:
            raise ScannerError("OPENING_CONFIRMATION_INSUFFICIENT", "Opening entry requires aligned futures/OI confirmation or exceptionally strong 1m/3m price structure")

    # Extreme global OI + futures opposition remains a veto, but ordinary OI
    # disagreement is handled as context rather than a timing gate.
    raw_oi = str(oi.get("raw_label") or oi.get("label") or "MISSING").upper()
    oi_conf = float(oi.get("confidence") or 0.0)
    opposite = "BEARISH" if direction == "BULLISH" else "BULLISH"
    if raw_oi == opposite and oi_conf >= 0.95:
        futures_component = (consensus.get("components") or {}).get("futures_positioning") if isinstance(consensus.get("components"), Mapping) else None
        futures_signal = float((futures_component or {}).get("signal") or 0.0) if isinstance(futures_component, Mapping) else 0.0
        if futures_signal * _direction_sign(direction) < -0.65:
            raise ScannerError("DERIVATIVES_STRONGLY_OPPOSE_ENTRY", "Fresh OI and futures positioning both strongly oppose the price/thesis signal")

    # A structural reversal entry must have a confirmed broken level in state;
    # this prevents a transient 1m/3m flip from masquerading as a reversal.
    if setup.kind == "STRUCTURAL_BREAK_REVERSAL_1M3M" and not thesis.get("break_confirmed"):
        raise ScannerError("REVERSAL_STRUCTURE_NOT_CONFIRMED", "Reversal setup requires a confirmed support/resistance break in the persistent market thesis")

def validate_live_setup_trigger(setup: Setup, spot: float, tolerance_points: float = 0.0) -> None:
    """Require the live underlying quote to remain on the trigger side.

    A closed candle that confirmed a pattern is not an executable entry if the
    live quote has already moved back through the trigger.
    """
    if setup.direction == "BULLISH" and spot <= setup.invalidation:
        raise ScannerError("SETUP_INVALIDATED", f"Bullish setup invalidation is {setup.invalidation:.2f}; live NIFTY {spot:.2f} is at/below invalidation.")
    if setup.direction == "BEARISH" and spot >= setup.invalidation:
        raise ScannerError("SETUP_INVALIDATED", f"Bearish setup invalidation is {setup.invalidation:.2f}; live NIFTY {spot:.2f} is at/above invalidation.")
    if setup.direction == "BULLISH" and spot < setup.trigger - max(0.0, tolerance_points):
        raise ScannerError("LIVE_TRIGGER_NOT_CONFIRMED", f"Bullish trigger is {setup.trigger:.2f}; live NIFTY {spot:.2f} is below it. Wait for price to reclaim the trigger.")
    if setup.direction == "BEARISH" and spot > setup.trigger + max(0.0, tolerance_points):
        raise ScannerError("LIVE_TRIGGER_NOT_CONFIRMED", f"Bearish trigger is {setup.trigger:.2f}; live NIFTY {spot:.2f} is above it. Wait for price to trade at or below the trigger.")


def quote_timing(source_timestamp: datetime, received_at: datetime, *, future_tolerance_seconds: float = 5.0, error_code: str = "SPOT_QUOTE_CLOCK_SKEW") -> tuple[float, float, str]:
    """Return nonnegative quote age, future clock skew and a transparent status."""
    if source_timestamp.tzinfo is None or received_at.tzinfo is None:
        raise ScannerError("QUOTE_TIMESTAMP_INVALID", "Quote source and receipt timestamps must be timezone-aware")
    delta = (received_at - source_timestamp).total_seconds()
    if delta >= 0:
        return delta, 0.0, "SOURCE_TIMESTAMP_NOT_AFTER_RECEIPT"
    skew = -delta
    if skew > future_tolerance_seconds:
        raise ScannerError(error_code, f"Quote source timestamp is {skew:.2f}s ahead of local receipt time")
    return 0.0, skew, "SOURCE_TIMESTAMP_AHEAD_OF_RECEIPT_WITHIN_TOLERANCE"


def _option_record_from_state(row: Mapping[str, Any]) -> OptionRecord:
    return OptionRecord(
        instrument_key=str(row["instrument_key"]), expiry=parse_expiry(row.get("expiry")) or date.min,
        strike=float(row["strike"]), side=str(row["side"]), ltp=float(row.get("ltp", 0)), oi=float(row.get("oi", 0)),
        volume=float(row.get("volume", 0)), previous_session_oi=float(row["previous_session_oi"]) if row.get("previous_session_oi") is not None else None,
        chain_bid=float(row.get("chain_bid", 0)), chain_ask=float(row.get("chain_ask", 0)), chain_bid_qty=float(row.get("chain_bid_qty", 0)), chain_ask_qty=float(row.get("chain_ask_qty", 0)),
        delta=float(row["delta"]) if row.get("delta") is not None else None, gamma=float(row["gamma"]) if row.get("gamma") is not None else None,
        theta=float(row["theta"]) if row.get("theta") is not None else None, vega=float(row["vega"]) if row.get("vega") is not None else None,
        iv=float(row["iv"]) if row.get("iv") is not None else None,
    )


def _snapshot_payload(records: Sequence[OptionRecord], spot: float, session_date: date, expiry: date, fetched_at: datetime) -> dict[str, Any]:
    return {"session_date": session_date.isoformat(), "expiry": expiry.isoformat(), "fetched_at": fetched_at.isoformat(), "spot": spot, "rows": _snapshot_rows(records, spot)}


def _quote_timestamp(raw: Mapping[str, Any]) -> Optional[datetime]:
    return parse_datetime(raw.get("timestamp"))


def _spot_from_full_quote(raw: Mapping[str, Any]) -> tuple[float, Optional[datetime], Mapping[str, Any]]:
    try:
        spot = float(raw.get("last_price"))
    except (TypeError, ValueError):
        spot = 0.0
    if not math.isfinite(spot) or spot <= 0:
        raise ScannerError("SPOT_QUOTE_INVALID", "Full market quote returned an invalid NIFTY spot")
    return spot, _quote_timestamp(raw), raw


def _recent_current_snapshot(state: Mapping[str, Any], session_date: date, expiry: date) -> Optional[Mapping[str, Any]]:
    for snapshot in reversed(state.get("chain_snapshots", [])):
        if snapshot.get("session_date") == session_date.isoformat() and snapshot.get("expiry") == expiry.isoformat():
            return snapshot
    return None


def _first_session_baseline(state: Mapping[str, Any], session_date: date, expiry: date) -> Optional[Mapping[str, Any]]:
    baseline = state.get("session_oi_baseline")
    if baseline and baseline.get("session_date") == session_date.isoformat() and baseline.get("expiry") == expiry.isoformat():
        return baseline
    return None


def _setup_from_state(raw: Optional[Mapping[str, Any]]) -> Optional[Setup]:
    if not isinstance(raw, Mapping):
        return None
    confirmed = parse_datetime(raw.get("confirmed_at"))
    try:
        if confirmed is None:
            return None
        direction = str(raw.get("direction", ""))
        kind = str(raw.get("kind", ""))
        if direction not in {"BULLISH", "BEARISH"} or not kind:
            return None
        return Setup(kind, direction, float(raw["trigger"]), float(raw["invalidation"]), confirmed,
                     float(raw["source_level"]) if raw.get("source_level") is not None else None,
                     str(raw.get("source", "PERSISTED_SETUP")), float(raw.get("price_confidence", 0.0)))
    except (KeyError, TypeError, ValueError):
        return None


def futures_basis_metrics(futures_price: Optional[float], spot_price: float) -> dict[str, Optional[float]]:
    """Return futures-spot spread in index points and true basis points."""
    if futures_price is None or not math.isfinite(float(futures_price)) or not math.isfinite(float(spot_price)) or spot_price <= 0:
        return {"basis_points_value": None, "basis_points": None}
    spread = float(futures_price) - float(spot_price)
    return {"basis_points_value": spread, "basis_points": spread / float(spot_price) * 10000.0}


def build_futures_context(
    futures_quote: Optional[Mapping[str, Any]],
    futures_candles: Sequence[Candle],
    spot_price: float,
    received_at: datetime,
    *,
    max_quote_age_seconds: int,
    max_candle_age_seconds: int,
    instrument_key: Optional[str] = None,
    trading_symbol: Optional[str] = None,
    expiry: Optional[date] = None,
) -> dict[str, Any]:
    """Build futures context only from fresh, timestamped futures data.

    Futures context is informational. A stale/malformed futures feed is
    excluded rather than allowed to contaminate basis or VWAP levels.
    """
    price: Optional[float] = None
    quote_time: Optional[datetime] = None
    quote_age: Optional[float] = None
    quote_status = "FUTURES_QUOTE_UNAVAILABLE"
    if futures_quote is not None:
        try:
            candidate = float(futures_quote.get("last_price"))
            if math.isfinite(candidate) and candidate > 0:
                quote_time = parse_datetime(futures_quote.get("timestamp"))
                if quote_time is None:
                    quote_status = "FUTURES_QUOTE_TIMESTAMP_MISSING"
                else:
                    try:
                        quote_age, _skew, timing_status = quote_timing(
                            quote_time, received_at, error_code="FUTURES_QUOTE_CLOCK_SKEW"
                        )
                    except ScannerError:
                        quote_status = "FUTURES_QUOTE_CLOCK_SKEW"
                    else:
                        if quote_age > max_quote_age_seconds:
                            quote_status = "FUTURES_QUOTE_STALE"
                        else:
                            price = candidate
                            quote_status = timing_status
            else:
                quote_status = "FUTURES_QUOTE_INVALID"
        except (TypeError, ValueError, OverflowError):
            quote_status = "FUTURES_QUOTE_INVALID"

    futures_vwap: Optional[float] = None
    candle_age: Optional[float] = None
    vwap_status = "FUTURES_CANDLES_UNAVAILABLE"
    if futures_candles:
        candle_age = (received_at - futures_candles[-1].close_time).total_seconds()
        if candle_age < -1.0:
            vwap_status = "FUTURES_CANDLE_TIMESTAMP_AHEAD"
        elif candle_age > max_candle_age_seconds:
            vwap_status = "FUTURES_CANDLES_STALE"
        else:
            futures_vwap = valid_futures_vwap(futures_candles)
            vwap_status = "FRESH_WITH_POSITIVE_VOLUME" if futures_vwap is not None else "NO_POSITIVE_VOLUME"

    # Futures OI provides an independent participant-positioning cross-check.
    # It is not mixed into option OI deltas and is never fabricated from candles
    # whose OI field is zero or unchanged.
    futures_oi_signal = "UNAVAILABLE"
    futures_oi_delta = None
    futures_price_delta = None
    futures_oi_pct = None
    recent_futures = _contiguous_tail(futures_candles, 1) if futures_candles else []
    if len(recent_futures) >= 2:
        prev_bar, last_bar = recent_futures[-2], recent_futures[-1]
        futures_oi_delta = last_bar.oi - prev_bar.oi
        futures_price_delta = last_bar.close - prev_bar.close
        futures_oi_pct = 100.0 * futures_oi_delta / prev_bar.oi if prev_bar.oi > 0 else None
        if prev_bar.oi > 0 and last_bar.oi > 0 and futures_oi_delta != 0 and futures_price_delta != 0:
            if futures_price_delta > 0 and futures_oi_delta > 0:
                futures_oi_signal = "LONG_BUILDUP_BULLISH"
            elif futures_price_delta < 0 and futures_oi_delta > 0:
                futures_oi_signal = "SHORT_BUILDUP_BEARISH"
            elif futures_price_delta > 0 and futures_oi_delta < 0:
                futures_oi_signal = "SHORT_COVERING_BULLISH"
            elif futures_price_delta < 0 and futures_oi_delta < 0:
                futures_oi_signal = "LONG_UNWINDING_BEARISH"
        elif futures_oi_delta == 0:
            futures_oi_signal = "OI_UNCHANGED"
    basis = futures_basis_metrics(price, spot_price)
    return {
        "instrument_key": instrument_key,
        "trading_symbol": trading_symbol,
        "expiry": expiry.isoformat() if expiry else None,
        "price": price,
        "quote_timestamp": quote_time.isoformat() if quote_time else None,
        "quote_age_seconds": quote_age,
        "quote_status": quote_status,
        "basis_points": basis["basis_points"],
        "basis_points_value": basis["basis_points_value"],
        "vwap": futures_vwap,
        "vwap_valid": futures_vwap is not None,
        "vwap_status": vwap_status,
        "latest_candle_age_seconds": candle_age,
        "futures_oi_signal": futures_oi_signal,
        "futures_oi_delta": futures_oi_delta,
        "futures_oi_delta_pct": futures_oi_pct,
        "futures_price_delta_points": futures_price_delta,
    }



def classify_market_scenario(oi: Mapping[str, Any], structure: Mapping[str, Any], futures: Mapping[str, Any]) -> dict[str, Any]:
    """Describe the v109 persistent-thesis market scenario for audit/email context."""
    raw = str(oi.get("raw_label", oi.get("label", "MISSING"))).upper()
    stable = str(oi.get("label", "MISSING")).upper()
    d1 = str(structure.get("execution_direction") or "UNKNOWN").upper()
    d3 = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    d15 = str(structure.get("market_context_15m_bias") or structure.get("higher_timeframe_bias") or "UNKNOWN").upper()
    scenario = str(structure.get("regime") or "TRANSITION")
    futures_signal = str(futures.get("futures_oi_signal") or "UNAVAILABLE")
    futures_bias = "BULLISH" if futures_signal in {"LONG_BUILDUP_BULLISH", "SHORT_COVERING_BULLISH"} else "BEARISH" if futures_signal in {"SHORT_BUILDUP_BEARISH", "LONG_UNWINDING_BEARISH"} else "UNKNOWN"
    price_direction = d1 if d1 == d3 and d1 in {"BULLISH", "BEARISH"} else "MIXED"
    confirmations = [x for x in (raw, futures_bias) if x in {"BULLISH", "BEARISH"}]
    aligned = price_direction in {"BULLISH", "BEARISH"} and all(x == price_direction for x in confirmations) if confirmations else price_direction in {"BULLISH", "BEARISH"}
    return {
        "scenario": scenario,
        "price_1m_direction": d1,
        "price_3m_direction": d3,
        "market_context_15m": d15,
        "price_execution_direction": price_direction,
        "higher_timeframe_bias": d15,
        "oi_raw_direction": raw,
        "oi_stable_direction": stable,
        "oi_confidence": float(oi.get("confidence") or 0.0),
        "futures_positioning": futures_signal,
        "futures_bias": futures_bias,
        "multi_horizon_direction": oi.get("multi_horizon_direction"),
        "multi_horizon_balance": oi.get("multi_horizon_balance"),
        "alignment": "ALIGNED" if aligned else "PARTIAL_OR_CONFLICTING",
    }

def _next_grid_price(entry: float, direction: str, grid: float, minimum_distance: float) -> float:
    if grid <= 0:
        raise ScannerError("TARGET_GRID_INVALID", "Target grid must be positive")
    if direction == "BULLISH":
        level = math.ceil((entry + 1e-9) / grid) * grid
        if level - entry < minimum_distance:
            level += grid
        return level
    level = math.floor((entry - 1e-9) / grid) * grid
    if entry - level < minimum_distance:
        level -= grid
    return level



def choose_oi_targets_and_stop(
    entry: float, setup: Setup, oi: Mapping[str, Any], structure: Mapping[str, Any],
    config: Config, now: datetime, levels: Sequence[PriceLevel] = (),
    market_thesis: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    """Build one immutable v109 risk plan.

    Trend/thesis-continuation trades use meaningful NIFTY 50-point objectives.
    Reversal/range trades retain tighter local structural objectives. Minor
    1m/3m levels before T1 are recorded as intermediate barriers, not promoted
    to profit targets merely because they are nearby.
    """
    direction = setup.direction
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("DIRECTION_INVALID", "Risk plan requires BULLISH or BEARISH setup")
    atr1 = float(structure.get("atr_1m") or 0.0)
    atr3 = float(structure.get("atr_3m") or structure.get("atr_5m") or atr1 or 0.0)
    atr15 = float(structure.get("atr_15m") or atr3 or 0.0)
    if atr1 <= 0 or not math.isfinite(atr1):
        raise ScannerError("ATR_UNAVAILABLE", "One-minute ATR is unavailable for risk planning")

    try:
        invalidation = float(setup.invalidation)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ScannerError("INVALID_STOP", "Setup invalidation is not numeric") from exc
    if not math.isfinite(invalidation) or invalidation <= 0:
        raise ScannerError("INVALID_STOP", "Setup invalidation must be finite and positive")
    raw_risk = (entry - invalidation) if direction == "BULLISH" else (invalidation - entry)
    if raw_risk <= 0:
        raise ScannerError("INVALID_STOP", "Setup invalidation is not on the risk side of entry")

    min_risk = max(config.minimum_stop_points, config.min_initial_stop_atr * atr1)
    buffer = max(1.0, config.stop_buffer_atr_fraction * atr1)
    risk = max(raw_risk + buffer, min_risk)
    max_risk = min(config.max_initial_stop_points, max(config.minimum_stop_points, config.max_stop_atr * atr1))
    if risk > max_risk + 1e-9:
        raise ScannerError("STOP_TOO_WIDE", f"Fresh setup requires {risk:.1f} NIFTY points of risk; v109 limit is {max_risk:.1f}")
    stop = entry - risk if direction == "BULLISH" else entry + risk

    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    thesis_direction = str(thesis.get("direction") or "RANGE").upper()
    thesis_state = str(thesis.get("state") or "RANGE").upper()
    trend_trade = setup.kind != "EARLY_OI_LEVEL_REVERSAL" and thesis_direction == direction and thesis_state not in {"RANGE", "REVERSAL_PENDING_BULL", "REVERSAL_PENDING_BEAR"}

    target_side = "RESISTANCE" if direction == "BULLISH" else "SUPPORT"
    rows: list[dict[str, Any]] = []
    max_target_distance = config.trend_target2_max_points if trend_trade else config.target2_max_points
    for level in levels:
        if level.side != target_side:
            continue
        distance = (level.price - entry) if direction == "BULLISH" else (entry - level.price)
        if distance <= 0 or distance > max_target_distance + 1e-9:
            continue
        source = str(level.source)
        priority = 3
        if "15M_CONTEXT" in source:
            priority = 0
        elif "3M_SWING" in source or "SESSION_HIGH" in source or "SESSION_LOW" in source:
            priority = 1
        elif "NIFTY_50_GRID" in source:
            priority = 2
        elif "OI_" in source:
            priority = 4
        rows.append({"price": float(level.price), "source": source, "strength": float(level.strength),
                     "distance": float(distance), "priority": priority})

    if trend_trade:
        grid1 = _next_grid_price(entry, direction, config.target_grid_points, config.trend_target_min_points)
        grid2 = grid1 + config.target_grid_points if direction == "BULLISH" else grid1 - config.target_grid_points
        grid1_distance, grid2_distance = abs(grid1 - entry), abs(grid2 - entry)
        if grid1_distance > config.trend_target1_max_points + 1e-9:
            raise ScannerError("LOCAL_TARGET_RR_UNAVAILABLE", f"Next meaningful 50-point trend target is {grid1_distance:.1f} points away, beyond the v109 trend T1 limit")
        if grid1_distance / max(risk, 1e-9) < config.min_underlying_rr:
            raise ScannerError("LOCAL_TARGET_RR_UNAVAILABLE", f"Trend T1 {grid1:.2f} offers only {grid1_distance / max(risk,1e-9):.2f}R with {risk:.1f}-point risk")
        t1, t2 = grid1, grid2 if grid2_distance <= config.trend_target2_max_points + 1e-9 else None
        t1_row = {"price": t1, "source": "NIFTY_50_GRID_TREND_OBJECTIVE", "strength": 1.5, "distance": grid1_distance, "priority": 0}
        t2_row = ({"price": t2, "source": "NIFTY_50_GRID_TREND_RUNNER", "strength": 1.5, "distance": grid2_distance, "priority": 0}
                  if t2 is not None else None)
        # Levels before the grid objective remain useful management barriers.
        intermediate = sorted([r for r in rows if r["distance"] < grid1_distance - 1e-9], key=lambda r: r["distance"])[:6]
        target_method = "THESIS_TREND_MEANINGFUL_50_POINT_GRID"
    else:
        grid1 = _next_grid_price(entry, direction, config.target_grid_points, config.target1_min_points)
        rows.append({"price": grid1, "source": "NIFTY_50_GRID", "strength": 1.25,
                     "distance": abs(grid1 - entry), "priority": 2})
        grid2 = grid1 + config.target_grid_points if direction == "BULLISH" else grid1 - config.target_grid_points
        if abs(grid2 - entry) <= config.target2_max_points + 1e-9:
            rows.append({"price": grid2, "source": "NIFTY_50_GRID_NEXT", "strength": 1.25,
                         "distance": abs(grid2 - entry), "priority": 2})
        deduped: list[dict[str, Any]] = []
        for row in sorted(rows, key=lambda r: (r["distance"], r["priority"], -r["strength"])):
            if row["distance"] < config.target1_min_points - 1e-9:
                continue
            existing = next((x for x in deduped if abs(float(x["price"]) - float(row["price"])) <= max(1.5, 0.10 * atr1)), None)
            if existing is None:
                deduped.append(row)
            elif (row["priority"], -row["strength"]) < (existing["priority"], -existing["strength"]):
                existing.update(row)
        deduped.sort(key=lambda r: r["distance"])
        t1_candidates = [r for r in deduped if r["distance"] <= config.target1_max_points + 1e-9
                         and r["distance"] / max(risk, 1e-9) >= config.min_underlying_rr]
        if not t1_candidates:
            raise ScannerError("LOCAL_TARGET_RR_UNAVAILABLE", f"No local reversal/range T1 within {config.target1_max_points:.0f} points offers at least {config.min_underlying_rr:.2f}R")
        t1_row = min(t1_candidates, key=lambda r: (r["distance"], r["priority"], -r["strength"]))
        t1 = float(t1_row["price"])
        t1_distance = abs(t1 - entry)
        beyond = [r for r in deduped if r["distance"] >= t1_distance + max(8.0, 0.45 * atr1)
                  and r["distance"] <= config.target2_max_points + 1e-9]
        t2_row = min(beyond, key=lambda r: (r["distance"], r["priority"], -r["strength"]), default=None)
        t2 = float(t2_row["price"]) if t2_row is not None else None
        if t2 is None:
            synthetic = t1 + config.target_grid_points if direction == "BULLISH" else t1 - config.target_grid_points
            if abs(synthetic - entry) <= config.target2_max_points + 1e-9:
                t2 = synthetic
                t2_row = {"price": synthetic, "source": "NIFTY_50_GRID_RUNNER", "strength": 1.0,
                          "distance": abs(synthetic - entry), "priority": 2}
        intermediate = [r for r in deduped if r["distance"] < t1_distance - 1e-9][:5]
        target_method = "REVERSAL_RANGE_LOCAL_STRUCTURE_AND_50_POINT_GRID"

    t1_distance = abs(float(t1) - entry)
    rr = t1_distance / risk
    local_now = now.astimezone(IST)
    close_time = datetime.combine(local_now.date(), dtime(15, 30), tzinfo=IST)
    minutes_left = max(0.0, (close_time - local_now).total_seconds() / 60.0)
    if minutes_left <= 0:
        raise ScannerError("MARKET_CLOSED", "No trading time remains")
    if minutes_left < config.min_entry_minutes_to_close:
        raise ScannerError("ENTRY_TOO_CLOSE_TO_MARKET_CLOSE", f"Only {minutes_left:.1f} minutes remain; v109 requires at least {config.min_entry_minutes_to_close:.1f} minutes for a new position")

    return {
        "entry_underlying": entry, "stop_underlying": stop, "initial_stop_underlying": stop,
        "stop_source": "FRESH_1M_3M_INVALIDATION_WITH_ATR_FLOOR",
        "stop_reference_price": invalidation, "stop_reference_source": setup.source,
        "risk_points": risk, "stop_buffer_points": buffer, "atr_1m": atr1, "atr_3m": atr3,
        "atr_15m": atr15, "atr_5m": atr3,
        "t1_underlying": float(t1), "t1_source": t1_row["source"],
        "t1_confluence": "THESIS_TREND_GRID" if trend_trade else "LOCAL_PRICE_STRUCTURE_OR_50_GRID",
        "t1_level_strength": t1_row["strength"], "t1_oi_score": None, "t1_oi": None, "t1_flow": None,
        "t2_underlying": float(t2) if t2 is not None else None,
        "t2_source": t2_row["source"] if t2_row else None,
        "t2_confluence": "THESIS_TREND_GRID" if trend_trade and t2_row else ("LOCAL_PRICE_STRUCTURE_OR_50_GRID" if t2_row else None),
        "t2_level_strength": t2_row["strength"] if t2_row else None,
        "underlying_rr": rr, "t2_underlying_rr": abs(float(t2) - entry) / risk if t2 is not None else None,
        "minutes_to_market_close": minutes_left, "target_method": target_method,
        "targets_fixed_at_entry": True, "target1_distance_points": t1_distance,
        "target2_distance_points": abs(float(t2) - entry) if t2 is not None else None,
        "intermediate_soft_barriers": intermediate,
        "t1_hard_barrier": not trend_trade and t1_row.get("priority", 3) <= 1,
        "t1_barrier_quality": t1_row["strength"], "trend_trade": trend_trade,
        "thesis_state_at_entry": thesis_state, "thesis_direction_at_entry": thesis_direction,
    }

def _position_direction(position: Mapping[str, Any]) -> str:
    direction = str(position.get("direction") or "").upper()
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("ACTIVE_POSITION_INVALID", "Active position has no valid BULLISH/BEARISH direction")
    return direction


def create_active_position(
    signal_key: str,
    opened_at: datetime,
    setup: Mapping[str, Any],
    selected: Mapping[str, Any],
    risk_plan: Mapping[str, Any],
    latest_candle: Candle,
    config: Config,
    *,
    recovered: bool = False,
) -> dict[str, Any]:
    """Create the immutable identity and mutable management state for one signal position."""
    direction = str(setup.get("direction") or ("BULLISH" if selected.get("side") == "CE" else "BEARISH")).upper()
    side = str(selected.get("side") or "").upper()
    if direction not in {"BULLISH", "BEARISH"} or side != ("CE" if direction == "BULLISH" else "PE"):
        raise ScannerError("ACTIVE_POSITION_INVALID", "Selected contract side and setup direction do not agree")
    required = ("instrument_key", "strike", "expiry", "reference_entry_ask")
    if any(selected.get(field) in (None, "") for field in required):
        raise ScannerError("ACTIVE_POSITION_INVALID", "Selected contract is missing a required identity/entry field")
    for field in ("entry_underlying", "stop_underlying", "t1_underlying"):
        try:
            value = float(risk_plan[field])
        except (KeyError, TypeError, ValueError, OverflowError) as exc:
            raise ScannerError("ACTIVE_POSITION_INVALID", f"Risk plan is missing valid {field}") from exc
        if not math.isfinite(value) or value <= 0:
            raise ScannerError("ACTIVE_POSITION_INVALID", f"Risk plan {field} must be finite and positive")
    t2 = risk_plan.get("t2_underlying")
    if t2 is not None and (not math.isfinite(float(t2)) or float(t2) <= 0):
        raise ScannerError("ACTIVE_POSITION_INVALID", "Risk plan T2 must be finite and positive when supplied")
    entry_ask = float(selected["reference_entry_ask"])
    if entry_ask <= 0 or not math.isfinite(entry_ask):
        raise ScannerError("ACTIVE_POSITION_INVALID", "Reference entry premium must be finite and positive")
    opened = opened_at.astimezone(IST)
    # A full OHLC candle for the entry minute contains price action that occurred
    # before the position existed, so it must not be replayed as post-entry risk.
    # Use the entry minute as a sentinel checkpoint; the first safely replayable
    # completed candle is the following minute.
    entry_minute = opened.replace(second=0, microsecond=0)
    monitoring_checkpoint = max(latest_candle.start.astimezone(IST), entry_minute)
    return {
        "position_id": signal_key,
        "signal_key": signal_key,
        "session_date": opened.date().isoformat(),
        "status": "OPEN",
        "direction": direction,
        "selected_contract": dict(selected),
        "instrument_key": str(selected["instrument_key"]),
        "side": side,
        "strike": float(selected["strike"]),
        "expiry": str(selected["expiry"]),
        "opened_at": opened.isoformat(),
        "entry_spot": float(risk_plan["entry_underlying"]),
        "entry_premium_ask": entry_ask,
        "entry_premium_bid": float(selected.get("reference_bid") or 0.0),
        "peak_premium_bid": float(selected.get("reference_bid") or 0.0),
        "last_premium_bid": float(selected.get("reference_bid") or 0.0),
        "last_premium_quote_at": selected.get("quote_timestamp"),
        "initial_stop_underlying": float(risk_plan["stop_underlying"]),
        "stop_underlying": float(risk_plan["stop_underlying"]),
        "t1_underlying": float(risk_plan["t1_underlying"]),
        "t1_source": risk_plan.get("t1_source"),
        "t1_confluence": risk_plan.get("t1_confluence"),
        "t2_underlying": float(t2) if t2 is not None else None,
        "t2_source": risk_plan.get("t2_source"),
        "t2_confluence": risk_plan.get("t2_confluence"),
        "risk_plan": dict(risk_plan),
        "t1_hit": False,
        "t1_hit_at": None,
        "t1_partial_exit_pct": float(config.t1_partial_exit_pct),
        "remaining_pct": 100.0,
        "management_state": "ENTRY_ACTIVE",
        "post_t1_started_at": None,
        "post_t1_anchor_spot": None,
        "post_t1_peak_spot": None,
        "post_t1_peak_premium_bid": None,
        "post_t1_last_progress_at": None,
        "post_t1_no_progress_bars": 0,
        "last_monitored_candle": monitoring_checkpoint.isoformat(),
        "favourable_spot_extreme": float(risk_plan["entry_underlying"]),
        "recovered_from_legacy": bool(recovered),
        "recovered_at": opened.isoformat() if recovered else None,
        "created_at": now_ist().isoformat(),
    }



def _position_event(
    active: Mapping[str, Any],
    event_type: str,
    reason_code: str,
    timestamp: datetime,
    spot: float,
    *,
    premium_bid: Optional[float] = None,
    details: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    position_id = str(active.get("position_id") or active.get("signal_key") or "UNKNOWN")
    event_token = f"{position_id}|{event_type}|{timestamp.astimezone(IST).isoformat()}"
    event_key = hashlib.sha256(event_token.encode("utf-8")).hexdigest()[:24]
    risk = dict(active.get("risk_plan") or {})
    risk.update({
        "entry_underlying": active.get("entry_spot"),
        "stop_underlying": active.get("stop_underlying"),
        "t1_underlying": active.get("t1_underlying"),
        "t2_underlying": active.get("t2_underlying"),
    })
    payload: dict[str, Any] = {
        "scanner_version": VERSION,
        "schema_version": SCHEMA_VERSION,
        "timestamp": timestamp.astimezone(IST).isoformat(),
        "session_date": timestamp.astimezone(IST).date().isoformat(),
        "decision": "POSITION_EVENT",
        "reason_code": reason_code,
        "event_type": event_type,
        "signal_key": event_key,
        "position_id": position_id,
        "original_signal_key": active.get("signal_key"),
        "setup_direction": active.get("direction"),
        "selected_contract": dict(active.get("selected_contract") or {}),
        "risk_plan": risk,
        "spot": spot,
        "position_status": active.get("status"),
        "remaining_pct": active.get("remaining_pct"),
        "t1_hit": active.get("t1_hit"),
        "premium_bid": premium_bid,
        "oi": {},
        "structure": {},
    }
    if details:
        payload["position_event_details"] = dict(details)
    return payload


def close_active_position(
    active: dict[str, Any],
    reason_code: str,
    timestamp: datetime,
    spot: float,
    *,
    premium_bid: Optional[float] = None,
    details: Optional[Mapping[str, Any]] = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    closed = dict(active)
    closed.update({
        "status": "CLOSED",
        "exit_reason": reason_code,
        "closed_at": timestamp.astimezone(IST).isoformat(),
        "exit_spot": float(spot),
        "exit_premium_bid": premium_bid,
        "remaining_pct": 0.0,
    })
    event = _position_event(closed, "POSITION_EXIT", reason_code, timestamp, spot,
                            premium_bid=premium_bid, details=details)
    event["position_status"] = "CLOSED"
    event["exit_spot"] = spot
    event["exit_reason"] = reason_code
    event["remaining_pct"] = active.get("remaining_pct", 100.0)
    return closed, event



def _runner_support_score(direction: str, oi_structure: Optional[Mapping[str, Any]]) -> float:
    if not isinstance(oi_structure, Mapping):
        return 0.0
    key = "supportive_bullish_score" if direction == "BULLISH" else "supportive_bearish_score"
    try:
        return _clamp(float(oi_structure.get(key) or 0.0), 0.0, 1.0)
    except (TypeError, ValueError, OverflowError):
        return 0.0


def _adaptive_runner_drawdown_limit(
    active: Mapping[str, Any], now: datetime, structure: Mapping[str, Any],
    market_thesis: Optional[Mapping[str, Any]], oi_structure: Optional[Mapping[str, Any]],
    config: Config,
) -> float:
    """Return adaptive post-T1 premium giveback tolerance as a percentage."""
    limit = float(config.post_t1_base_peak_drawdown_pct)
    expiry = parse_expiry(active.get("expiry"))
    local = now.astimezone(IST)
    if expiry == local.date():
        # Same-day expiry becomes progressively less forgiving after lunch.
        if local.time() >= dtime(12, 30):
            minutes = max(0.0, (local - datetime.combine(local.date(), dtime(12, 30), tzinfo=IST)).total_seconds() / 60.0)
            span = 120.0  # 12:30 -> 14:30
            fraction = min(1.0, minutes / span)
            limit = limit + fraction * (config.post_t1_expiry_afternoon_drawdown_pct - limit)
    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    if str(thesis.get("direction") or "").upper() == _position_direction(active):
        state = str(thesis.get("state") or "")
        if state.endswith("_TREND"):
            limit += 1.5
        elif "PULLBACK" in state or "TEST" in state:
            limit -= 1.0
    supportive = _runner_support_score(_position_direction(active), oi_structure)
    if supportive >= 0.70:
        limit += 1.5
    d3 = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    if d3 in {"SIDEWAYS", "MIXED"}:
        limit -= 1.0
    return round(max(7.5, min(18.0, limit)), 2)


def _initialize_runner_state(active: dict[str, Any], at: datetime, spot_anchor: float, premium_bid: Optional[float]) -> None:
    active["management_state"] = "RUNNER_TRENDING"
    active["post_t1_started_at"] = at.astimezone(IST).isoformat()
    active["post_t1_anchor_spot"] = float(spot_anchor)
    active["post_t1_peak_spot"] = float(spot_anchor)
    active["post_t1_peak_premium_bid"] = float(premium_bid) if premium_bid is not None and premium_bid > 0 else None
    active["post_t1_last_progress_at"] = at.astimezone(IST).isoformat()
    active["post_t1_no_progress_bars"] = 0


def _trail_active_stop(
    active: dict[str, Any], levels: Sequence[PriceLevel], spot: float,
    structure: Mapping[str, Any], config: Config,
    *, market_thesis: Optional[Mapping[str, Any]] = None,
    oi_structure: Optional[Mapping[str, Any]] = None,
) -> Optional[dict[str, Any]]:
    """Ratchet the underlying stop behind improving structural/OI support.

    Before T1 a trail is allowed only after meaningful favourable progress and
    supportive location-aware OI. After T1 the runner may also use a strong OI
    support/resistance strike as a profit-protection reference. The stop can
    never loosen.
    """
    direction = _position_direction(active)
    atr1 = float(structure.get("atr_1m") or (active.get("risk_plan") or {}).get("atr_1m") or 0.0)
    if atr1 <= 0:
        return None
    entry = float(active.get("entry_spot") or 0.0)
    old_stop = float(active.get("stop_underlying") or 0.0)
    if entry <= 0 or old_stop <= 0:
        return None
    favourable_extreme = float(active.get("favourable_spot_extreme") or entry)
    progress = (favourable_extreme - entry) if direction == "BULLISH" else (entry - favourable_extreme)
    supportive = _runner_support_score(direction, oi_structure)
    after_t1 = bool(active.get("t1_hit"))
    if not after_t1 and (progress < config.pre_t1_trail_min_progress_atr * atr1 or supportive < config.thesis_oi_support_score_min):
        return None

    buffer_fraction = 0.22 if after_t1 else 0.32
    buffer = max(3.0 if after_t1 else 4.0, atr1 * buffer_fraction)
    side = "SUPPORT" if direction == "BULLISH" else "RESISTANCE"
    candidates: list[tuple[float, str, float]] = []
    for level in levels:
        if level.side != side or level.strength < max(config.min_level_strength, 1.5):
            continue
        if not _level_has_structural_provenance(level):
            continue
        candidate = float(level.price) - buffer if direction == "BULLISH" else float(level.price) + buffer
        candidates.append((candidate, level.source, float(level.strength)))

    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    thesis_anchor = thesis.get("anchor_support") if direction == "BULLISH" else thesis.get("anchor_resistance")
    thesis_source = thesis.get("anchor_support_source") if direction == "BULLISH" else thesis.get("anchor_resistance_source")
    if thesis_anchor is not None:
        try:
            anchor = float(thesis_anchor)
            candidates.append((anchor - buffer if direction == "BULLISH" else anchor + buffer,
                               str(thesis_source or "MARKET_THESIS_LEVEL"), 2.5))
        except (TypeError, ValueError, OverflowError):
            pass

    # Post-T1 only: strong fresh writer support/resistance is allowed as a soft
    # runner-profit reference even without a second structural source.
    if after_t1 and supportive >= config.thesis_oi_support_score_min and isinstance(oi_structure, Mapping):
        row = oi_structure.get("support") if direction == "BULLISH" else oi_structure.get("resistance")
        if isinstance(row, Mapping):
            try:
                strike = float(row.get("strike"))
                if strike > 0:
                    candidates.append((strike - buffer if direction == "BULLISH" else strike + buffer,
                                       "OI_RUNNER_SUPPORT" if direction == "BULLISH" else "OI_RUNNER_RESISTANCE",
                                       1.0 + supportive))
            except (TypeError, ValueError, OverflowError):
                pass

    valid: list[tuple[float, str, float]] = []
    minimum_gap = max(2.0, 0.12 * atr1)
    for candidate, source, strength in candidates:
        improves = candidate > old_stop + 0.25 if direction == "BULLISH" else candidate < old_stop - 0.25
        behind = candidate <= spot - minimum_gap if direction == "BULLISH" else candidate >= spot + minimum_gap
        if after_t1:
            locks_profit = candidate >= entry if direction == "BULLISH" else candidate <= entry
        else:
            locks_profit = True
        if improves and behind and locks_profit:
            valid.append((candidate, source, strength))
    if not valid:
        return None
    candidate, source, strength = (max(valid, key=lambda x: (x[0], x[2])) if direction == "BULLISH"
                                   else min(valid, key=lambda x: (x[0], -x[2])))
    active["stop_underlying"] = candidate
    risk = dict(active.get("risk_plan") or {})
    risk.update({"stop_underlying": candidate, "trailing_stop_source": source,
                 "trailing_stop_buffer_points": buffer, "trailing_oi_support_score": supportive})
    active["risk_plan"] = risk
    return {"previous_stop": old_stop, "new_stop": candidate, "source": source,
            "buffer_points": buffer, "oi_support_score": supportive}


def manage_active_position(
    active: dict[str, Any], candles: Sequence[Candle], spot: float,
    quote_received_at: datetime, oi: Mapping[str, Any], structure: Mapping[str, Any],
    setup: Optional[Setup], config: Config, *, chain_refresh_ok: bool,
    option_quote: Optional[OptionQuote], levels: Sequence[PriceLevel] = (),
    direction_consensus: Optional[Mapping[str, Any]] = None,
    market_thesis: Optional[Mapping[str, Any]] = None,
    oi_structure: Optional[Mapping[str, Any]] = None,
) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]], str, dict[str, Any]]:
    """Manage one locked contract with thesis-aware and option-aware protection.

    Before T1 the durable market thesis is protected. After T1 the remaining
    runner switches to profit protection: structural/OI stop ratchet, post-T1
    premium peak drawdown, and theta/no-progress exits. An option may be exited
    while the broader market thesis remains intact; a fresh 3m setup can re-enter.
    """
    active = dict(active)
    direction = _position_direction(active)
    opened_at = parse_datetime(active.get("opened_at"))
    last_candle = parse_datetime(active.get("last_monitored_candle"))
    if opened_at is None or last_candle is None:
        raise ScannerError("ACTIVE_POSITION_STATE_INVALID", "Active position has invalid opened_at or last_monitored_candle")
    entry_minute = opened_at.replace(second=0, microsecond=0)
    if last_candle < entry_minute:
        last_candle = entry_minute
        active["last_monitored_candle"] = last_candle.isoformat()
    if active.get("status") != "OPEN":
        raise ScannerError("ACTIVE_POSITION_STATE_INVALID", "Only OPEN positions can be managed")

    entry_spot = float(active.get("entry_spot") or 0.0)
    t1 = float(active.get("t1_underlying") or 0.0)
    t2_raw = active.get("t2_underlying")
    t2 = float(t2_raw) if t2_raw is not None else None
    if min(entry_spot, t1, float(active.get("stop_underlying") or 0.0)) <= 0:
        raise ScannerError("ACTIVE_POSITION_STATE_INVALID", "Active position contains invalid entry, stop or T1")

    events: list[dict[str, Any]] = []
    latest_bid: Optional[float] = None
    quote_age: Optional[float] = None
    if option_quote is not None and option_quote.timestamp is not None and option_quote.bid > 0:
        try:
            quote_age, _, _ = quote_timing(option_quote.timestamp, quote_received_at, error_code="OPTION_QUOTE_CLOCK_SKEW")
        except ScannerError:
            quote_age = None
        if quote_age is not None and quote_age <= config.max_quote_age_seconds:
            latest_bid = float(option_quote.bid)
            active["last_premium_quote_at"] = option_quote.timestamp.isoformat()
            active["last_premium_bid"] = latest_bid
            active["peak_premium_bid"] = max(float(active.get("peak_premium_bid") or 0.0), latest_bid)

    def close(reason: str, at: datetime, price: float, detail: Optional[Mapping[str, Any]] = None):
        closed, event = close_active_position(active, reason, at, price, premium_bid=latest_bid, details=detail)
        events.append(event)
        return None, events, reason, {"position_closed": True, "exit_reason": reason,
                                      "closed_position": closed, **(dict(detail or {}))}

    def hit_t1(at: datetime, source: str) -> Optional[tuple[Optional[dict[str, Any]], list[dict[str, Any]], str, dict[str, Any]]]:
        if active.get("t1_hit"):
            return None
        if t2 is None:
            return close("TARGET_1_HIT_NO_T2", at, t1, {"full_exit_pct": active.get("remaining_pct", 100.0), "touch_source": source})
        active["t1_hit"] = True
        active["t1_hit_at"] = at.astimezone(IST).isoformat()
        partial_pct = float(active.get("t1_partial_exit_pct") or config.t1_partial_exit_pct)
        active["remaining_pct"] = max(0.0, 100.0 - partial_pct)
        old_stop = float(active.get("stop_underlying") or entry_spot)
        active["stop_underlying"] = max(old_stop, entry_spot) if direction == "BULLISH" else min(old_stop, entry_spot)
        _initialize_runner_state(active, at, t1, latest_bid)
        events.append(_position_event(
            active, "TARGET_1_PARTIAL", "TARGET_1_HIT_CONTINUE_MANAGING", at, t1,
            premium_bid=latest_bid,
            details={"partial_exit_pct": partial_pct, "remaining_pct": active["remaining_pct"],
                     "t1_underlying": t1, "t2_underlying": t2, "stop_moved_to_at_least_entry": True,
                     "management_state": "RUNNER_TRENDING", "touch_source": source},
        ))
        return None

    new_candles = [c for c in sorted(candles, key=lambda x: x.start) if c.start > last_candle]
    if new_candles:
        first_gap = (new_candles[0].start - last_candle).total_seconds()
        if first_gap > 60.5:
            raise ScannerError("POSITION_CANDLE_GAP", f"First available monitoring candle {new_candles[0].start.isoformat()} is more than one minute after checkpoint {last_candle.isoformat()}; position lock retained")
    for previous, current in zip(new_candles, new_candles[1:]):
        if (current.start - previous.start).total_seconds() > 60.5:
            raise ScannerError("POSITION_CANDLE_GAP", f"Missing one-minute monitoring candles between {previous.start.isoformat()} and {current.start.isoformat()}; position lock retained")

    progress_step = max(2.0, 0.12 * float(structure.get("atr_1m") or 1.0))
    for candle in new_candles:
        if candle.start <= last_candle:
            continue
        current_stop = float(active.get("stop_underlying") or 0.0)  # refreshed every candle; T1 may have ratcheted it
        stop_hit = (candle.low <= current_stop) if direction == "BULLISH" else (candle.high >= current_stop)
        if stop_hit:
            active["last_monitored_candle"] = candle.start.isoformat()
            return close("STOP_LOSS_HIT" if not active.get("t1_hit") else "BREAKEVEN_OR_TRAILING_STOP_HIT",
                         candle.close_time, current_stop,
                         {"monitoring_candle": candle.start.isoformat(), "candle_high": candle.high, "candle_low": candle.low})

        t1_cross = (candle.high >= t1) if direction == "BULLISH" else (candle.low <= t1)
        t2_cross = t2 is not None and ((candle.high >= t2) if direction == "BULLISH" else (candle.low <= t2))
        if not active.get("t1_hit") and t1_cross:
            closed = hit_t1(candle.close_time, "COMPLETED_1M_CANDLE")
            if closed is not None:
                return closed
            if t2_cross:
                return close("TARGET_2_HIT", candle.close_time, float(t2),
                             {"remaining_pct_before_exit": active.get("remaining_pct"), "monitoring_candle": candle.start.isoformat()})
        elif active.get("t1_hit") and t2_cross:
            return close("TARGET_2_HIT", candle.close_time, float(t2),
                         {"remaining_pct_before_exit": active.get("remaining_pct"), "monitoring_candle": candle.start.isoformat()})

        favourable_price = candle.high if direction == "BULLISH" else candle.low
        old_extreme = float(active.get("favourable_spot_extreme") or entry_spot)
        improved = favourable_price > old_extreme + progress_step if direction == "BULLISH" else favourable_price < old_extreme - progress_step
        if (direction == "BULLISH" and favourable_price > old_extreme) or (direction == "BEARISH" and favourable_price < old_extreme):
            active["favourable_spot_extreme"] = favourable_price
        if active.get("t1_hit"):
            peak = float(active.get("post_t1_peak_spot") or t1)
            post_progress_step = max(2.0, config.post_t1_min_progress_atr * float(structure.get("atr_1m") or 1.0))
            post_improved = favourable_price > peak + post_progress_step if direction == "BULLISH" else favourable_price < peak - post_progress_step
            if (direction == "BULLISH" and favourable_price > peak) or (direction == "BEARISH" and favourable_price < peak):
                active["post_t1_peak_spot"] = favourable_price
            if post_improved or improved:
                active["post_t1_last_progress_at"] = candle.close_time.astimezone(IST).isoformat()
                active["post_t1_no_progress_bars"] = 0
        active["last_monitored_candle"] = candle.start.isoformat()

    # Current spot catches touches after the last completed candle.
    current_stop = float(active.get("stop_underlying") or 0.0)
    spot_stop_hit = (spot <= current_stop) if direction == "BULLISH" else (spot >= current_stop)
    if spot_stop_hit:
        return close("STOP_LOSS_HIT" if not active.get("t1_hit") else "BREAKEVEN_OR_TRAILING_STOP_HIT",
                     quote_received_at, current_stop, {"touch_source": "LIVE_SPOT_QUOTE"})
    if not active.get("t1_hit"):
        spot_t1 = (spot >= t1) if direction == "BULLISH" else (spot <= t1)
        if spot_t1:
            closed = hit_t1(quote_received_at, "LIVE_SPOT_QUOTE")
            if closed is not None:
                return closed
            if t2 is not None and ((spot >= t2) if direction == "BULLISH" else (spot <= t2)):
                return close("TARGET_2_HIT", quote_received_at, t2, {"touch_source": "LIVE_SPOT_QUOTE_CROSSED_T1_AND_T2"})
    elif t2 is not None and ((spot >= t2) if direction == "BULLISH" else (spot <= t2)):
        return close("TARGET_2_HIT", quote_received_at, t2, {"touch_source": "LIVE_SPOT_QUOTE"})

    if active.get("t1_hit") and active.get("post_t1_started_at") is None:
        _initialize_runner_state(active, parse_datetime(active.get("t1_hit_at")) or quote_received_at, t1, latest_bid)

    # Update live spot/premium runner peaks before applying protection.
    if active.get("t1_hit"):
        peak_spot = float(active.get("post_t1_peak_spot") or t1)
        post_progress_step = max(2.0, config.post_t1_min_progress_atr * float(structure.get("atr_1m") or 1.0))
        live_improved = spot > peak_spot + post_progress_step if direction == "BULLISH" else spot < peak_spot - post_progress_step
        if (direction == "BULLISH" and spot > peak_spot) or (direction == "BEARISH" and spot < peak_spot):
            active["post_t1_peak_spot"] = spot
        if live_improved:
            active["post_t1_last_progress_at"] = quote_received_at.isoformat()
            active["post_t1_no_progress_bars"] = 0
    if active.get("t1_hit") and latest_bid is not None:
        post_peak = float(active.get("post_t1_peak_premium_bid") or 0.0)
        if latest_bid > post_peak:
            active["post_t1_peak_premium_bid"] = latest_bid
            active["post_t1_last_progress_at"] = quote_received_at.isoformat()
            active["post_t1_no_progress_bars"] = 0

    thesis = dict(market_thesis) if isinstance(market_thesis, Mapping) else {}
    thesis_direction = str(thesis.get("direction") or "RANGE").upper()
    thesis_state = str(thesis.get("state") or "RANGE").upper()
    if thesis_direction in {"BULLISH", "BEARISH"} and thesis_direction != direction and bool(thesis.get("break_confirmed")):
        return close("THESIS_STRUCTURAL_REVERSAL", quote_received_at, spot, {
            "market_thesis_state": thesis_state, "broken_level": thesis.get("broken_level"),
            "market_thesis_reason": thesis.get("reason"),
        })

    # Ratchet stop before evaluating slower premium/time exits.
    trail_update = _trail_active_stop(active, levels, spot, structure, config,
                                      market_thesis=thesis, oi_structure=oi_structure)
    if trail_update:
        active["last_trailing_stop_update"] = {**trail_update, "at": quote_received_at.isoformat()}

    consensus_now = direction_consensus if isinstance(direction_consensus, Mapping) else {}
    consensus_direction = str(consensus_now.get("direction") or "MIXED").upper()
    consensus_score = abs(float(consensus_now.get("score") or 0.0))
    opposite = "BEARISH" if direction == "BULLISH" else "BULLISH"
    execution_now = str(structure.get("execution_direction") or "UNKNOWN").upper()
    execution_3m_now = str(structure.get("execution_3m_direction") or "UNKNOWN").upper()
    context_15m_now = str(structure.get("market_context_15m_bias") or "UNKNOWN").upper()
    supportive = _runner_support_score(direction, oi_structure)

    # Opposite 1m/3m price action is a pullback while the thesis level survives;
    # it no longer closes a trend trade by itself.
    thesis_in_pullback = "PULLBACK" in thesis_state or "TEST" in thesis_state
    if (execution_now == opposite and execution_3m_now == opposite) or thesis_in_pullback:
        active["management_state"] = "RUNNER_PULLBACK" if active.get("t1_hit") else "THESIS_PULLBACK"
    elif active.get("t1_hit"):
        active["management_state"] = "RUNNER_TRENDING"
    else:
        active["management_state"] = "ENTRY_ACTIVE"

    elapsed_minutes = max(0.0, (quote_received_at - opened_at).total_seconds() / 60.0)
    atr1 = float(structure.get("atr_1m") or (active.get("risk_plan") or {}).get("atr_1m") or 0.0)
    best_extreme = float(active.get("favourable_spot_extreme") or entry_spot)
    best_move = (best_extreme - entry_spot) if direction == "BULLISH" else (entry_spot - best_extreme)

    premium_loss_pct = 0.0
    peak_drawdown_pct = 0.0
    if latest_bid is not None:
        entry_ask = float(active.get("entry_premium_ask") or 0.0)
        peak_bid = float(active.get("peak_premium_bid") or latest_bid)
        premium_loss_pct = max(0.0, (entry_ask - latest_bid) / entry_ask * 100.0) if entry_ask > 0 else 0.0
        peak_drawdown_pct = max(0.0, (peak_bid - latest_bid) / peak_bid * 100.0) if peak_bid > 0 else 0.0
        active["premium_loss_pct"] = premium_loss_pct
        active["premium_peak_drawdown_pct"] = peak_drawdown_pct
        if premium_loss_pct >= config.max_premium_loss_pct:
            return close("PREMIUM_MAX_LOSS", quote_received_at, spot,
                         {"premium_bid": latest_bid, "entry_ask": entry_ask, "premium_loss_pct": premium_loss_pct})

    if not active.get("t1_hit"):
        sideways_votes = (
            int(execution_now == "MIXED") + int(execution_3m_now in {"MIXED", "SIDEWAYS"})
            + int(context_15m_now in {"SIDEWAYS", "TRANSITION"})
            + int(consensus_score <= config.sideways_consensus_abs_max)
        )
        no_progress = atr1 > 0 and best_move < config.sideways_max_progress_atr * atr1
        if elapsed_minutes >= config.sideways_exit_minutes and no_progress and sideways_votes >= 2:
            # Supportive OI earns time only while premium remains healthy.
            if latest_bid is None or premium_loss_pct >= min(6.0, config.premium_decay_min_loss_pct) or supportive < config.thesis_oi_support_score_min:
                return close("SIDEWAYS_NO_PROGRESS", quote_received_at, spot, {
                    "elapsed_minutes": elapsed_minutes, "best_favourable_spot_move": best_move,
                    "atr_1m": atr1, "premium_loss_pct": premium_loss_pct,
                    "oi_support_score": supportive, "market_thesis_state": thesis_state,
                })
        if (latest_bid is not None and elapsed_minutes >= config.premium_decay_review_minutes
                and no_progress and premium_loss_pct >= config.premium_decay_min_loss_pct):
            return close("PREMIUM_DECAY_NO_PROGRESS", quote_received_at, spot, {
                "premium_bid": latest_bid, "premium_loss_pct": premium_loss_pct,
                "elapsed_minutes": elapsed_minutes, "best_favourable_spot_move": best_move, "atr_1m": atr1,
            })
    else:
        # Dedicated post-T1 runner economics.
        t1_at = parse_datetime(active.get("post_t1_started_at")) or parse_datetime(active.get("t1_hit_at")) or quote_received_at
        last_progress_at = parse_datetime(active.get("post_t1_last_progress_at")) or t1_at
        stall_minutes = max(0.0, (quote_received_at - last_progress_at).total_seconds() / 60.0)
        no_progress_bars = int(stall_minutes // 3.0)
        active["post_t1_no_progress_bars"] = no_progress_bars
        required_bars = int(config.post_t1_min_no_progress_bars)
        if supportive >= config.thesis_oi_support_score_min and thesis_direction == direction:
            required_bars += int(config.post_t1_supportive_oi_extra_bars)
        active["runner_required_no_progress_bars"] = required_bars

        post_peak = float(active.get("post_t1_peak_premium_bid") or latest_bid or 0.0)
        post_drawdown = (max(0.0, (post_peak - latest_bid) / post_peak * 100.0)
                         if latest_bid is not None and post_peak > 0 else 0.0)
        active["post_t1_peak_drawdown_pct"] = post_drawdown
        drawdown_limit = _adaptive_runner_drawdown_limit(active, quote_received_at, structure, thesis, oi_structure, config)
        active["post_t1_drawdown_limit_pct"] = drawdown_limit

        theta_fraction = 0.0
        if option_quote is not None and option_quote.theta is not None and post_peak > 0:
            try:
                expected_theta_points = abs(float(option_quote.theta)) * stall_minutes / 1440.0
                theta_fraction = expected_theta_points / post_peak
            except (TypeError, ValueError, OverflowError):
                theta_fraction = 0.0
        active["post_t1_theta_fraction_since_progress"] = theta_fraction

        if latest_bid is not None and post_drawdown >= drawdown_limit:
            return close("POST_T1_PREMIUM_PROFIT_PROTECTION", quote_received_at, spot, {
                "premium_bid": latest_bid, "post_t1_peak_premium_bid": post_peak,
                "post_t1_peak_drawdown_pct": post_drawdown, "drawdown_limit_pct": drawdown_limit,
                "oi_support_score": supportive, "market_thesis_state": thesis_state,
            })
        stall_economic = latest_bid is not None and (
            post_drawdown >= max(4.0, drawdown_limit * 0.45)
            and (theta_fraction >= config.post_t1_theta_fraction_limit or post_drawdown >= drawdown_limit * 0.65)
        )
        if no_progress_bars >= required_bars and stall_economic:
            return close("POST_T1_THETA_NO_PROGRESS", quote_received_at, spot, {
                "no_progress_3m_bars": no_progress_bars, "required_bars": required_bars,
                "minutes_since_runner_progress": stall_minutes, "premium_bid": latest_bid,
                "post_t1_peak_premium_bid": post_peak, "post_t1_peak_drawdown_pct": post_drawdown,
                "theta_fraction_since_progress": theta_fraction, "oi_support_score": supportive,
                "market_thesis_state": thesis_state,
            })

    active["last_checked_at"] = quote_received_at.isoformat()
    active["last_spot"] = spot
    active["last_oi_direction"] = oi.get("raw_label", oi.get("label"))
    active["last_price_execution"] = structure.get("execution_direction")
    active["last_market_thesis_state"] = thesis_state
    active["monitoring_status"] = "ACTIVE" if latest_bid is not None else "SPOT_ONLY_OPTION_QUOTE_UNAVAILABLE"
    summary = {
        "position_open": True, "position_id": active.get("position_id"), "instrument_key": active.get("instrument_key"),
        "side": active.get("side"), "strike": active.get("strike"), "direction": direction,
        "entry_spot": entry_spot, "stop_underlying": active.get("stop_underlying"),
        "t1_underlying": t1, "t2_underlying": t2, "t1_hit": active.get("t1_hit"),
        "remaining_pct": active.get("remaining_pct"), "premium_bid": latest_bid,
        "premium_loss_pct": active.get("premium_loss_pct"), "monitoring_status": active.get("monitoring_status"),
        "management_state": active.get("management_state"), "market_thesis_state": thesis_state,
        "post_t1_peak_drawdown_pct": active.get("post_t1_peak_drawdown_pct"),
        "post_t1_drawdown_limit_pct": active.get("post_t1_drawdown_limit_pct"),
        "post_t1_no_progress_bars": active.get("post_t1_no_progress_bars"),
        "oi_support_score": supportive, "direction_consensus": dict(consensus_now),
    }
    return active, events, "POSITION_ACTIVE", summary

def queue_notification(state: dict[str, Any], signal_key: str, payload: Mapping[str, Any], created_at: datetime) -> bool:
    """Queue a unique entry or position-event alert without replaying prior keys."""
    normalize_notification_queue(state)
    key = str(signal_key or "").strip()
    if not key:
        raise ScannerError("NOTIFICATION_KEY_MISSING", "Notification event has no deterministic key")
    if key in set(str(x) for x in state.get("delivered_signal_keys", [])):
        return False
    if key in {_notification_key(item) for item in state.get("pending_notifications", [])}:
        return False
    item_payload = dict(payload)
    item_payload["signal_key"] = key
    item_payload["notification_status"] = "QUEUED"
    state["pending_notifications"].append({
        "signal_key": key,
        "payload": compact_audit_record(item_payload),
        "attempts": 0,
        "status": "QUEUED",
        "created_at": created_at.astimezone(IST).isoformat(),
    })
    normalize_notification_queue(state)
    return True


def _record_closed_position(state: dict[str, Any], position: Mapping[str, Any]) -> None:
    history = _ensure_state_list(state, "position_history")
    history.append(json_safe(dict(position)))
    state["position_history"] = history[-200:]
    state["last_position_exit"] = {
        "position_id": position.get("position_id"),
        "signal_key": position.get("signal_key"),
        "direction": position.get("direction"),
        "exit_reason": position.get("exit_reason"),
        "closed_at": position.get("closed_at"),
        "exit_spot": position.get("exit_spot"),
    }


def _find_confirmed_reversal_in_audit(
    audit_path: Path, opened_at: datetime, old_direction: str, config: Config,
) -> Optional[dict[str, Any]]:
    """Find the first fully confirmed opposite reversal after a legacy signal.

    This is used only when explicitly restoring one v106 signal from its audit
    log. It does not treat an OI-only reversal watch or price-only turn as a
    position exit.
    """
    opposite = "BEARISH" if old_direction == "BULLISH" else "BULLISH"
    if not audit_path.exists():
        return None
    try:
        if audit_path.stat().st_size > 30_000_000:
            raise ScannerError("POSITION_AUDIT_TOO_LARGE", "Legacy audit file exceeds the 30 MB reconciliation safety limit")
        with audit_path.open("r", encoding="utf-8") as stream:
            for line_number, line in enumerate(stream, 1):
                if not line.strip():
                    continue
                row = json.loads(line)
                timestamp = parse_datetime(row.get("timestamp"))
                if timestamp is None or timestamp <= opened_at:
                    continue
                oi = row.get("oi") if isinstance(row.get("oi"), Mapping) else {}
                structure = row.get("structure") if isinstance(row.get("structure"), Mapping) else {}
                setup = row.get("setup") if isinstance(row.get("setup"), Mapping) else None
                if setup is None:
                    continue
                if str(oi.get("raw_label") or "").upper() != opposite:
                    continue
                if str(oi.get("label") or "").upper() != opposite:
                    continue
                if int(oi.get("persistence_count") or 0) < 2:
                    continue
                if oi.get("transition_status") != "DIRECTION_PERSISTENT":
                    continue
                if float(oi.get("confidence") or 0.0) < config.min_oi_direction_confidence:
                    continue
                if not oi.get("compared_to_previous_successful_snapshot"):
                    continue
                oi_age = oi.get("oi_age_seconds")
                if oi_age is not None and float(oi_age) > config.max_oi_age_seconds:
                    continue
                if row.get("option_chain_status") != "SUCCESS" or row.get("option_chain_error"):
                    continue
                if str(structure.get("execution_direction") or "UNKNOWN").upper() != opposite:
                    continue
                if str(setup.get("direction") or "").upper() != opposite:
                    continue
                setup_at = parse_datetime(setup.get("confirmed_at"))
                spot = float(row.get("spot") or 0.0)
                trigger = float(setup.get("trigger") or 0.0)
                invalidation = float(setup.get("invalidation") or 0.0)
                confidence = float(setup.get("price_confidence") or 0.0)
                if setup_at is None or not spot > 0 or not trigger > 0 or not invalidation > 0:
                    continue
                setup_age = (timestamp - setup_at).total_seconds()
                if setup_age < -1 or setup_age > config.setup_max_age_minutes * 60:
                    continue
                if confidence < config.min_mixed_price_confirmation:
                    continue
                atr1 = float(structure.get("atr_1m") or 0.0)
                tolerance = max(0.5, atr1 * 0.15)
                if opposite == "BEARISH":
                    trigger_valid = spot < invalidation and spot <= trigger + tolerance
                else:
                    trigger_valid = spot > invalidation and spot >= trigger - tolerance
                if not trigger_valid:
                    continue
                return {
                    "timestamp": timestamp.isoformat(), "spot": spot,
                    "direction": opposite, "setup_direction": opposite,
                    "setup_kind": setup.get("kind"), "setup_trigger": trigger,
                    "setup_invalidation": invalidation,
                    "setup_confirmed_at": setup_at.isoformat(),
                    "setup_price_confidence": confidence,
                    "oi_confidence": oi.get("confidence"),
                    "oi_persistence_count": oi.get("persistence_count"),
                    "price_execution_direction": structure.get("execution_direction"),
                    "audit_line": line_number,
                }
    except ScannerError:
        raise
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise ScannerError("POSITION_AUDIT_READ_FAILED", f"Cannot safely inspect legacy reversal audit: {exc}") from exc
    return None


def reconcile_legacy_position(config: Config, signal_key: str) -> dict[str, Any]:
    """Explicitly reconcile a v106 advisory position by legacy signal key, or confirm flat.

    A v106 `last_signal` is not proof of the active position because v106 could
    select multiple strikes without position ownership. Reconciliation is
    intentionally explicit; the scanner never guesses which historical signal
    the user was following.
    """
    key = signal_key.strip()
    if not key:
        raise ScannerError("POSITION_RECONCILIATION_VALUE_REQUIRED", "Supply 'flat' or an exact historical signal key")
    state = read_state(config.state_file)
    _ensure_state_list(state, "position_history")
    existing_position = state.get("active_position")
    if isinstance(existing_position, Mapping) and existing_position.get("status") == "OPEN":
        if key.casefold() != "flat" and str(existing_position.get("signal_key")) != key:
            raise ScannerError("ACTIVE_POSITION_ALREADY_EXISTS", "An active position is already stored; reconcile it as flat or use its exact signal key")
    if key.casefold() == "flat":
        old = state.get("active_position")
        if isinstance(old, Mapping) and old.get("status") == "OPEN":
            old_closed = dict(old)
            old_closed.update({"status": "CLOSED", "exit_reason": "OPERATOR_CONFIRMED_FLAT", "closed_at": now_ist().isoformat(), "remaining_pct": 0.0})
            _record_closed_position(state, old_closed)
        state["active_position"] = None
        state["position_reconciliation_required"] = False
        state["position_reconciliation_reason"] = None
        state["position_reconciled_at"] = now_ist().isoformat()
        state["position_entry_block_after"] = state["position_reconciled_at"]
        atomic_write_json(config.state_file, state)
        return {"reconciled": "FLAT", "active_position": None}

    session = str(state.get("session_date") or now_ist().date().isoformat())
    audit_path = config.audit_dir / f"market_scan_{session}.jsonl"
    if not audit_path.exists():
        raise ScannerError("POSITION_AUDIT_NOT_FOUND", f"Cannot find legacy audit record {audit_path}")
    matches: list[dict[str, Any]] = []
    try:
        if audit_path.stat().st_size > 30_000_000:
            raise ScannerError("POSITION_AUDIT_TOO_LARGE", "Legacy audit file exceeds the 30 MB reconciliation safety limit")
        with audit_path.open("r", encoding="utf-8") as stream:
            for line_number, line in enumerate(stream, 1):
                if not line.strip():
                    continue
                record = json.loads(line)
                if record.get("decision") == "QUALIFIED" and record.get("signal_key") == key:
                    matches.append(record)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ScannerError("POSITION_AUDIT_READ_FAILED", f"Cannot safely read legacy audit: {exc}") from exc
    if len(matches) != 1:
        raise ScannerError("POSITION_SIGNAL_NOT_UNIQUE", f"Expected exactly one QUALIFIED audit record for key {key}; found {len(matches)}")
    record = matches[0]
    selected = record.get("selected_contract")
    risk = record.get("risk_plan")
    setup = record.get("setup")
    opened_at = parse_datetime(record.get("timestamp"))
    if not all(isinstance(value, Mapping) for value in (selected, risk, setup)) or opened_at is None:
        raise ScannerError("POSITION_AUDIT_INCOMPLETE", "Legacy signal record lacks selected contract, risk plan, setup or valid timestamp")
    if opened_at.date().isoformat() != session:
        raise ScannerError("POSITION_SESSION_MISMATCH", "Legacy signal belongs to a different trading session")
    if opened_at.date() != now_ist().date():
        raise ScannerError("POSITION_SESSION_EXPIRED", "A prior-session advisory signal cannot be restored as an open intraday position; reconcile flat or wait for a new-session signal")
    last_candle = opened_at.replace(second=0, microsecond=0)
    active = create_active_position(key, opened_at, setup, selected, risk,
                                    Candle(last_candle, float(record.get("spot") or risk.get("entry_underlying")),
                                           float(record.get("spot") or risk.get("entry_underlying")),
                                           float(record.get("spot") or risk.get("entry_underlying")),
                                           float(record.get("spot") or risk.get("entry_underlying"))),
                                    config, recovered=True)
    active["last_monitored_candle"] = last_candle.isoformat()
    replay_reversal = _find_confirmed_reversal_in_audit(audit_path, opened_at,
                                                        str(setup.get("direction") or ""), config)
    if replay_reversal:
        active["pending_replay_reversal"] = replay_reversal
    state["active_position"] = active
    state["position_reconciliation_required"] = False
    state["position_reconciliation_reason"] = None
    state["position_reconciled_at"] = now_ist().isoformat()
    state["position_reconciliation_source"] = str(audit_path)
    atomic_write_json(config.state_file, state)
    return {"reconciled": "ACTIVE", "signal_key": key, "instrument_key": active["instrument_key"],
            "side": active["side"], "strike": active["strike"], "opened_at": active["opened_at"],
            "pending_replay_reversal": replay_reversal}

def _option_record_from_active_position(active: Mapping[str, Any]) -> OptionRecord:
    selected = active.get("selected_contract")
    if not isinstance(selected, Mapping):
        raise ScannerError("ACTIVE_POSITION_INVALID", "Stored active position has no selected contract")
    try:
        return OptionRecord(
            instrument_key=str(active.get("instrument_key") or selected["instrument_key"]),
            expiry=parse_expiry(active.get("expiry") or selected.get("expiry")) or date.min,
            strike=float(active.get("strike") or selected["strike"]),
            side=str(active.get("side") or selected["side"]),
            ltp=float(selected.get("ltp") or 0.0),
            oi=float(selected.get("oi") or 0.0),
            volume=float(selected.get("volume") or 0.0),
            previous_session_oi=None,
            chain_bid=float(selected.get("reference_bid") or 0.0),
            chain_ask=float(selected.get("reference_entry_ask") or 0.0),
            chain_bid_qty=float(selected.get("bid_qty") or 0.0),
            chain_ask_qty=float(selected.get("ask_qty") or 0.0),
            delta=float(selected["delta"]) if selected.get("delta") is not None else None,
            gamma=float(selected["gamma"]) if selected.get("gamma") is not None else None,
            theta=float(selected["theta"]) if selected.get("theta") is not None else None,
            vega=float(selected["vega"]) if selected.get("vega") is not None else None,
            iv=float(selected["iv_percent"]) if selected.get("iv_percent") is not None else None,
        )
    except (KeyError, TypeError, ValueError, OverflowError) as exc:
        raise ScannerError("ACTIVE_POSITION_INVALID", f"Stored active contract cannot be normalized: {exc}") from exc



def _build_live_records(records: Sequence[OptionRecord], instrument_rows: Sequence[Mapping[str, Any]], spot: float, step_limit: int = 6) -> tuple[list[OptionRecord], list[str]]:
    strikes = sorted({r.strike for r in records})
    if not strikes:
        return [], []
    atm = min(strikes, key=lambda s: abs(s - spot))
    index = strikes.index(atm)
    step_values = [b - a for a, b in zip(strikes, strikes[1:]) if b > a]
    step = median(step_values) if step_values else 50.0
    eligible_strikes = set(strikes[max(0, index - step_limit):min(len(strikes), index + step_limit + 1)])
    selected = [r for r in records if r.strike in eligible_strikes]
    return selected, [r.instrument_key for r in selected]


def _levels_summary(levels: Sequence[PriceLevel], spot: float) -> dict[str, Any]:
    below = sorted((x for x in levels if x.side == "SUPPORT" and x.price < spot), key=lambda x: x.price, reverse=True)
    above = sorted((x for x in levels if x.side == "RESISTANCE" and x.price > spot), key=lambda x: x.price)
    return {
        "nearest_support": {"price": below[0].price, "source": below[0].source, "strength": below[0].strength} if below else None,
        "nearest_resistance": {"price": above[0].price, "source": above[0].source, "strength": above[0].strength} if above else None,
        "support_count": len(below), "resistance_count": len(above),
    }


def _market_open(now: datetime) -> bool:
    local = now.astimezone(IST)
    if local.weekday() >= 5:
        return False
    t = local.time()
    return dtime(9, 15) <= t <= dtime(15, 30)


def _empty_oi(status: str = "MISSING") -> dict[str, Any]:
    return {"label": status, "score": 0.0, "bull_score": 0.0, "bear_score": 0.0, "confidence": 0.0, "score_margin": 0.0, "snapshot_status": "MISSING", "compared_to_previous_successful_snapshot": False, "features": [], "call_oi_walls": [], "put_oi_walls": []}


def run_scan(config: Config, *, now: Optional[datetime] = None, client: Optional[UpstoxClient] = None, master: Optional[InstrumentMaster] = None) -> dict[str, Any]:
    """Run one idempotent scan and return full structured evidence."""
    if now is None:
        now = now_ist()
    if now.tzinfo is None or now.utcoffset() is None:
        raise ScannerError("TIMEZONE_INVALID", "Scan evaluation time must be timezone-aware")
    now = now.astimezone(IST)
    scan_monotonic_start = time.monotonic()
    session_date = now.date()
    base_result: dict[str, Any] = {"scanner_version": VERSION, "schema_version": SCHEMA_VERSION, "timestamp": now.isoformat(), "session_date": session_date.isoformat(), "decision": "NO_TRADE", "reason_code": "UNINITIALIZED"}
    if not _market_open(now):
        return {**base_result, "regime": "UNKNOWN", "oi_label": "MISSING", "reason_code": "MARKET_CLOSED", "decision": "NO_TRADE"}
    state = read_state(config.state_file)
    same_session = state.get("session_date") == session_date.isoformat()
    previous_processed = parse_datetime(state.get("last_processed_candle")) if same_session else None
    if not same_session:
        # Reset market baselines, but never silently discard an unresolved position.
        prior_position = state.get("active_position")
        reconciliation_required = bool(state.get("position_reconciliation_required"))
        reconciliation_reason = state.get("position_reconciliation_reason")
        if isinstance(prior_position, Mapping) and prior_position.get("status") == "OPEN":
            reconciliation_required = True
            reconciliation_reason = "OPEN_POSITION_CROSSED_SESSION_BOUNDARY"
        state = {
            "schema_version": SCHEMA_VERSION,
            "scanner_version": VERSION,
            "session_date": session_date.isoformat(),
            "chain_snapshots": [],
            "session_oi_baseline": None,
            "seen_signal_keys": [],
            "pending_notifications": state.get("pending_notifications", []),
            "delivered_signal_keys": state.get("delivered_signal_keys", []),
            "notification_history": state.get("notification_history", []),
            "active_position": prior_position,
            "position_history": state.get("position_history", []),
            "position_reconciliation_required": reconciliation_required,
            "position_reconciliation_reason": reconciliation_reason,
            "position_entry_block_after": state.get("position_entry_block_after"),
            "last_position_exit": state.get("last_position_exit"),
            "last_processed_candle": None,
            "setup_watch": None,
            "market_thesis": None,
            "thesis_history": [],
        }
    for collection in (
        "chain_snapshots", "seen_signal_keys", "pending_notifications",
        "delivered_signal_keys", "notification_history", "oi_evidence_history", "position_history", "thesis_history",
    ):
        _ensure_state_list(state, collection)
    state.setdefault("active_position", None)
    state.setdefault("position_reconciliation_required", False)
    state.setdefault("market_thesis", None)
    state.setdefault("thesis_history", [])
    normalize_notification_queue(state)
    client = client or UpstoxClient(config.token, config.request_timeout, config.max_retries)
    master = master or InstrumentMaster(client, config.instrument_cache, config.instrument_cache_hours)
    index_row: Optional[dict[str, Any]] = None
    expiry: Optional[date] = None
    chain_records: list[OptionRecord] = []
    spot_chain = 0.0
    chain_time: Optional[datetime] = None
    prior_snapshot: Optional[Mapping[str, Any]] = None
    baseline: Optional[Mapping[str, Any]] = None
    oi = _empty_oi()
    chain_refresh_ok = False
    chain_refresh_error: Optional[ScannerError] = None
    try:
        if now.time() < dtime(9, 16) and not state.get("active_position") and not state.get("position_reconciliation_required"):
            raise ScannerError("OPENING_CANDLE_WARMUP", "Waiting for the first completed one-minute candle")
        master.load(now)
        index_row = master.resolve_index()
        index_key = str(index_row["instrument_key"])
        expiry = master.resolve_expiry(index_key, session_date, config.explicit_expiry)
        option_instruments = master.option_instruments(index_key, expiry)
        chain_url = f"{API_BASE}/v2/option/chain?{urllib.parse.urlencode({'instrument_key': index_key, 'expiry_date': expiry.isoformat()})}"
        prior_snapshot = _recent_current_snapshot(state, session_date, expiry)
        baseline = _first_session_baseline(state, session_date, expiry)
        try:
            chain_payload = client.get_json(chain_url)
            chain_time = now_ist()
            spot_chain, chain_records = parse_option_chain(chain_payload, expiry, chain_time)
            oi = calculate_oi_evidence(chain_records, prior_snapshot, baseline, spot_chain, chain_time, config, state.get("chain_snapshots", []))
            stabilize_oi_evidence(oi, state, session_date, expiry)
            # Fetch/receive time is distinct from the actual interval between snapshots.
            oi["oi_age_seconds"] = max(0.0, (now_ist() - chain_time).total_seconds())
            oi["source_refresh_status"] = "SUCCESS"
            oi["source_refresh_error"] = None
            chain_snapshot = _snapshot_payload(chain_records, spot_chain, session_date, expiry, chain_time)
            # First successful snapshot sets the session baseline; subsequent
            # successful observations are kept in fetch order, never replaced by errors.
            old_baseline = state.get("session_oi_baseline") or {}
            if old_baseline.get("session_date") != session_date.isoformat() or old_baseline.get("expiry") != expiry.isoformat():
                state["session_oi_baseline"] = chain_snapshot
            existing_snapshots = state.get("chain_snapshots", [])
            if not existing_snapshots or existing_snapshots[-1].get("fetched_at") != chain_snapshot["fetched_at"]:
                existing_snapshots.append(chain_snapshot)
            state["chain_snapshots"] = existing_snapshots[-16:]
            state["last_successful_snapshot_at"] = chain_time.isoformat()
            state["latest_oi_evidence"] = persisted_oi_evidence(oi)
            # Persist the successful observation before later market-data calls.
            # This survives a subsequent quote/candle failure or interrupted job.
            atomic_write_json(config.state_file, state)
            chain_refresh_ok = True
        except ScannerError as chain_exc:
            chain_refresh_error = chain_exc
            # A failed refresh never creates an OI delta. Retain last successful
            # same-session evidence for context while continuing to update spot
            # structure. Entries remain blocked because current Greeks/IV are not fresh.
            prior_snapshot = _recent_current_snapshot(state, session_date, expiry)
            if prior_snapshot is not None:
                chain_time = parse_datetime(prior_snapshot.get("fetched_at"))
                try:
                    spot_chain = float(prior_snapshot.get("spot") or 0.0)
                    chain_records = [_option_record_from_state(r) for r in prior_snapshot.get("rows", []) if isinstance(r, Mapping)]
                except (TypeError, ValueError, KeyError) as fallback_exc:
                    LOG.warning("Previous option snapshot could not be normalized (%s)", type(fallback_exc).__name__)
                    chain_records = []
                    spot_chain = 0.0
                retained = state.get("latest_oi_evidence") or _empty_oi()
                oi = dict(retained)
                age = max(0.0, (now - chain_time).total_seconds()) if chain_time else float(config.max_oi_age_seconds + 1)
                original_confidence = float(oi.get("confidence") or 0.0)
                decay = max(0.0, 1.0 - age / max(1.0, config.max_oi_age_seconds))
                oi.update({
                    "oi_age_seconds": age,
                    "stored_confidence_before_age_decay": original_confidence,
                    "confidence": original_confidence * decay,
                    "confidence_decay_factor": decay,
                    "snapshot_status": "RETAINED_AFTER_REFRESH_FAILURE",
                    "source_refresh_status": "FAILED_RETAINED_LAST_SUCCESSFUL_SNAPSHOT",
                    "source_refresh_error": chain_exc.code,
                    "current_snapshot_delta_available": False,
                })
            else:
                oi = _empty_oi("MISSING")
                oi.update({"source_refresh_status": "FAILED_NO_SESSION_BASELINE", "source_refresh_error": chain_exc.code, "current_snapshot_delta_available": False, "oi_age_seconds": None})
        # Fetch index and nearest current futures candles even if chain refresh failed.
        index_candles = fetch_candles(client, index_key, now, minutes=1)
        freshness = candle_freshness(index_candles, now)
        # Retry the same snapshot boundary; do not add an unfinished candle.
        for _ in range(2):
            if freshness["latest_expected_available"]:
                break
            time.sleep(1.0)
            index_candles = fetch_candles(client, index_key, now, minutes=1)
            freshness = candle_freshness(index_candles, now)
        base_result["candle_freshness"] = freshness
        latest_close_time = index_candles[-1].close_time
        candle_age = (now - latest_close_time).total_seconds()
        if candle_age < -1 or candle_age > config.max_candle_age_seconds:
            raise ScannerError("CANDLES_STALE", f"Latest completed candle age is {candle_age:.0f}s")
        daily_candles = fetch_daily_candles(client, index_key, now)
        future_row = master.resolve_future(index_key, session_date)
        futures_candles: list[Candle] = []
        future_key = str(future_row.get("instrument_key")) if future_row else ""
        if future_key:
            try:
                futures_candles = fetch_candles(client, future_key, now, minutes=1)
            except ScannerError as exc:
                LOG.warning("Futures context unavailable (%s); VWAP remains unavailable", exc.code)
        futures_vwap = valid_futures_vwap(futures_candles)
        bars_3m = aggregate_candles(index_candles, 3, now)
        bars_15m = aggregate_candles(index_candles, 15, now)
        structure = price_regime(index_candles, bars_3m, bars_15m, config)
        spot_quote_keys = [index_key] + ([future_key] if future_key else [])
        live_records, _ = _build_live_records(chain_records, option_instruments, spot_chain, step_limit=6)
        all_quote_keys = spot_quote_keys + [r.instrument_key for r in live_records]
        active_before_quotes = state.get("active_position")
        active_instrument_key = str(active_before_quotes.get("instrument_key") or "") if isinstance(active_before_quotes, Mapping) else ""
        if active_instrument_key:
            all_quote_keys.append(active_instrument_key)
        full_quotes = get_full_quotes(client, all_quote_keys)
        raw_spot_quote = full_quotes.get(index_key)
        if raw_spot_quote is None:
            raise ScannerError("SPOT_QUOTE_MISSING", "Full Market Quotes did not return NIFTY 50 index quote")
        spot, spot_quote_time, _ = _spot_from_full_quote(raw_spot_quote)
        if spot_quote_time is None:
            raise ScannerError("SPOT_QUOTE_TIMESTAMP_MISSING", "NIFTY 50 live quote has no source timestamp")
        # `now` is captured at scan start. Compare quote time with the actual
        # local receipt instant, reconstructed from monotonic elapsed time.
        quote_received_at = now + timedelta(seconds=max(0.0, time.monotonic() - scan_monotonic_start))
        spot_age, quote_clock_skew, quote_timestamp_status = quote_timing(spot_quote_time, quote_received_at)
        if spot_age > config.max_quote_age_seconds:
            raise ScannerError("SPOT_QUOTE_STALE", f"NIFTY spot quote age is {spot_age:.0f}s")
        divergence_signed = spot - index_candles[-1].close
        spot_context = {
            "spot": spot,
            "spot_quote_timestamp": spot_quote_time.isoformat(),
            "spot_quote_received_at": quote_received_at.isoformat(),
            "spot_quote_age_seconds": spot_age,
            "spot_quote_clock_skew_seconds": quote_clock_skew,
            "spot_quote_timestamp_status": quote_timestamp_status,
            "latest_completed_candle_time": index_candles[-1].start.isoformat(),
            "latest_candle_close": index_candles[-1].close,
            "spot_vs_last_close_points": abs(divergence_signed),
            "spot_minus_last_close_points": divergence_signed,
        }
        futures_quote = full_quotes.get(future_key) if future_key else None
        future_expiry = parse_expiry(future_row.get("expiry")) if future_row else None
        future_context = build_futures_context(
            futures_quote, futures_candles, spot, quote_received_at,
            max_quote_age_seconds=config.max_quote_age_seconds,
            max_candle_age_seconds=config.max_candle_age_seconds,
            instrument_key=future_key or None,
            trading_symbol=future_row.get("trading_symbol") if future_row else None,
            expiry=future_expiry,
        )
        # Only a fresh futures VWAP with positive volume may become a level.
        futures_vwap = future_context["vwap"]
        levels = build_levels(
            index_candles, daily_candles, oi, futures_vwap, structure.get("atr_1m"), config,
            candles_3m=bars_3m, candles_15m=bars_15m,
        )
        level_summary = _levels_summary(levels, spot)
        oi_structure = build_oi_structure_context(oi, spot, config)
        previous_thesis = state.get("market_thesis") if isinstance(state.get("market_thesis"), Mapping) else None
        market_thesis = update_market_thesis(
            previous_thesis, spot, structure, levels, oi_structure, future_context, bars_3m, quote_received_at, config
        )
        structure = dict(structure)
        structure["market_thesis_state"] = market_thesis.get("state")
        structure["market_thesis_direction"] = market_thesis.get("direction")
        structure["market_thesis_support"] = market_thesis.get("anchor_support")
        structure["market_thesis_resistance"] = market_thesis.get("anchor_resistance")
        previous_thesis_key = (
            str((previous_thesis or {}).get("direction") or ""),
            str((previous_thesis or {}).get("state") or ""),
            (previous_thesis or {}).get("anchor_support"),
            (previous_thesis or {}).get("anchor_resistance"),
        )
        current_thesis_key = (
            str(market_thesis.get("direction") or ""), str(market_thesis.get("state") or ""),
            market_thesis.get("anchor_support"), market_thesis.get("anchor_resistance"),
        )
        if previous_thesis_key != current_thesis_key:
            thesis_history = _ensure_state_list(state, "thesis_history")
            thesis_history.append({
                "at": quote_received_at.isoformat(), "direction": market_thesis.get("direction"),
                "state": market_thesis.get("state"), "reason": market_thesis.get("reason"),
                "anchor_support": market_thesis.get("anchor_support"),
                "anchor_resistance": market_thesis.get("anchor_resistance"),
                "broken_level": market_thesis.get("broken_level"),
            })
            state["thesis_history"] = thesis_history[-120:]
        state["market_thesis"] = market_thesis
        tracked_setup = advance_setup_watch(index_candles, previous_processed, daily_candles, state, config, oi)
        if tracked_setup is not None and not tracked_setup.kind.startswith("V111_"):
            tracked_setup = None  # never upgrade an old version's watch into a v111 trade
        current_setup, price_evidence = v111_price_candidate(index_candles, levels, structure, market_thesis)
        setup = select_active_setup(current_setup, tracked_setup, spot, oi, structure, quote_received_at, config)
        direction_consensus = build_direction_consensus(oi, structure, future_context, setup, config, market_thesis)
        early_evidence = {"status": "REPLACED_BY_V111_PATHS"}
        oi_confirmation = v111_oi_confirmation(setup, oi, oi_structure, future_context, spot) if setup else {"approved": False, "reason": "NO_PRICE_CANDIDATE"}
        detected_new_setup = setup is not None and (tracked_setup is None or setup.confirmed_at != tracked_setup.confirmed_at or setup.direction != tracked_setup.direction)
        state["last_processed_candle"] = index_candles[-1].start.isoformat()
        # Freshness-validated futures quote/VWAP context was built before levels.
        if oi.get("raw_label") in {"BULLISH", "BEARISH"} and oi.get("label") == "MIXED":
            transition = oi.get("transition_status") or "PENDING_PERSISTENCE"
            oi_state = f"{transition}_{oi.get('raw_label')}"
        else:
            oi_state = oi.get("label", "MISSING")
        market_scenario = classify_market_scenario(oi, structure, future_context)
        base_result.update({"expiry": expiry.isoformat(), "underlying_key": index_key, "spot": spot, "spot_context": spot_context, "oi": {k: v for k, v in oi.items() if k != "features"}, "oi_label": oi.get("label", "MISSING"), "oi_state": oi_state, "oi_raw_label": oi.get("raw_label", oi.get("label", "MISSING")), "option_chain_status": oi.get("source_refresh_status", "SUCCESS" if chain_refresh_ok else "UNKNOWN"), "option_chain_error": chain_refresh_error.code if chain_refresh_error else None, "structure": structure, "regime": structure.get("regime"), "market_scenario": market_scenario, "levels": level_summary, "futures": future_context, "market_thesis": market_thesis, "oi_structure": oi_structure, "setup": json_safe(setup) if setup else None, "direction_consensus": direction_consensus, "decision": "NO_TRADE", "reason_code": "NO_CONFIRMED_SETUP"})

        base_result["local_reversal_watch"] = local_reversal_watch(index_candles, levels, structure, market_thesis)
        base_result["early_oi_reversal"] = early_evidence
        base_result["v111_evidence"] = {"price": price_evidence, "oi_confirmation": oi_confirmation}
        base_result["entry_gate_diagnostics"] = {
            "latest_candle_ready": freshness["latest_expected_available"],
            "price_1m": structure.get("execution_direction"),
            "price_3m": structure.get("execution_3m_direction"),
            "thesis_direction": market_thesis.get("direction"),
            "thesis_state": market_thesis.get("state"),
            "thesis_break_pending_at": market_thesis.get("break_pending_at"),
            "thesis_break_confirmed": market_thesis.get("break_confirmed"),
            "setup_before_consensus": json_safe(current_setup) if current_setup else None,
            "setup_after_consensus": json_safe(setup) if setup else None,
        }

        # Always record what single contract would currently rank first when a
        # directional consensus exists.  This is a shadow diagnostic only and
        # never creates a position by itself; it makes missed opportunities and
        # strike selection auditable after the fact.
        shadow_direction = str(direction_consensus.get("direction") or "MIXED")
        if chain_refresh_ok and shadow_direction in {"BULLISH", "BEARISH"}:
            try:
                shadow = select_option_and_risk(
                    shadow_direction, spot, spot_quote_time, chain_records, full_quotes, expiry,
                    quote_received_at, {"underlying_rr": None}, structure, config,
                )
                base_result["shadow_option_selection"] = {
                    "direction": shadow_direction,
                    "selected": {k: v for k, v in shadow.items() if k != "candidate_ranking"},
                    "candidate_ranking": shadow.get("candidate_ranking", []),
                }
            except ScannerError as shadow_exc:
                base_result["shadow_option_selection"] = {
                    "direction": shadow_direction, "status": "UNAVAILABLE",
                    "reason_code": shadow_exc.code, "message": str(shadow_exc),
                }
        if setup is not None:
            setup_age = (quote_received_at - setup.confirmed_at).total_seconds()
            base_result["setup_age_seconds"] = setup_age
            base_result["setup_direction"] = setup.direction
            base_result["setup_kind"] = setup.kind
            if detected_new_setup or not state.get("setup_watch") or _setup_from_state(state.get("setup_watch")) != setup:
                state["setup_watch"] = {
                    "direction": setup.direction, "kind": setup.kind,
                    "confirmed_at": setup.confirmed_at.isoformat(), "trigger": setup.trigger,
                    "invalidation": setup.invalidation, "source_level": setup.source_level,
                    "source": setup.source, "price_confidence": setup.price_confidence,
                }
        else:
            base_result["reason_code"] = "OI_BASELINE_MISSING" if not oi.get("compared_to_previous_successful_snapshot") else "NO_CONFIRMED_SETUP"
            prior_watch = _setup_from_state(state.get("setup_watch"))
            if prior_watch is not None:
                age = (now - prior_watch.confirmed_at).total_seconds()
                invalidated = (prior_watch.direction == "BULLISH" and spot <= prior_watch.invalidation) or (prior_watch.direction == "BEARISH" and spot >= prior_watch.invalidation)
                if age > config.setup_state_ttl_minutes * 60 or invalidated:
                    state["setup_watch"] = None

        active_position = state.get("active_position")
        position_events: list[dict[str, Any]] = []
        can_evaluate_new_entry = not bool(state.get("position_reconciliation_required"))
        allow_reversal_entry = False

        if state.get("position_reconciliation_required"):
            base_result.update({
                "decision": "NO_TRADE",
                "reason_code": "POSITION_RECONCILIATION_REQUIRED",
                "message": str(state.get("position_reconciliation_reason") or "Legacy position state must be explicitly reconciled as flat or by signal key."),
                "position_reconciliation_required": True,
            })
            can_evaluate_new_entry = False

        elif isinstance(active_position, Mapping) and active_position.get("status") == "OPEN":
            active_key = str(active_position.get("instrument_key") or "")
            active_expiry = str(active_position.get("expiry") or "")
            if active_expiry != expiry.isoformat():
                base_result.update({
                    "decision": "NO_TRADE",
                    "reason_code": "ACTIVE_POSITION_EXPIRY_MISMATCH",
                    "message": f"Active contract expiry {active_expiry} differs from current selected expiry {expiry.isoformat()}; position lock retained for reconciliation.",
                    "active_position_summary": {"position_id": active_position.get("position_id"), "instrument_key": active_key, "side": active_position.get("side"), "strike": active_position.get("strike")},
                })
                can_evaluate_new_entry = False
            else:
                active_record = next((record for record in chain_records if record.instrument_key == active_key), None)
                if active_record is None:
                    active_record = _option_record_from_active_position(active_position)
                raw_active_quote = full_quotes.get(active_key)
                option_quote = None
                if raw_active_quote is not None:
                    try:
                        option_quote = option_quote_from_full(active_record, raw_active_quote)
                    except (ScannerError, TypeError, ValueError, KeyError) as quote_exc:
                        LOG.warning("Active option quote could not be normalized (%s); spot management remains enabled", type(quote_exc).__name__)
                managed, position_events, management_code, management_detail = manage_active_position(
                    dict(active_position), index_candles, spot, quote_received_at,
                    oi, structure, setup, config,
                    chain_refresh_ok=chain_refresh_ok,
                    option_quote=option_quote,
                    levels=levels,
                    direction_consensus=direction_consensus,
                    market_thesis=market_thesis,
                    oi_structure=oi_structure,
                )
                if managed is not None:
                    state["active_position"] = managed
                    can_evaluate_new_entry = False
                    base_result.update({
                        "decision": "POSITION_OPEN",
                        "reason_code": "POSITION_T1_TO_T2_TRACKING" if managed.get("t1_hit") else "ACTIVE_POSITION_LOCKED",
                        "active_position_summary": management_detail,
                    })
                else:
                    closed_position = management_detail.get("closed_position") if isinstance(management_detail, Mapping) else None
                    state["active_position"] = None
                    if isinstance(closed_position, Mapping):
                        _record_closed_position(state, closed_position)
                    exit_reason = management_code
                    base_result["position_exit"] = {
                        "position_id": active_position.get("position_id"),
                        "side": active_position.get("side"),
                        "strike": active_position.get("strike"),
                        "direction": active_position.get("direction"),
                        "reason": exit_reason,
                        "detected_at": quote_received_at.isoformat(),
                        "recorded_close_time": (closed_position or {}).get("closed_at"),
                        "recorded_stop_or_exit_spot": (closed_position or {}).get("exit_spot"),
                        "reference_option_bid_at_detection": (closed_position or {}).get("exit_premium_bid"),
                        "option_quote_time": (closed_position or {}).get("last_premium_quote_at"),
                        "details": {k: v for k, v in management_detail.items() if k != "closed_position"},
                    }
                    # Never reverse on the same evaluation that closed a position.
                    # A newly completed setup after exit is required on a later scan.
                    state["position_entry_block_after"] = (closed_position or {}).get("closed_at") or quote_received_at.isoformat()
                    can_evaluate_new_entry = False
                    base_result.update({"decision": "POSITION_CLOSED", "reason_code": exit_reason})

                # Position-event notices have independent deterministic IDs, so
                # T1 and final exit are separate, non-duplicating notifications.
                for event_payload in position_events:
                    event_payload.update({
                        "oi": {k: v for k, v in oi.items() if k != "features"},
                        "oi_label": oi.get("label", "MISSING"),
                        "oi_raw_label": oi.get("raw_label", oi.get("label", "MISSING")),
                        "structure": structure,
                        "regime": structure.get("regime"),
                        "market_scenario": market_scenario,
                        "futures": future_context,
                        "direction_consensus": direction_consensus,
                        "market_thesis": market_thesis,
                        "oi_structure": oi_structure,
                    })
                    queue_notification(state, str(event_payload["signal_key"]), event_payload, quote_received_at)

        elif active_position is not None:
            if isinstance(active_position, Mapping) and active_position.get("status") == "CLOSED":
                # A previously persisted closed record is not an open lock, but
                # the next entry still requires a post-exit setup.
                state["active_position"] = None
                closed_at = parse_datetime(active_position.get("closed_at"))
                state["position_entry_block_after"] = (
                    closed_at.isoformat() if closed_at is not None
                    else state.get("position_entry_block_after") or quote_received_at.isoformat()
                )
                can_evaluate_new_entry = False
                base_result.update({
                    "decision": "NO_TRADE",
                    "reason_code": "WAITING_FOR_POST_EXIT_SETUP",
                    "message": "A persisted closed position was reconciled; a new setup confirmed after its exit is required.",
                })
            else:
                # Never treat an unknown/corrupt position state as permission
                # to select another contract.
                can_evaluate_new_entry = False
                base_result.update({
                    "decision": "NO_TRADE",
                    "reason_code": "ACTIVE_POSITION_STATE_INVALID",
                    "message": "An active-position record exists with an unsupported state; position lock retained for manual reconciliation.",
                })

        if can_evaluate_new_entry and not freshness["latest_expected_available"]:
            can_evaluate_new_entry = False
            base_result.update({"decision": "NO_TRADE", "reason_code": "WAITING_FOR_LATEST_CANDLE",
                                "message": "Latest completed one-minute candle is unavailable after retries; new entries blocked."})
        if can_evaluate_new_entry:
            exit_block = parse_datetime(state.get("position_entry_block_after"))
            if setup is None:
                base_result.setdefault("reason_code", "NO_CONFIRMED_SETUP")
            elif exit_block is not None and not allow_reversal_entry and setup.confirmed_at <= exit_block:
                base_result.update({
                    "decision": "NO_TRADE",
                    "reason_code": "WAITING_FOR_POST_EXIT_SETUP",
                    "message": "A fresh setup confirmed after the prior position exit is required before another same-session entry.",
                })
            elif exit_block is not None and not allow_reversal_entry:
                last_exit = state.get("last_position_exit") if isinstance(state.get("last_position_exit"), Mapping) else {}
                same_direction_reentry = str(last_exit.get("direction") or "").upper() == setup.direction
                newest_3m_close = (bars_3m[-1].start + timedelta(minutes=3)) if bars_3m else None
                if same_direction_reentry and (newest_3m_close is None or newest_3m_close <= exit_block):
                    base_result.update({
                        "decision": "NO_TRADE",
                        "reason_code": "WAITING_FOR_FRESH_3M_STRUCTURE",
                        "message": "Same-direction re-entry is allowed without a time cooldown, but requires a newly completed 3-minute structure bar after the prior exit.",
                    })
                    setup = None
            if can_evaluate_new_entry and setup is not None and base_result.get("reason_code") != "WAITING_FOR_FRESH_3M_STRUCTURE":
                setup_age = (quote_received_at - setup.confirmed_at).total_seconds()
                max_setup_age = config.setup_max_age_minutes
                if setup_age < -1 or setup_age > max_setup_age * 60:
                    raise ScannerError("MISSED_OR_STALE_SETUP", f"Setup confirmation is {setup_age:.0f}s old; no backdated entry allowed")
                validate_live_setup_trigger(setup, spot, max(0.5, float(structure.get("atr_1m") or 0.0) * 0.15))
                extension = abs(spot - setup.trigger)
                if structure.get("atr_1m") and extension > float(structure["atr_1m"]) * config.max_entry_extension_atr:
                    base_result["entry_timing_status"] = "WAIT_FOR_PULLBACK_RETEST"
                    raise ScannerError("ENTRY_TOO_EXTENDED", f"Current spot is {extension:.2f} points from setup trigger; thesis retained for a fresh pullback/retest")
                if not chain_refresh_ok:
                    detail = chain_refresh_error.code if chain_refresh_error else "UNKNOWN_REFRESH_FAILURE"
                    raise ScannerError("OPTION_CHAIN_REFRESH_FAILED", f"A fresh option chain/Greeks snapshot is required before entry; latest refresh failed with {detail}")
                if not oi_confirmation.get("approved"):
                    raise ScannerError(str(oi_confirmation.get("reason") or "OI_CONFIRMATION_MISSING"), "Current price setup lacks fresh compatible OI confirmation")
                if setup.kind == "V111_CONTINUATION":
                    d3 = str(structure.get("execution_3m_direction") or "")
                    if d3 in {"BULLISH", "BEARISH"} and d3 != setup.direction and float(structure.get("execution_3m_confidence") or 0) >= 0.70:
                        raise ScannerError("THREE_MINUTE_STRONGLY_OPPOSES", "Strong opposing three-minute structure blocks continuation")
                plan = v111_risk_plan(spot, setup, structure, levels, config, quote_received_at, market_thesis)
                base_result["risk_plan"] = plan
                selection_structure = dict(structure)
                selected = select_option_and_risk(setup.direction, spot, spot_quote_time, chain_records, full_quotes, expiry, quote_received_at, plan, selection_structure, config)
                signal_key_raw = f"{session_date}|{expiry}|{setup.direction}|{selected['instrument_key']}|{setup.kind}|{setup.confirmed_at.isoformat()}"
                signal_key = hashlib.sha256(signal_key_raw.encode()).hexdigest()[:24]
                if signal_key in state.get("seen_signal_keys", []):
                    base_result["reason_code"] = "DUPLICATE_SIGNAL_SUPPRESSED"
                    base_result["decision"] = "NO_TRADE"
                else:
                    active_position = create_active_position(
                        signal_key, quote_received_at, json_safe(setup), selected, plan,
                        index_candles[-1], config,
                    )
                    state["active_position"] = active_position
                    state["position_entry_block_after"] = None
                    base_result.update({
                        "decision": "QUALIFIED",
                        "reason_code": "QUALIFIED_CE" if setup.direction == "BULLISH" else "QUALIFIED_PE",
                        "signal_key": signal_key,
                        "selected_contract": selected,
                        "risk_plan": plan,
                        "setup": json_safe(setup),
                        "candidate_offsets_allowed": list(_strike_offsets_for_regime(setup.direction, selection_structure, config)),
                        "notification_status": "QUEUED" if config.email_configured else "NOT_CONFIGURED",
                        "active_position_summary": {
                            "position_id": signal_key, "direction": setup.direction,
                            "side": selected["side"], "strike": selected["strike"],
                            "entry_spot": plan["entry_underlying"], "stop_underlying": plan["stop_underlying"],
                            "t1_underlying": plan["t1_underlying"], "t2_underlying": plan.get("t2_underlying"),
                            "t1_partial_exit_pct": config.t1_partial_exit_pct,
                            "market_thesis_state": market_thesis.get("state"),
                            "market_thesis_direction": market_thesis.get("direction"),
                        },
                    })
                    state.setdefault("seen_signal_keys", []).append(signal_key)
                    state["seen_signal_keys"] = state["seen_signal_keys"][-1000:]
                    state["last_signal"] = {
                        "signal_key": signal_key, "timestamp": now.isoformat(),
                        "decision": base_result["decision"], "contract": selected, "risk_plan": plan,
                    }
                    queue_notification(state, signal_key, base_result, quote_received_at)
        elif state.get("position_reconciliation_required"):
            base_result["position_reconciliation_required"] = True

        base_result["evaluation_timestamp"] = quote_received_at.isoformat()
        state["last_decision"] = {k: base_result.get(k) for k in ("timestamp", "evaluation_timestamp", "decision", "reason_code", "signal_key", "spot", "oi_label", "regime")}
        state["schema_version"] = SCHEMA_VERSION
        state["scanner_version"] = VERSION
        state["session_date"] = session_date.isoformat()
        state["expiry"] = expiry.isoformat()
        if chain_refresh_ok:
            state["latest_oi_evidence"] = persisted_oi_evidence(oi)
            if chain_time is not None:
                state["last_successful_snapshot_at"] = chain_time.isoformat()
        state["last_processed_candle"] = index_candles[-1].start.isoformat()
        # Scanning only enqueues alerts. GitHub persists a durable claim before
        # a separate delivery phase is allowed to contact Gmail.
        normalize_notification_queue(state)
        atomic_write_json(config.state_file, state)
        if base_result.get("signal_key"):
            pending = next((x for x in state["pending_notifications"] if x.get("signal_key") == base_result["signal_key"]), None)
            if base_result["signal_key"] in state.get("delivered_signal_keys", []):
                base_result["notification_status"] = "SENT"
            elif pending:
                base_result["notification_status"] = pending.get("status", "QUEUED")
            elif base_result.get("notification_status") != "NOT_CONFIGURED":
                base_result["notification_status"] = "HELD_OR_ALREADY_PROCESSED"
        base_result["audit_persistence"] = persist_audit_records(
            config, session_date, base_result, oi_diagnostics=oi
        )
        return json_safe(base_result)
    except ScannerError as exc:
        operational_failure = is_operational_failure(exc.code)
        base_result.update({
            "decision": "NO_TRADE",
            "result_type": "ERROR" if operational_failure else "BLOCKED",
            "reason_code": exc.code,
            "message": str(exc),
            "expiry": expiry.isoformat() if expiry else None,
            "underlying_key": index_row.get("instrument_key") if index_row else None,
            "oi_label": oi.get("label", "MISSING"),
            "regime": base_result.get("regime", "UNKNOWN"),
            "spot": base_result.get("spot", spot_chain or None),
        })
        if operational_failure:
            base_result["error_type"] = "ScannerError"
        else:
            base_result.pop("error_type", None)
        # Preserve the last good baseline/snapshots on API errors; do not replace them with empty data.
        try:
            state["schema_version"] = SCHEMA_VERSION
            state["scanner_version"] = VERSION
            state["session_date"] = session_date.isoformat()
            state["last_decision"] = {k: base_result.get(k) for k in ("timestamp", "decision", "reason_code", "signal_key", "spot", "oi_label", "regime")}
            atomic_write_json(config.state_file, state)
        except Exception as persistence_error:
            LOG.error("Could not persist blocked scan state (%s); alerts suppressed", persistence_error)
            base_result["reason_code"] = "STATE_SAVE_FAILED"
            base_result["result_type"] = "ERROR"
            base_result["error_type"] = "ScannerError"
            base_result["message"] = f"{exc}; state persistence failed"
        base_result["audit_persistence"] = persist_audit_records(
            config, session_date, base_result, oi_diagnostics=oi
        )
        return json_safe(base_result)
    except Exception as exc:
        LOG.exception("Unexpected scanner failure")
        base_result.update({"decision": "NO_TRADE", "result_type": "ERROR", "error_type": type(exc).__name__, "reason_code": "UNEXPECTED_ERROR", "message": str(exc)[:500]})
        try:
            state["schema_version"] = SCHEMA_VERSION
            state["scanner_version"] = VERSION
            state["session_date"] = session_date.isoformat()
            state["last_decision"] = {k: base_result.get(k) for k in ("timestamp", "decision", "reason_code", "signal_key", "spot", "oi_label", "regime")}
            atomic_write_json(config.state_file, state)
        except Exception:
            base_result["reason_code"] = "STATE_SAVE_FAILED"
        base_result["audit_persistence"] = persist_audit_records(
            config, session_date, base_result, oi_diagnostics=oi
        )
        return json_safe(base_result)


# ---------- Notification queue and Gmail delivery ----------

def _ensure_state_list(state: dict[str, Any], key: str) -> list[Any]:
    value = state.get(key)
    if value is None:
        value = []
        state[key] = value
    if not isinstance(value, list):
        raise ScannerError("STATE_COLLECTION_INVALID", f"State field {key!r} must be a JSON list")
    return value


def _notification_key(item: Mapping[str, Any]) -> str:
    key = item.get("signal_key")
    if not key and isinstance(item.get("payload"), Mapping):
        key = item["payload"].get("signal_key")
    return str(key or "").strip()


def normalize_notification_queue(state: dict[str, Any]) -> list[dict[str, Any]]:
    """Remove duplicate, delivered, and malformed queue entries conservatively."""
    delivered = {str(x) for x in _ensure_state_list(state, "delivered_signal_keys") if x}
    raw_pending = _ensure_state_list(state, "pending_notifications")
    unique: dict[str, dict[str, Any]] = {}
    priority = {"QUEUED": 0, "CLAIMED": 1, "LEGACY_UNCERTAIN": 2, "DELIVERY_UNKNOWN": 3, "EXPIRED": 4}

    for raw in raw_pending:
        if not isinstance(raw, Mapping):
            continue
        item = dict(raw)
        key = _notification_key(item)
        if not key or key in delivered:
            continue
        item["signal_key"] = key
        status = str(item.get("status") or "").upper()
        if not status:
            status = "QUEUED" if int(item.get("attempts", 0) or 0) == 0 else "LEGACY_UNCERTAIN"
        if status in {"PENDING", "NOT_CONFIGURED", "FAILED", "DRY_RUN_NOT_SENT"}:
            status = "QUEUED" if int(item.get("attempts", 0) or 0) == 0 else "LEGACY_UNCERTAIN"
        item["status"] = status
        previous = unique.get(key)
        if previous is None or priority.get(status, 4) > priority.get(str(previous.get("status")), 4):
            unique[key] = item

    state["pending_notifications"] = list(unique.values())
    return state["pending_notifications"]


def _record_notification_history(state: dict[str, Any], item: Mapping[str, Any], status: str) -> None:
    history = _ensure_state_list(state, "notification_history")
    history.append({
        "signal_key": _notification_key(item),
        "status": status,
        "timestamp": now_ist().isoformat(),
        "attempts": int(item.get("attempts", 0) or 0),
        "error": str(item.get("last_error") or "")[:240] or None,
    })
    state["notification_history"] = history[-500:]


def _format_value(value: Any, decimals: int = 2) -> str:
    try:
        number = float(value)
        if not math.isfinite(number):
            return "—"
        return f"{number:,.{decimals}f}"
    except (TypeError, ValueError):
        return "—" if value is None else str(value)


def build_trade_email(payload: Mapping[str, Any]) -> EmailMessage:
    """Build a concise multipart trade alert with its full audit JSON attached."""
    data = compact_audit_record(payload)
    selected = data.get("selected_contract") or {}
    risk = data.get("risk_plan") or {}
    setup = data.get("setup") or {}
    oi = data.get("oi") or {}
    structure = data.get("structure") or {}
    thesis = data.get("market_thesis") if isinstance(data.get("market_thesis"), Mapping) else {}
    oi_structure = data.get("oi_structure") if isinstance(data.get("oi_structure"), Mapping) else {}
    timestamp = parse_datetime(data.get("timestamp")) or now_ist()
    side = str(selected.get("side") or "OPTION")
    strike = _format_value(selected.get("strike"), 0)
    expiry = str(selected.get("expiry") or data.get("expiry") or "—")
    reason = str(data.get("reason_code") or data.get("decision") or "QUALIFIED")
    direction = str(data.get("setup_direction") or setup.get("direction") or ("BULLISH" if side == "CE" else "BEARISH"))
    spot = data.get("spot", risk.get("entry_underlying"))
    signal_key = _notification_key({"signal_key": data.get("signal_key")})
    signal_short = signal_key[:12] if signal_key else "UNKEYED"

    trade_rows = [
        ("Signal", reason), ("Direction", direction), ("Option", f"{side} {strike}"),
        ("Expiry", expiry), ("NIFTY spot", _format_value(spot)),
        ("Entry premium (ask ref.)", _format_value(selected.get("reference_entry_ask"))),
        ("Bid / Ask", f"{_format_value(selected.get('reference_bid'))} / {_format_value(selected.get('reference_entry_ask'))}"),
        ("Delta", _format_value(selected.get("delta"), 4)),
        ("IV", _format_value(selected.get("iv_percent"))),
        ("Spread", f"{_format_value(selected.get('spread_pct'), 3)}%"),
        ("Selection score", _format_value(selected.get("selection_score"), 4)),
    ]
    risk_rows = [
        ("Underlying entry ref.", _format_value(risk.get("entry_underlying", spot))),
        ("Underlying stop", _format_value(risk.get("stop_underlying"))),
        ("Stop source", str(risk.get("stop_reference_source") or risk.get("stop_source") or "—")),
        ("Target 1", _format_value(risk.get("t1_underlying"))),
        ("Target 1 evidence", str(risk.get("t1_confluence") or risk.get("t1_source") or "—")),
        ("Target 2", _format_value(risk.get("t2_underlying"))),
        ("Target 2 evidence", str(risk.get("t2_confluence") or risk.get("t2_source") or "—")),
        ("Spot-based RR to T1", f"{_format_value(risk.get('underlying_rr'))}:1"),
    ]
    event_type = str(data.get("event_type") or "")
    event_details = data.get("position_event_details") if isinstance(data.get("position_event_details"), Mapping) else {}
    event_rows: list[tuple[str, str]] = []
    if event_type:
        event_rows = [
            ("Position event", event_type),
            ("Position status", str(data.get("position_status") or "—")),
            ("Remaining quantity", f"{_format_value(data.get('remaining_pct'), 1)}%"),
            ("Option best bid", _format_value(data.get("premium_bid"))),
            ("Original signal ID", str(data.get("original_signal_key") or "—")),
        ]
        for key, label in (("partial_exit_pct", "Quantity exited at T1"),
                            ("continuation_status", "Continuation assessment"),
                            ("reversal_status", "Reversal assessment"),
                            ("management_state", "Management state"),
                            ("market_thesis_state", "Market thesis state"),
                            ("post_t1_peak_drawdown_pct", "Post-T1 premium drawdown"),
                            ("drawdown_limit_pct", "Post-T1 drawdown limit"),
                            ("no_progress_3m_bars", "Post-T1 no-progress 3m bars"),
                            ("theta_fraction_since_progress", "Theta fraction since progress"),
                            ("peak_drawdown_pct", "Premium drawdown from peak"),
                            ("premium_loss_pct", "Premium loss from entry"),
                            ("new_t2", "Revised T2"), ("new_stop", "Revised stop")):
            if key in event_details:
                value = event_details[key]
                if key.endswith("_pct"):
                    value = f"{_format_value(value, 2)}%"
                elif isinstance(value, (int, float)):
                    value = _format_value(value)
                event_rows.append((label, str(value)))
    oi_direction = str(oi.get("raw_label") or oi.get("label") or data.get("oi_raw_label") or "—")
    oi_stable = str(oi.get("label") or data.get("oi_label") or "—")
    oi_confidence = _format_value(oi.get("confidence"), 3)
    setup_kind = str(setup.get("kind") or data.get("setup_kind") or "—")
    setup_confirmed = str(setup.get("confirmed_at") or "—")

    def plain_table(rows: Sequence[tuple[str, str]]) -> str:
        return "\n".join(f"{label}: {value}" for label, value in rows)

    text_body = "\n".join([
        f"NIFTY 50 — {reason}", f"{side} {strike} | Expiry {expiry}",
        f"Generated: {timestamp.strftime('%d %b %Y, %I:%M:%S %p IST')}",
        f"Signal ID: {signal_key or '—'}", "", "TRADE DETAILS", plain_table(trade_rows),
        *(["", "POSITION MANAGEMENT", plain_table(event_rows)] if event_rows else []),
        "", "OI / STRUCTURE RISK PLAN", plain_table(risk_rows), "", "MARKET CONFIRMATION",
        f"Setup: {setup_kind}", f"Setup confirmed: {setup_confirmed}",
        f"OI raw / stable: {oi_direction} / {oi_stable}", f"OI confidence: {oi_confidence}",
        f"Market thesis: {thesis.get('direction', structure.get('market_thesis_direction', '—'))} / {thesis.get('state', structure.get('market_thesis_state', '—'))}",
        f"Thesis support / resistance: {_format_value(thesis.get('anchor_support', structure.get('market_thesis_support')))} / {_format_value(thesis.get('anchor_resistance', structure.get('market_thesis_resistance')))}",
        f"OI support score: {_format_value(oi_structure.get('supportive_bullish_score') if direction.upper() == 'BULLISH' else oi_structure.get('supportive_bearish_score'), 3)}",
        f"OI break pressure: {_format_value(oi_structure.get('bearish_break_pressure') if direction.upper() == 'BULLISH' else oi_structure.get('bullish_break_pressure'), 3)}",
        f"Price execution 1m / 3m: {structure.get('execution_direction', '—')} / {structure.get('execution_3m_direction', '—')}",
        f"Market regime: {data.get('regime', structure.get('regime', '—'))}",
        "", "The JSON attachment contains the compact technical audit record.",
        "This is an analytical alert, not an order placed by the scanner.",
    ])

    def html_table(rows: Sequence[tuple[str, str]]) -> str:
        cells = "".join(
            f'<tr><th style="text-align:left;padding:7px 10px;color:#586174;font-weight:500">{html.escape(label)}</th>'
            f'<td style="text-align:right;padding:7px 10px;font-weight:600">{html.escape(value)}</td></tr>'
            for label, value in rows
        )
        return f'<table role="presentation" style="width:100%;border-collapse:collapse">{cells}</table>'

    accent = "#b42318" if direction.upper() == "BEARISH" else "#067647"
    html_body = f'''<!doctype html>
<html><body style="margin:0;padding:24px;background:#f4f6f8;font-family:Arial,Helvetica,sans-serif;color:#172033">
<div style="max-width:680px;margin:0 auto;background:#ffffff;border:1px solid #e2e6ea;border-radius:12px;overflow:hidden">
  <div style="padding:22px 24px;border-bottom:1px solid #e8ebef">
    <div style="font-size:12px;letter-spacing:1px;color:#667085">NIFTY 50 MARKET SCANNER · v{VERSION}</div>
    <div style="margin-top:8px;font-size:25px;font-weight:700;color:{accent}">{html.escape(event_type or reason)}</div>
    <div style="margin-top:5px;font-size:19px;font-weight:600">{html.escape(side)} {html.escape(strike)} <span style="font-size:14px;color:#667085">· Expiry {html.escape(expiry)}</span></div>
    <div style="margin-top:8px;font-size:12px;color:#667085">{html.escape(timestamp.strftime('%d %b %Y, %I:%M:%S %p IST'))} · Signal {html.escape(signal_short)}</div>
  </div>
  <div style="padding:18px 24px"><h3 style="margin:0 0 8px;font-size:15px">Trade details</h3>{html_table(trade_rows)}</div>
  {('<div style="padding:0 24px 18px"><h3 style="margin:0 0 8px;font-size:15px">Position management</h3>' + html_table(event_rows) + '</div>') if event_rows else ''}
  <div style="padding:0 24px 18px"><h3 style="margin:0 0 8px;font-size:15px">OI / structure risk plan</h3>{html_table(risk_rows)}</div>
  <div style="padding:0 24px 22px"><h3 style="margin:0 0 8px;font-size:15px">Market confirmation</h3>{html_table([
      ('Setup', setup_kind), ('Setup confirmed', setup_confirmed),
      ('OI raw / stable', f'{oi_direction} / {oi_stable}'), ('OI confidence', oi_confidence),
      ('Market thesis', f"{thesis.get('direction', structure.get('market_thesis_direction', '—'))} / {thesis.get('state', structure.get('market_thesis_state', '—'))}"),
      ('Thesis support / resistance', f"{_format_value(thesis.get('anchor_support', structure.get('market_thesis_support')))} / {_format_value(thesis.get('anchor_resistance', structure.get('market_thesis_resistance')))}"),
      ('OI support score', _format_value(oi_structure.get('supportive_bullish_score') if direction.upper() == 'BULLISH' else oi_structure.get('supportive_bearish_score'), 3)),
      ('OI break pressure', _format_value(oi_structure.get('bearish_break_pressure') if direction.upper() == 'BULLISH' else oi_structure.get('bullish_break_pressure'), 3)),
      ('Price execution 1m / 3m', f"{structure.get('execution_direction') or '—'} / {structure.get('execution_3m_direction') or '—'}"),
      ('Market regime', str(data.get('regime') or structure.get('regime') or '—')),
  ])}</div>
  <div style="padding:14px 24px;background:#f8fafc;border-top:1px solid #e8ebef;font-size:12px;color:#667085">
    Full compact technical evidence is attached as JSON. This is an analytical alert; the scanner does not place orders.
  </div>
</div></body></html>'''

    message = EmailMessage()
    subject_label = f"POSITION EVENT · {event_type}" if event_type else reason
    message["Subject"] = f"NIFTY v{VERSION} | {subject_label} | {side} {strike} | {timestamp.strftime('%d-%b %I:%M %p IST')}"
    message["X-Scanner-Version"] = VERSION
    if signal_key:
        message["Message-ID"] = f"<nifty-v109-{signal_key}@market-scanner.local>"
    message.set_content(text_body)
    message.add_alternative(html_body, subtype="html")
    attachment = dict(data)
    attachment["notification_status"] = "SENT"
    message.add_attachment(
        json.dumps(json_safe(attachment), indent=2, allow_nan=False).encode("utf-8"),
        maintype="application", subtype="json",
        filename=f"nifty_v109_signal_{signal_short}.json",
    )
    return message


def send_gmail(config: Config, payload: Mapping[str, Any]) -> None:
    """Send one message over Gmail SMTP; never retries an uncertain send."""
    if not config.email_configured:
        raise ScannerError("SMTP_CONFIG_MISSING", "Gmail sender, receiver, App Password, and SMTP host are required")
    message = build_trade_email(payload)
    message["From"] = config.email_sender
    message["To"] = config.email_receiver
    username = config.email_username or config.email_sender
    if config.smtp_port == 465:
        with smtplib.SMTP_SSL(config.smtp_host, config.smtp_port, timeout=20, context=ssl.create_default_context()) as smtp:
            smtp.login(username, config.email_password)
            refused = smtp.send_message(message)
    elif config.smtp_port == 587:
        with smtplib.SMTP(config.smtp_host, config.smtp_port, timeout=20) as smtp:
            smtp.starttls(context=ssl.create_default_context())
            smtp.login(username, config.email_password)
            refused = smtp.send_message(message)
    else:
        raise ScannerError("SMTP_PORT_INVALID", "Gmail SMTP port must be 465 (SSL) or 587 (STARTTLS)")
    if refused:
        raise ScannerError("SMTP_RECIPIENT_REFUSED", f"SMTP refused recipient(s): {', '.join(refused)}")


def claim_pending_notifications(config: Config, claim_token: str) -> dict[str, int]:
    """Durably claim queued alerts before the workflow attempts SMTP delivery."""
    if not config.email_configured:
        raise ScannerError("SMTP_CONFIG_MISSING", "Gmail settings are incomplete; refusing to claim notifications")
    if not claim_token.strip():
        raise ScannerError("NOTIFICATION_CLAIM_TOKEN_MISSING", "Set NOTIFICATION_CLAIM_TOKEN from the GitHub run ID and attempt")
    state = read_state(config.state_file)
    normalize_notification_queue(state)
    claimed = 0
    uncertain = 0
    expired = 0
    claim_time = now_ist()
    for item in state["pending_notifications"]:
        status = str(item.get("status", "QUEUED"))
        if status == "QUEUED":
            created_at = parse_datetime(item.get("created_at"))
            age_seconds = (claim_time - created_at).total_seconds() if created_at else float("inf")
            if age_seconds < -30 or age_seconds > config.setup_max_age_minutes * 60:
                item.update({
                    "status": "EXPIRED",
                    "last_error": "Alert exceeded the live setup freshness window before delivery; stale trade alerts are not sent.",
                    "expired_at": claim_time.isoformat(),
                })
                _record_notification_history(state, item, "EXPIRED")
                expired += 1
                continue
            item.update({"status": "CLAIMED", "claim_token": claim_token,
                         "claimed_at": claim_time.isoformat()})
            claimed += 1
        elif status == "CLAIMED" and item.get("claim_token") != claim_token:
            item.update({"status": "DELIVERY_UNKNOWN", "last_error":
                         "A previous workflow attempt claimed this signal but did not persist a final delivery result; automatic resend is disabled."})
            _record_notification_history(state, item, "DELIVERY_UNKNOWN")
            uncertain += 1
    state["schema_version"] = SCHEMA_VERSION
    state["scanner_version"] = VERSION
    atomic_write_json(config.state_file, state)
    return {"claimed": claimed, "uncertain_previous_claims": uncertain,
            "expired": expired,
            "queued_or_held": len(state["pending_notifications"]) - claimed - uncertain - expired}


def requeue_uncertain_notification(config: Config, signal_key: str) -> None:
    """Manually requeue one uncertain alert after an operator checks the inbox."""
    key = signal_key.strip()
    if not key:
        raise ScannerError("SIGNAL_KEY_REQUIRED", "Supply the exact signal key to requeue")
    state = read_state(config.state_file)
    normalize_notification_queue(state)
    if key in {str(x) for x in state.get("delivered_signal_keys", [])}:
        raise ScannerError("SIGNAL_ALREADY_DELIVERED", "This signal is recorded as delivered and will not be requeued")
    item = next((x for x in state["pending_notifications"] if x.get("signal_key") == key), None)
    if item is None or item.get("status") not in {"DELIVERY_UNKNOWN", "LEGACY_UNCERTAIN"}:
        raise ScannerError("SIGNAL_NOT_REQUEUEABLE", "Only DELIVERY_UNKNOWN or LEGACY_UNCERTAIN signals can be manually requeued")
    item.update({
        "status": "QUEUED",
        "attempts": 0,
        "claim_token": None,
        "last_error": None,
        "operator_requeued_at": now_ist().isoformat(),
    })
    state["pending_notifications"] = [x for x in state["pending_notifications"] if x.get("signal_key") != key]
    state["pending_notifications"].append(item)
    atomic_write_json(config.state_file, state)


def deliver_claimed_notifications(config: Config, claim_token: str) -> dict[str, int]:
    """Send only alerts claimed by this exact GitHub run attempt; no automatic retry."""
    if not config.email_configured:
        raise ScannerError("SMTP_CONFIG_MISSING", "Gmail settings are incomplete; refusing notification delivery")
    if not claim_token.strip():
        raise ScannerError("NOTIFICATION_CLAIM_TOKEN_MISSING", "Notification claim token is missing")
    state = read_state(config.state_file)
    normalize_notification_queue(state)
    sent = 0
    unknown = 0
    skipped = 0

    for item in list(state["pending_notifications"]):
        if item.get("status") != "CLAIMED" or item.get("claim_token") != claim_token:
            skipped += 1
            continue

        # Persist the one-shot attempt before contacting SMTP. A failure is not
        # automatically retried because SMTP acceptance can be ambiguous.
        item["status"] = "DELIVERY_UNKNOWN"
        item["attempts"] = int(item.get("attempts", 0) or 0) + 1
        item["last_attempt_at"] = now_ist().isoformat()
        item["last_error"] = "Delivery attempt started; automatic resend is disabled unless delivery is manually verified."
        atomic_write_json(config.state_file, state)

        try:
            payload = item.get("payload") if isinstance(item.get("payload"), Mapping) else {}
            send_gmail(config, payload)
        except Exception as exc:
            item["last_error"] = f"{type(exc).__name__}: {str(exc)[:220]}"
            _record_notification_history(state, item, "DELIVERY_UNKNOWN")
            unknown += 1
            LOG.error("Notification delivery uncertain for signal %s: %s", item.get("signal_key"), item["last_error"])
        else:
            item["status"] = "SENT"
            item["sent_at"] = now_ist().isoformat()
            item.pop("last_error", None)
            state.setdefault("delivered_signal_keys", []).append(item["signal_key"])
            state["delivered_signal_keys"] = list(dict.fromkeys(state["delivered_signal_keys"]))[-1000:]
            _record_notification_history(state, item, "SENT")
            sent += 1

        atomic_write_json(config.state_file, state)

    state["pending_notifications"] = [
        item for item in state["pending_notifications"]
        if item.get("status") != "SENT"
    ]
    atomic_write_json(config.state_file, state)
    return {"sent": sent, "delivery_unknown": unknown, "skipped": skipped}

# ---------- CLI ----------

def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="NIFTY 50 v109 persistent structural-thesis + option-aware runner scanner (no order execution)"
    )
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--config-check", action="store_true", help="Validate Upstox and Gmail configuration")
    modes.add_argument("--prepare-only", action="store_true", help="Run scan and queue alerts without sending")
    modes.add_argument("--scan-and-claim", action="store_true", help="Run one scan and claim its queued alerts for this GitHub run attempt")
    modes.add_argument("--claim-notifications", action="store_true", help="Claim queued alerts for this GitHub run attempt")
    modes.add_argument("--deliver-claimed", action="store_true", help="Send only alerts claimed by this GitHub run attempt")
    modes.add_argument("--requeue-notification", metavar="SIGNAL_KEY", help="Manually requeue one uncertain alert after checking Gmail")
    modes.add_argument("--reconcile-position", metavar="FLAT_OR_SIGNAL_KEY", help="Legacy migration/recovery utility: explicitly confirm flat or recover one legacy signal position")
    parser.add_argument("--version", action="version", version=VERSION)
    args = parser.parse_args(argv)
    logging.basicConfig(
        level=os.getenv("LOG_LEVEL", "INFO").upper(),
        format="%(asctime)s %(levelname)s %(message)s",
    )

    try:
        config = Config.from_env()
        if args.config_check:
            if not config.email_configured:
                raise ScannerError(
                    "SMTP_CONFIG_MISSING",
                    "Set EMAIL_SENDER, EMAIL_RECEIVER, EMAIL_PASSWORD and SMTP_HOST (smtp.gmail.com by default).",
                )
            print(json.dumps({
                "version": VERSION,
                "config": "valid",
                "state_file": str(config.state_file),
                "audit_dir": str(config.audit_dir),
                "notification_configured": config.email_configured,
                "smtp_host": config.smtp_host,
                "smtp_port": config.smtp_port,
            }, sort_keys=True))
            return 0

        if args.scan_and_claim:
            # Keep the market scan and notification claim in one process. The
            # workflow still commits this durable claim before a separate
            # delivery invocation is allowed to contact Gmail.
            scan_result = run_scan(config)
            if is_operational_failure(scan_result.get("reason_code")):
                print(json.dumps(compact_audit_record(scan_result), separators=(",", ":"), sort_keys=True))
                return 1
            claim_token = os.getenv("NOTIFICATION_CLAIM_TOKEN", "").strip()
            claim_result = claim_pending_notifications(config, claim_token)
            print(json.dumps({
                "scan": compact_audit_record(scan_result),
                "notifications": claim_result,
            }, separators=(",", ":"), sort_keys=True))
            return 0

        if args.claim_notifications:
            claim_token = os.getenv("NOTIFICATION_CLAIM_TOKEN", "").strip()
            result = claim_pending_notifications(config, claim_token)
            print(json.dumps(result, sort_keys=True))
            return 0

        if args.requeue_notification:
            requeue_uncertain_notification(config, args.requeue_notification)
            print(json.dumps({"requeued_signal_key": args.requeue_notification, "status": "QUEUED"}, sort_keys=True))
            return 0

        if args.reconcile_position:
            result = reconcile_legacy_position(config, args.reconcile_position)
            print(json.dumps(result, sort_keys=True))
            return 0

        if args.deliver_claimed:
            claim_token = os.getenv("NOTIFICATION_CLAIM_TOKEN", "").strip()
            result = deliver_claimed_notifications(config, claim_token)
            print(json.dumps(result, sort_keys=True))
            return 1 if result["delivery_unknown"] else 0

        result = run_scan(config)
        print(json.dumps(compact_audit_record(result), separators=(",", ":"), sort_keys=True))
        return 1 if is_operational_failure(result.get("reason_code")) else 0
    except ScannerError as exc:
        result = {
            "scanner_version": VERSION,
            "timestamp": now_ist().isoformat(),
            "decision": "NO_TRADE",
            "result_type": "ERROR",
            "reason_code": exc.code,
            "error_type": "ScannerError",
            "message": str(exc),
        }
        print(json.dumps(result, separators=(",", ":"), sort_keys=True))
        return 1
    except Exception as exc:
        LOG.exception("Fatal configuration/CLI failure")
        print(json.dumps({
            "scanner_version": VERSION,
            "timestamp": now_ist().isoformat(),
            "decision": "NO_TRADE",
            "result_type": "ERROR",
            "reason_code": "UNEXPECTED_ERROR",
            "error_type": type(exc).__name__,
            "message": str(exc)[:500],
        }, separators=(",", ":"), sort_keys=True))
        return 1

if __name__ == "__main__":
    raise SystemExit(main())
