#!/usr/bin/env python3
"""NIFTY 50 OI-first intraday scanner with persistent position management v107.0.0.

Single-file runtime for a GitHub Actions workflow dispatched about every three
minutes. It never places orders. Tests and documentation are separate files.

Design contract:
- signed OI changes are computed only between consecutive successful,
  same-session, same-expiry, identity-matched option-chain snapshots;
- one-minute candles are price observations, never a source of fabricated OI;
- a historical setup must pass a current-price/fresh-quote revalidation;
- the nearest valid opposing barrier is always T1 and cannot be bypassed;
- a trade requires spot-only RR >= 2.0; option premium RR is not used;
- state is written atomically before notification is attempted;
- failures produce explicit reason codes and never silently reuse stale data.

Sources of truth for the API adapter are documented in RESEARCH_NOTES.md.
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

VERSION = "107.0.0"
SCHEMA_VERSION = 107
IST = ZoneInfo("Asia/Kolkata")
UTC = timezone.utc
API_BASE = "https://api.upstox.com"
INSTRUMENTS_URL = "https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz"
LOG = logging.getLogger("nifty_scanner")


# ---------- Configuration and errors ----------

class ScannerError(RuntimeError):
    def __init__(self, code: str, message: str, *, retryable: bool = False):
        super().__init__(message)
        self.code = code
        self.retryable = retryable


@dataclass(frozen=True)
class Config:
    token: str
    state_file: Path = Path("state/market_state_v107.json")
    audit_dir: Path = Path("audit")
    instrument_cache: Path = Path(".cache/upstox_nse.json.gz")
    explicit_expiry: Optional[date] = None
    request_timeout: float = 12.0
    max_retries: int = 2
    instrument_cache_hours: int = 12
    oi_material_threshold_pct: float = 2.0
    min_underlying_rr: float = 2.0
    max_oi_age_seconds: int = 720
    expected_oi_interval_seconds: int = 180
    max_quote_age_seconds: int = 120
    max_candle_age_seconds: int = 150
    max_spread_pct: float = 3.0
    min_bid_qty: float = 1.0
    min_ask_qty: float = 1.0
    min_option_volume: float = 1.0
    min_abs_delta: float = 0.30
    max_abs_delta: float = 0.80
    max_entry_extension_atr: float = 1.35
    pivot_left: int = 2
    pivot_right: int = 2
    support_lookback_candles: int = 8
    setup_max_age_minutes: int = 6
    setup_state_ttl_minutes: int = 20
    strike_offsets_ce: tuple[int, ...] = (0, -1, -2)
    strike_offsets_pe: tuple[int, ...] = (0, 1, 2)
    iv_shock_points: float = 1.0
    expected_hold_minutes: float = 15.0
    annual_risk_free_rate: float = 0.06
    option_slippage_points: float = 1.0
    transaction_cost_rate: float = 0.0018
    min_level_strength: float = 1.0
    level_cluster_atr_fraction: float = 0.12
    stop_buffer_atr_fraction: float = 0.10
    minimum_stop_points: float = 5.0
    max_stop_atr: float = 2.5
    min_oi_direction_confidence: float = 0.52
    min_oi_score_margin: float = 0.12
    min_mixed_price_confirmation: float = 0.65
    t1_partial_exit_pct: float = 50.0
    max_premium_loss_pct: float = 20.0
    premium_trailing_drawdown_pct: float = 25.0
    premium_decay_review_minutes: float = 15.0
    premium_decay_min_loss_pct: float = 12.0
    no_progress_min_spot_move_atr: float = 0.25
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
            "max_stop_atr": self.max_stop_atr,
            "premium_decay_review_minutes": self.premium_decay_review_minutes,
        }
        for name, value in positive.items():
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite number greater than zero")
        if self.min_underlying_rr < 2.0:
            raise ScannerError("CONFIG_INVALID", "MIN_UNDERLYING_RR cannot be set below the hard 2.0:1 spot-based minimum")
        if self.min_abs_delta < 0 or self.max_abs_delta > 1 or self.min_abs_delta >= self.max_abs_delta:
            raise ScannerError("CONFIG_INVALID", "Delta limits must satisfy 0 <= min_abs_delta < max_abs_delta <= 1")
        if self.max_retries < 0 or self.max_retries > 5:
            raise ScannerError("CONFIG_INVALID", "max_retries must be between 0 and 5")
        if not isinstance(self.debug_audit, bool):
            raise ScannerError("CONFIG_INVALID", "debug_audit must be a boolean")
        if self.setup_state_ttl_minutes < self.setup_max_age_minutes:
            raise ScannerError("CONFIG_INVALID", "setup_state_ttl_minutes must be at least setup_max_age_minutes")
        if self.smtp_port not in {465, 587}:
            raise ScannerError("CONFIG_INVALID", "SMTP_PORT must be 465 (SSL) or 587 (STARTTLS)")
        for name, value in {
            "min_oi_direction_confidence": self.min_oi_direction_confidence,
            "min_oi_score_margin": self.min_oi_score_margin,
            "min_mixed_price_confirmation": self.min_mixed_price_confirmation,
        }.items():
            if not math.isfinite(float(value)) or not 0.0 <= float(value) <= 1.0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be between 0 and 1")
        bounded_percentages = {
            "t1_partial_exit_pct": self.t1_partial_exit_pct,
            "max_premium_loss_pct": self.max_premium_loss_pct,
            "premium_trailing_drawdown_pct": self.premium_trailing_drawdown_pct,
            "premium_decay_min_loss_pct": self.premium_decay_min_loss_pct,
        }
        for name, value in bounded_percentages.items():
            if not math.isfinite(float(value)) or not 0.0 <= float(value) <= 100.0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be between 0 and 100")
        if not 0.0 < self.t1_partial_exit_pct < 100.0:
            raise ScannerError("CONFIG_INVALID", "T1_PARTIAL_EXIT_PCT must be greater than 0 and less than 100")
        if not math.isfinite(float(self.no_progress_min_spot_move_atr)) or self.no_progress_min_spot_move_atr < 0:
            raise ScannerError("CONFIG_INVALID", "NO_PROGRESS_MIN_SPOT_MOVE_ATR must be finite and nonnegative")
        nonnegative = {
            "min_bid_qty": self.min_bid_qty, "min_ask_qty": self.min_ask_qty,
            "min_option_volume": self.min_option_volume, "option_slippage_points": self.option_slippage_points,
            "transaction_cost_rate": self.transaction_cost_rate, "iv_shock_points": self.iv_shock_points,
            "annual_risk_free_rate": self.annual_risk_free_rate, "stop_buffer_atr_fraction": self.stop_buffer_atr_fraction,
            "level_cluster_atr_fraction": self.level_cluster_atr_fraction,
        }
        for name, value in nonnegative.items():
            if not math.isfinite(float(value)) or float(value) < 0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite nonnegative number")

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
            state_file=Path(os.getenv("STATE_FILE", "state/market_state_v107.json")),
            audit_dir=Path(os.getenv("AUDIT_DIR", "audit")),
            instrument_cache=Path(os.getenv("INSTRUMENT_CACHE_FILE", ".cache/upstox_nse.json.gz")),
            explicit_expiry=expiry,
            request_timeout=float_env("REQUEST_TIMEOUT_SECONDS", 12.0),
            max_retries=int_env("API_MAX_RETRIES", 2),
            instrument_cache_hours=int_env("INSTRUMENT_CACHE_HOURS", 12),
            oi_material_threshold_pct=float_env("OI_MATERIAL_THRESHOLD_PCT", 2.0) or 2.0,
            min_underlying_rr=float_env("MIN_UNDERLYING_RR", 2.0) or 2.0,
            max_oi_age_seconds=int_env("MAX_OI_AGE_SECONDS", 720),
            expected_oi_interval_seconds=max(30, int_env("EXPECTED_OI_INTERVAL_SECONDS", 180)),
            max_quote_age_seconds=int_env("MAX_QUOTE_AGE_SECONDS", 120),
            max_candle_age_seconds=int_env("MAX_CANDLE_AGE_SECONDS", 150),
            max_spread_pct=float_env("MAX_SPREAD_PCT", 3.0),
            min_bid_qty=float_env("MIN_BID_QTY", 1.0),
            min_ask_qty=float_env("MIN_ASK_QTY", 1.0),
            min_option_volume=float_env("MIN_OPTION_VOLUME", 1.0),
            min_abs_delta=float_env("MIN_ABS_DELTA", 0.30),
            max_abs_delta=float_env("MAX_ABS_DELTA", 0.80),
            max_entry_extension_atr=float_env("MAX_ENTRY_EXTENSION_ATR", 1.35),
            setup_max_age_minutes=int_env("SETUP_MAX_AGE_MINUTES", 6),
            setup_state_ttl_minutes=int_env("SETUP_STATE_TTL_MINUTES", 20),
            iv_shock_points=float_env("IV_SHOCK_POINTS", 1.0),
            expected_hold_minutes=float_env("EXPECTED_HOLD_MINUTES", 15.0),
            annual_risk_free_rate=float_env("ANNUAL_RISK_FREE_RATE", 0.06),
            option_slippage_points=float_env("OPTION_SLIPPAGE_POINTS", 1.0),
            transaction_cost_rate=float_env("TRANSACTION_COST_RATE", 0.0018),
            min_oi_direction_confidence=float_env("MIN_OI_DIRECTION_CONFIDENCE", 0.52),
            min_oi_score_margin=float_env("MIN_OI_SCORE_MARGIN", 0.12),
            min_mixed_price_confirmation=float_env("MIN_MIXED_PRICE_CONFIRMATION", 0.65),
            t1_partial_exit_pct=float_env("T1_PARTIAL_EXIT_PCT", 50.0),
            max_premium_loss_pct=float_env("MAX_PREMIUM_LOSS_PCT", 20.0),
            premium_trailing_drawdown_pct=float_env("PREMIUM_TRAILING_DRAWDOWN_PCT", 25.0),
            premium_decay_review_minutes=float_env("PREMIUM_DECAY_REVIEW_MINUTES", 15.0),
            premium_decay_min_loss_pct=float_env("PREMIUM_DECAY_MIN_LOSS_PCT", 12.0),
            no_progress_min_spot_move_atr=float_env("NO_PROGRESS_MIN_SPOT_MOVE_ATR", 0.25),
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
    """Migrate compatible v102-v106 durable state without discarding the session baseline.

    Only data structures that already have stable meanings are carried forward.
    run_scan subsequently validates session date, expiry and instrument identity
    before using any snapshot for OI deltas.
    """
    try:
        old_schema = int(state.get("schema_version", 0) or 0)
    except (TypeError, ValueError):
        old_schema = 0
    if old_schema not in {102, 103, 104, 105, 106}:
        raise ScannerError("STATE_SCHEMA_UNSUPPORTED", f"Cannot safely migrate schema {old_schema} from {source}")
    migrated = dict(state)
    migrated["schema_version"] = SCHEMA_VERSION
    migrated["scanner_version"] = VERSION
    migrated["migration_note"] = (f"migrated_schema_{old_schema}_to_{SCHEMA_VERSION}; "
                                  "legacy pending notifications held as LEGACY_UNCERTAIN; active position requires explicit reconciliation")
    migrated.setdefault("position_history", [])
    if not isinstance(migrated.get("active_position"), Mapping):
        migrated["active_position"] = None
        migrated["position_reconciliation_required"] = True
        migrated["position_reconciliation_reason"] = "LEGACY_STATE_HAS_NO_ACTIVE_POSITION_RECORD"
    snapshots = migrated.get("chain_snapshots")
    migrated["chain_snapshots"] = [x for x in snapshots if isinstance(x, Mapping)][-16:] if isinstance(snapshots, list) else []
    legacy_pending = migrated.get("pending_notifications")
    if isinstance(legacy_pending, list):
        migrated["pending_notifications"] = [
            {**dict(item), "status": "LEGACY_UNCERTAIN", "claim_token": None,
             "migration_note": "Not automatically resent; delivery may already have occurred"}
            for item in legacy_pending if isinstance(item, Mapping)
        ]
    # Preserve only known durable workflow fields. Unknown schema-specific
    # structures are not silently interpreted by the new decision engine.
    allowed = {
        "schema_version", "scanner_version", "migration_note", "session_date", "expiry",
        "chain_snapshots", "session_oi_baseline", "last_successful_snapshot_at",
        "latest_oi_evidence", "oi_evidence_history", "last_processed_candle",
        "setup_watch", "seen_signal_keys", "pending_notifications",
        "delivered_signal_keys", "notification_history", "last_signal", "last_decision", "instrument_cache_version",
        "active_position", "position_history", "position_reconciliation_required", "position_reconciliation_reason",
        "last_position_exit", "last_position_event_key",
    }
    return {key: value for key, value in migrated.items() if key in allowed}


def read_state(path: Path) -> dict[str, Any]:
    """Load v107 state or migrate a compatible v102-v106 state file."""
    source = path if path.exists() else None
    if source is None:
        # GitHub Actions may still persist state under an earlier versioned filename.
        # Keep the old file untouched; migrate its compatible state into v105 on save.
        candidates = [path.parent / "market_state_v106.json", path.parent / "market_state_v105.json",
                      path.parent / "market_state_v104.json", path.parent / "market_state_v103.json",
                      path.parent / "market_state_v102.json"]
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
        schema = state.get("schema_version")
        if schema == SCHEMA_VERSION:
            return state
        if source != path or schema in {102, 103, 104, 105, 106}:
            migrated = _migrate_state_payload(state, source)
            LOG.warning("Migrated durable state schema %s to %s from %s", schema, SCHEMA_VERSION, source)
            return migrated
        old_schema = str(schema if schema is not None else "unknown")
        backup = path.with_name(path.name + f".schema-{old_schema}.backup")
        if backup.exists():
            backup = path.with_name(path.name + f".schema-{old_schema}.{datetime.now(UTC).strftime('%Y%m%dT%H%M%SZ')}.backup")
        try:
            shutil.copy2(path, backup)
        except OSError as exc:
            raise ScannerError("STATE_BACKUP_FAILED", f"Cannot preserve incompatible state before reset: {exc}") from exc
        LOG.warning("State schema %r is incompatible with v%s; old state copied to %s; starting clean state.", old_schema, VERSION, backup)
        return {"schema_version": SCHEMA_VERSION, "scanner_version": VERSION,
                "migration_note": "incompatible_state_not_reused", "migration_backup": str(backup)}
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
        "session_date", "expiry", "underlying_key", "decision", "reason_code",
        "error_type", "message", "spot", "oi_label", "oi_state", "oi_raw_label",
        "option_chain_status", "option_chain_error", "regime", "market_scenario", "setup_age_seconds",
        "setup_direction", "setup_kind", "signal_key", "notification_status",
        "notification_error", "candidate_offsets_allowed", "audit_persistence",
        "event_type", "position_id", "original_signal_key", "position_status",
        "remaining_pct", "t1_hit", "premium_bid", "exit_spot", "exit_reason",
        "position_event_details", "active_position_summary", "position_reconciliation_required",
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
        "execution_status", "reason", "atr_1m", "atr_5m", "efficiency_ratio",
        "momentum_3m_points", "completed_1m_contiguous_count",
        "completed_5m_contiguous_count", "duplicate_1m_candle_count",
        "duplicate_5m_candle_count", "ema8_1m", "ema8_5m", "ema21_5m",
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
    if record.get("error_type") or record.get("reason_code") in {
        "UNEXPECTED_ERROR", "STATE_SAVE_FAILED", "API_AUTH_FAILED", "API_PERMISSION_DENIED",
        "API_HTTP_ERROR", "API_HTTP_403", "API_HTTP_401",
    }:
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
    """OI-first directional evidence with four-way flow classification.

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


def price_regime(candles_1m: Sequence[Candle], candles_5m: Sequence[Candle]) -> dict[str, Any]:
    """Classify execution and higher-timeframe context independently.

    Eight contiguous one-minute closes are sufficient for an EMA(8) execution
    read. Three contiguous completed five-minute bars support only a provisional
    context; 21 bars are required before the EMA(21) slow-stack context is marked mature.
    ATR uses the available true ranges and never fabricates missing candles.
    """
    one = _contiguous_tail(candles_1m, 1)
    five = _contiguous_tail(candles_5m, 5)
    duplicate_1m = max(0, len(candles_1m) - len({c.start for c in candles_1m}))
    duplicate_5m = max(0, len(candles_5m) - len({c.start for c in candles_5m}))
    atr1 = atr(one, 14)
    atr5 = atr(five, 14)

    # One-minute execution structure is not gated by the number of five-minute
    # bars. This was the primary early-session coupling defect in v102.0.1.
    execution_direction = "UNKNOWN"
    execution_confidence = 0.0
    momentum = None
    ema8_1 = None
    execution_status = "INSUFFICIENT_CONTIGUOUS_1M_HISTORY"
    if len(one) >= 8:
        closes1 = [c.close for c in one]
        ema8_1 = ema(closes1[-16:], 8)
        ema8_1_previous = ema(closes1[-17:-1], 8) if len(closes1) >= 9 else None
        momentum = closes1[-1] - closes1[-4]
        recent_diffs = [b - a for a, b in zip(closes1[-5:], closes1[-4:])]
        up_count = sum(x > 0 for x in recent_diffs)
        down_count = sum(x < 0 for x in recent_diffs)
        vol_scale = max(0.25 * (atr1 or 0.0), 0.5)
        momentum_ok_up = momentum > vol_scale * 0.15
        momentum_ok_down = momentum < -vol_scale * 0.15
        ema_slope_up = ema8_1_previous is None or ema8_1 >= ema8_1_previous
        ema_slope_down = ema8_1_previous is None or ema8_1 <= ema8_1_previous
        if closes1[-1] > float(ema8_1) and momentum_ok_up and ema_slope_up and up_count >= 2:
            execution_direction = "BULLISH"
        elif closes1[-1] < float(ema8_1) and momentum_ok_down and ema_slope_down and down_count >= 2:
            execution_direction = "BEARISH"
        else:
            execution_direction = "MIXED"
        momentum_strength = min(1.0, abs(momentum) / max((atr1 or 1.0) * 0.75, 1.0))
        consistency = max(up_count, down_count) / max(1, len(recent_diffs))
        ema_distance = min(1.0, abs(closes1[-1] - float(ema8_1)) / max((atr1 or 1.0) * 0.5, 1.0))
        execution_confidence = round(0.45 * consistency + 0.35 * momentum_strength + 0.20 * ema_distance, 4)
        execution_status = "READY" if execution_direction in {"BULLISH", "BEARISH"} else "MIXED_PRICE_ACTION"

    # Five-minute context has its own readiness. During the first 15-35 minutes,
    # a transparent provisional read is preferable to hiding a usable 1m signal.
    htf = "UNKNOWN"
    htf_status = "INSUFFICIENT_COMPLETED_5M_BARS"
    htf_confidence = 0.0
    efficiency = None
    ema8_5 = None
    ema21_5 = None
    if len(five) >= 3:
        closes5 = [c.close for c in five]
        recent5 = closes5[-6:]
        net = recent5[-1] - recent5[0]
        path = sum(abs(b - a) for a, b in zip(recent5, recent5[1:]))
        efficiency = abs(net) / path if path > 0 else 0.0
        atr5 = atr5 or median([c.high - c.low for c in five[-min(5, len(five)):]]) or 0.0
        diffs5 = [b - a for a, b in zip(recent5, recent5[1:])]
        up5 = sum(x > 0 for x in diffs5)
        down5 = sum(x < 0 for x in diffs5)
        share = max(up5, down5) / max(1, len(diffs5))
        fast_period = 3 if len(five) < 8 else 8
        ema8_5 = ema(closes5[-max(fast_period, min(24, len(closes5))):], fast_period)
        # Do not call an 8- or 12-bar estimate a mature EMA(21). Wait for 21
        # completed five-minute observations before applying the slow-stack gate.
        ema21_5 = ema(closes5[-40:], 21) if len(five) >= 21 else None
        directional_threshold = max(0.30 * atr5, 1.0)
        if net > directional_threshold and up5 >= max(2, math.ceil(0.60 * len(diffs5))) and closes5[-1] > float(ema8_5):
            htf = "BULLISH"
            htf_confidence = min(0.90, 0.45 + 0.25 * min(1.0, abs(net) / max(atr5, 1.0)) + 0.20 * share)
        elif net < -directional_threshold and down5 >= max(2, math.ceil(0.60 * len(diffs5))) and closes5[-1] < float(ema8_5):
            htf = "BEARISH"
            htf_confidence = min(0.90, 0.45 + 0.25 * min(1.0, abs(net) / max(atr5, 1.0)) + 0.20 * share)
        elif efficiency < 0.22 and abs(net) <= max(0.50 * atr5, 1.0):
            htf = "SIDEWAYS"
            htf_confidence = max(0.40, 1.0 - efficiency)
        else:
            htf = "TRANSITION"
            htf_confidence = max(0.0, min(0.65, 0.35 + 0.25 * efficiency))
        htf_status = ("PROVISIONAL_EARLY_SESSION" if len(five) < 8
                      else "DEVELOPING_CONTEXT" if len(five) < 21
                      else "MATURE_CONTEXT")
        # At mature depth, require both the fast/slow EMA stack and momentum
        # before assigning a confirmed directional bias. Until EMA(21) has 21
        # completed observations, retain the early hypothesis as provisional.
        if len(five) >= 21:
            if closes5[-1] > float(ema8_5) > float(ema21_5) and net > max(0.45 * atr5, 1.0) and up5 >= 3:
                htf = "BULLISH"
                htf_confidence = min(1.0, 0.55 + 0.25 * min(1.0, abs(net) / max(atr5, 1.0)) + 0.20 * share)
            elif closes5[-1] < float(ema8_5) < float(ema21_5) and net < -max(0.45 * atr5, 1.0) and down5 >= 3:
                htf = "BEARISH"
                htf_confidence = min(1.0, 0.55 + 0.25 * min(1.0, abs(net) / max(atr5, 1.0)) + 0.20 * share)
            elif htf in {"BULLISH", "BEARISH"}:
                htf = "TRANSITION"
                htf_confidence = min(htf_confidence, 0.60)
            htf_status = "MATURE_CONTEXT"

    if execution_direction == "UNKNOWN":
        regime = "INSUFFICIENT_EXECUTION_HISTORY"
    elif htf == "UNKNOWN":
        regime = f"EARLY_SESSION_{execution_direction}_EXECUTION" if execution_direction in {"BULLISH", "BEARISH"} else "EARLY_SESSION_MIXED_EXECUTION"
    elif htf == "BULLISH" and execution_direction == "BULLISH":
        regime = "CONTINUOUS_BULLISH"
    elif htf == "BEARISH" and execution_direction == "BEARISH":
        regime = "CONTINUOUS_BEARISH"
    elif htf == "BEARISH" and execution_direction == "BULLISH":
        regime = "REVERSAL_BEAR_TO_BULL_WATCH"
    elif htf == "BULLISH" and execution_direction == "BEARISH":
        regime = "REVERSAL_BULL_TO_BEAR_WATCH"
    elif htf == "SIDEWAYS":
        regime = "SIDEWAYS"
    else:
        regime = "TRANSITION"
    # Make the maturity of the 5m context visible in the regime label itself.
    # A provisional first-hour read is never presented as a fully confirmed
    # continuous trend.
    if htf_status == "PROVISIONAL_EARLY_SESSION" and not regime.startswith(("EARLY_SESSION_", "INSUFFICIENT_")):
        regime = f"EARLY_SESSION_{regime}"
    elif htf_status == "DEVELOPING_CONTEXT" and not regime.startswith(("EARLY_SESSION_", "INSUFFICIENT_")):
        regime = f"DEVELOPING_{regime}"

    return {
        "regime": regime,
        "higher_timeframe_bias": htf,
        "higher_timeframe_status": htf_status,
        "higher_timeframe_confidence": round(htf_confidence, 4),
        "execution_direction": execution_direction,
        "execution_status": execution_status,
        "execution_confidence": execution_confidence,
        "efficiency_ratio": efficiency,
        "atr_1m": atr1,
        "atr_5m": atr5,
        "momentum_3m_points": momentum,
        "ema8_1m": ema8_1,
        "ema8_5m": ema8_5,
        "ema21_5m": ema21_5,
        "completed_1m_contiguous_count": len(one),
        "completed_5m_contiguous_count": len(five),
        "duplicate_1m_candle_count": duplicate_1m,
        "duplicate_5m_candle_count": duplicate_5m,
        "reason": "INDEPENDENT_1M_EXECUTION_AND_5M_CONTEXT",
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
    atr1: Optional[float], config: Config,
) -> list[PriceLevel]:
    if not candles:
        return []
    levels: list[PriceLevel] = []
    tick = 0.05  # NIFTY index price levels are analytical levels, not tradable contracts.
    tol = max(tick * 2, (atr1 or 0) * config.level_cluster_atr_fraction)
    latest = candles[-1]
    day = latest.start.astimezone(IST).date()
    session = [c for c in candles if c.start.astimezone(IST).date() == day]
    if session:
        # Today's extreme is a level only when it occurred before the current candle.
        prior_session = session[:-1]
        if prior_session:
            levels.append(PriceLevel(min(c.low for c in prior_session), "SUPPORT", "SESSION_LOW", 2.0))
            levels.append(PriceLevel(max(c.high for c in prior_session), "RESISTANCE", "SESSION_HIGH", 2.0))
        opening5 = [c for c in session if c.start.astimezone(IST).time() < dtime(9, 20)]
        opening15 = [c for c in session if c.start.astimezone(IST).time() < dtime(9, 30)]
        if len(opening5) >= 5:
            levels.extend([PriceLevel(min(c.low for c in opening5), "SUPPORT", "OPENING_RANGE_5M_LOW", 1.8), PriceLevel(max(c.high for c in opening5), "RESISTANCE", "OPENING_RANGE_5M_HIGH", 1.8)])
        if len(opening15) >= 15:
            levels.extend([PriceLevel(min(c.low for c in opening15), "SUPPORT", "OPENING_RANGE_15M_LOW", 1.6), PriceLevel(max(c.high for c in opening15), "RESISTANCE", "OPENING_RANGE_15M_HIGH", 1.6)])
    if previous_daily:
        prev = max((c for c in previous_daily if c.start.astimezone(IST).date() < day), key=lambda c: c.start, default=None)
        if prev:
            levels.extend([PriceLevel(prev.high, "RESISTANCE", "PREVIOUS_SESSION_HIGH", 2.2), PriceLevel(prev.low, "SUPPORT", "PREVIOUS_SESSION_LOW", 2.2), PriceLevel(prev.close, "SUPPORT" if prev.close <= latest.close else "RESISTANCE", "PREVIOUS_SESSION_CLOSE", 1.5)])
    lows, highs = confirmed_pivots(candles, config.pivot_left, config.pivot_right)
    for idx, value in lows[-8:]:
        levels.append(PriceLevel(value, "SUPPORT", f"CONFIRMED_SWING_LOW_{candles[idx].start.astimezone(IST).strftime('%H%M')}", 1.5))
    for idx, value in highs[-8:]:
        levels.append(PriceLevel(value, "RESISTANCE", f"CONFIRMED_SWING_HIGH_{candles[idx].start.astimezone(IST).strftime('%H%M')}", 1.5))
    if futures_vwap is not None and math.isfinite(futures_vwap):
        levels.append(PriceLevel(futures_vwap, "SUPPORT" if futures_vwap <= latest.close else "RESISTANCE", "FUTURES_VWAP_CONTEXT_ONLY", 0.8))
    # OI walls are directional levels only in their relevant market location:
    # put OI below spot is a potential support/target zone; call OI above spot
    # is a potential resistance/stop zone. A writer-flow score strengthens the
    # level, but total OI remains visible when the current snapshot has no flow
    # baseline yet. These are zones, never guarantees.
    for wall in oi_evidence.get("oi_levels", []):
        try:
            strike = float(wall.get("strike"))
            put_rel = float(wall.get("put_relative_oi") or 0.0)
            call_rel = float(wall.get("call_relative_oi") or 0.0)
            put_writer = float(wall.get("put_writer_strength") or 0.0)
            call_writer = float(wall.get("call_writer_strength") or 0.0)
            put_support_flow = float(wall.get("put_support_flow_strength") or put_writer)
            call_resistance_flow = float(wall.get("call_resistance_flow_strength") or call_writer)
        except (TypeError, ValueError, OverflowError):
            continue
        if strike < latest.close and put_rel >= 0.18:
            strength = min(3.8, 1.0 + 1.20 * put_rel + 0.75 * put_support_flow)
            source = "OI_PUT_ACTIVE_SUPPORT" if put_support_flow >= 0.25 else "OI_PUT_CONCENTRATION_SUPPORT"
            levels.append(PriceLevel(strike, "SUPPORT", source, strength))
        elif strike > latest.close and call_rel >= 0.18:
            strength = min(3.8, 1.0 + 1.20 * call_rel + 0.75 * call_resistance_flow)
            source = "OI_CALL_ACTIVE_RESISTANCE" if call_resistance_flow >= 0.25 else "OI_CALL_CONCENTRATION_RESISTANCE"
            levels.append(PriceLevel(strike, "RESISTANCE", source, strength))
    # Cluster nearby levels while preserving each level's provenance in source text.
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
            strength = min(4.0, sum(x.strength for x in cluster))
            price = sum(x.price * x.strength for x in cluster) / sum(x.strength for x in cluster)
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
    }
    sources = {part.strip() for part in level.source.split("+") if part.strip()}
    return bool(sources - context_only)


def _nearest_level(levels: Sequence[PriceLevel], side: str, price: float, minimum_strength: float = 1.0) -> Optional[PriceLevel]:
    candidates = [
        x for x in levels
        if x.side == side and x.strength >= minimum_strength
        and _level_has_structural_provenance(x)
        and ((x.price > price + 1e-6) if side == "RESISTANCE" else (x.price < price - 1e-6))
    ]
    if not candidates:
        return None
    return min(candidates, key=lambda x: x.price) if side == "RESISTANCE" else max(candidates, key=lambda x: x.price)


def detect_setup(candles: Sequence[Candle], levels: Sequence[PriceLevel], structure: Mapping[str, Any], config: Config, oi_evidence: Optional[Mapping[str, Any]] = None) -> Optional[Setup]:
    if len(candles) < 3:
        return None
    current = candles[-1]
    previous = candles[-2]
    atr1 = float(structure.get("atr_1m") or atr(candles) or 0.0)
    if atr1 <= 0:
        return None
    buffer = max(config.minimum_stop_points * 0.15, atr1 * 0.05)
    # Evaluate only recently completed candles. No future candles are used.
    recent = list(candles[-(config.support_lookback_candles + 1):])
    supports = [x for x in levels if x.side == "SUPPORT" and x.strength >= 1.0]
    resistances = [x for x in levels if x.side == "RESISTANCE" and x.strength >= 1.0]
    setups: list[Setup] = []
    for level in supports:
        test_band = max(buffer, atr1 * 0.12)
        historical_touches = [(i, c) for i, c in enumerate(recent[:-1]) if c.low <= level.price + test_band and c.low >= level.price - max(atr1 * 0.7, buffer)]
        historical_sweeps = [(i, c) for i, c in enumerate(recent[:-1]) if c.low < level.price - buffer and c.close > level.price]
        current_touch = current.low <= level.price + test_band and current.low >= level.price - max(atr1 * 0.7, buffer)
        current_sweep = current.low < level.price - buffer and current.close > level.price
        reclaimed = current.close >= level.price + buffer and current.close > current.open and current.close > previous.close
        if reclaimed and (historical_touches or historical_sweeps or current_touch or current_sweep):
            evidence_candles = [c for _, c in (historical_sweeps if historical_sweeps else historical_touches)]
            if current_touch or current_sweep:
                evidence_candles.append(current)
            invalidation = min(c.low for c in evidence_candles + [current])
            kind = "LIQUIDITY_SWEEP_RECLAIM" if (historical_sweeps or current_sweep) else "RANGE_EDGE_REVERSAL" if structure.get("regime") == "SIDEWAYS" else "TREND_CONTINUATION_PULLBACK" if structure.get("higher_timeframe_bias") == "BULLISH" else "SUPPORT_BOUNCE"
            confidence = min(0.95, 0.58 + 0.08 * (current.close > previous.high) + 0.08 * (current.close > level.price + 2 * buffer) + 0.05 * (structure.get("higher_timeframe_bias") == "BULLISH"))
            setups.append(Setup(kind, "BULLISH", current.close, invalidation, current.close_time, level.price, level.source, confidence))
    for level in resistances:
        test_band = max(buffer, atr1 * 0.12)
        historical_touches = [(i, c) for i, c in enumerate(recent[:-1]) if c.high >= level.price - test_band and c.high <= level.price + max(atr1 * 0.7, buffer)]
        historical_sweeps = [(i, c) for i, c in enumerate(recent[:-1]) if c.high > level.price + buffer and c.close < level.price]
        current_touch = current.high >= level.price - test_band and current.high <= level.price + max(atr1 * 0.7, buffer)
        current_sweep = current.high > level.price + buffer and current.close < level.price
        rejected = current.close <= level.price - buffer and current.close < current.open and current.close < previous.close
        if rejected and (historical_touches or historical_sweeps or current_touch or current_sweep):
            evidence_candles = [c for _, c in (historical_sweeps if historical_sweeps else historical_touches)]
            if current_touch or current_sweep:
                evidence_candles.append(current)
            invalidation = max(c.high for c in evidence_candles + [current])
            kind = "LIQUIDITY_SWEEP_RECLAIM" if (historical_sweeps or current_sweep) else "RANGE_EDGE_REVERSAL" if structure.get("regime") == "SIDEWAYS" else "TREND_CONTINUATION_PULLBACK" if structure.get("higher_timeframe_bias") == "BEARISH" else "RESISTANCE_REJECTION"
            confidence = min(0.95, 0.58 + 0.08 * (current.close < previous.low) + 0.08 * (current.close < level.price - 2 * buffer) + 0.05 * (structure.get("higher_timeframe_bias") == "BEARISH"))
            setups.append(Setup(kind, "BEARISH", current.close, invalidation, current.close_time, level.price, level.source, confidence))
    # Breakout/retest requires a prior close through a level, a retest and a
    # completed confirming candle. It does not jump directly at an old breakout.
    for level in resistances:
        crossed = any(c.close > level.price + buffer for c in recent[:-1])
        retested = current.low <= level.price + max(buffer, atr1 * 0.12) and current.low >= level.price - max(atr1 * 0.6, buffer)
        if crossed and retested and current.close > level.price + buffer and current.close > current.open:
            setups.append(Setup("BREAKOUT_RETEST", "BULLISH", current.close, min(current.low, level.price - buffer), current.close_time, level.price, level.source, 0.78))
    for level in supports:
        crossed = any(c.close < level.price - buffer for c in recent[:-1])
        retested = current.high >= level.price - max(buffer, atr1 * 0.12) and current.high <= level.price + max(atr1 * 0.6, buffer)
        if crossed and retested and current.close < level.price - buffer and current.close < current.open:
            setups.append(Setup("BREAKDOWN_RETEST", "BEARISH", current.close, max(current.high, level.price + buffer), current.close_time, level.price, level.source, 0.78))
    # Continuous-trend continuation: require a completed pullback candle and
    # a fresh resumed break, not merely an EMA touch. This supplements the
    # level-based sweep/retest patterns for persistent directional sessions.
    if len(recent) >= 4:
        last_three = recent[-3:]
        if structure.get("execution_direction") == "BEARISH" and structure.get("higher_timeframe_bias") in {"BEARISH", "TRANSITION", "UNKNOWN"}:
            had_pullback = any(c.close > c.open for c in last_three[:-1])
            resumed = current.close < current.open and current.close < previous.low
            if had_pullback and resumed:
                invalidation = max(c.high for c in last_three)
                setups.append(Setup("TREND_CONTINUATION_PULLBACK", "BEARISH", current.close, invalidation,
                                    current.close_time, previous.low, "BEARISH_PULLBACK_RESUMPTION", 0.76))
        if structure.get("execution_direction") == "BULLISH" and structure.get("higher_timeframe_bias") in {"BULLISH", "TRANSITION", "UNKNOWN"}:
            had_pullback = any(c.close < c.open for c in last_three[:-1])
            resumed = current.close > current.open and current.close > previous.high
            if had_pullback and resumed:
                invalidation = min(c.low for c in last_three)
                setups.append(Setup("TREND_CONTINUATION_PULLBACK", "BULLISH", current.close, invalidation,
                                    current.close_time, previous.high, "BULLISH_PULLBACK_RESUMPTION", 0.76))

    if not setups:
        return None
    # Prefer a pattern aligned with both OI's current raw direction and the
    # one-minute execution tape. This prevents countertrend bounce patterns
    # from constantly replacing a valid continuation watch.
    priority = {"BREAKDOWN_RETEST": 0, "BREAKOUT_RETEST": 0, "LIQUIDITY_SWEEP_RECLAIM": 1,
                "TREND_CONTINUATION_PULLBACK": 2, "RESISTANCE_REJECTION": 3,
                "SUPPORT_BOUNCE": 3, "RANGE_EDGE_REVERSAL": 3}
    raw_oi = str((oi_evidence or {}).get("raw_label", (oi_evidence or {}).get("label", "MISSING")))
    execution = str(structure.get("execution_direction", "UNKNOWN"))
    def setup_rank(candidate: Setup) -> tuple[float, float, float, float]:
        alignment = 1.0 if candidate.direction == raw_oi else 0.0
        price_alignment = 1.0 if candidate.direction == execution else 0.0
        return (alignment + price_alignment, -priority.get(candidate.kind, 9), candidate.price_confidence,
                candidate.trigger if candidate.direction == "BULLISH" else -candidate.trigger)
    return sorted(setups, key=setup_rank, reverse=True)[0]


# ---------- Risk planning and option pricing ----------
def black_scholes_price(spot: float, strike: float, years: float, volatility: float, rate: float, side: str) -> float:
    """European option approximation, used only for scenarios and calibrated to market mid."""
    if spot <= 0 or strike <= 0 or years <= 0 or volatility <= 0:
        return max(0.0, spot - strike) if side == "CE" else max(0.0, strike - spot)
    sqrt_t = math.sqrt(years)
    d1 = (math.log(spot / strike) + (rate + 0.5 * volatility**2) * years) / (volatility * sqrt_t)
    d2 = d1 - volatility * sqrt_t
    cdf = lambda x: 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))
    if side == "CE":
        return max(0.0, spot * cdf(d1) - strike * math.exp(-rate * years) * cdf(d2))
    return max(0.0, strike * math.exp(-rate * years) * cdf(-d2) - spot * cdf(-d1))


def years_to_expiry(expiry: date, now: datetime) -> float:
    expiry_close = datetime.combine(expiry, dtime(15, 30), tzinfo=IST)
    seconds = max(60.0, (expiry_close - now.astimezone(IST)).total_seconds())
    return seconds / (365.0 * 24 * 3600)


def price_option_scenario(quote: OptionQuote, current_spot: float, scenario_spot: float, now: datetime, config: Config, *, adverse_iv_points: float) -> Optional[float]:
    """Reprice via Black-Scholes, anchored to observed market mid, including gamma/theta/vega effects.

    IV is a percentage-point field in Upstox's chain response. We do not treat
    a missing/implausible IV as zero; the option fails closed instead.
    """
    if quote.iv is None or not (1.0 <= quote.iv <= 100.0) or quote.mid <= 0:
        return None
    iv = quote.iv / 100.0
    shocked_iv = max(0.01, min(1.0, (quote.iv - adverse_iv_points) / 100.0))
    years = years_to_expiry(quote.expiry, now)
    remaining_years = max(1.0 / (365 * 24 * 3600), years - config.expected_hold_minutes / (365.0 * 24 * 60))
    base = black_scholes_price(current_spot, quote.strike, years, iv, config.annual_risk_free_rate, quote.side)
    changed = black_scholes_price(scenario_spot, quote.strike, remaining_years, shocked_iv, config.annual_risk_free_rate, quote.side)
    # Local calibration preserves the observed market mid despite model basis error.
    return max(0.0, quote.mid + changed - base)


def choose_targets_and_stop(entry: float, setup: Setup, levels: Sequence[PriceLevel], structure: Mapping[str, Any], config: Config) -> dict[str, Any]:
    atr1 = float(structure.get("atr_1m") or 0.0)
    if atr1 <= 0:
        raise ScannerError("ATR_UNAVAILABLE", "ATR is not available for structural risk calculation")
    stop_buffer = max(config.minimum_stop_points, atr1 * config.stop_buffer_atr_fraction)
    if setup.direction == "BULLISH":
        stop = setup.invalidation - stop_buffer
        risk = entry - stop
        t1_level = _nearest_level(levels, "RESISTANCE", entry, config.min_level_strength)
        t2_level = _nearest_level([l for l in levels if not (t1_level and abs(l.price - t1_level.price) < max(2.0, atr1 * 0.10))], "RESISTANCE", (t1_level.price if t1_level else entry), config.min_level_strength) if t1_level else None
    else:
        stop = setup.invalidation + stop_buffer
        risk = stop - entry
        t1_level = _nearest_level(levels, "SUPPORT", entry, config.min_level_strength)
        t2_level = _nearest_level([l for l in levels if not (t1_level and abs(l.price - t1_level.price) < max(2.0, atr1 * 0.10))], "SUPPORT", (t1_level.price if t1_level else entry), config.min_level_strength) if t1_level else None
    if risk <= 0 or not math.isfinite(risk):
        raise ScannerError("INVALID_STRUCTURAL_STOP", "Structural stop is not on the risk side of current entry")
    if risk > atr1 * config.max_stop_atr:
        raise ScannerError("STOP_TOO_WIDE", f"Structural risk {risk:.2f} points exceeds {config.max_stop_atr:.2f} ATR ({atr1:.2f})")
    if t1_level is None:
        raise ScannerError("NO_VALID_T1", "No valid opposing resistance/support exists; refusing to fabricate a target")
    reward1 = t1_level.price - entry if setup.direction == "BULLISH" else entry - t1_level.price
    rr1 = reward1 / risk if reward1 > 0 else 0.0
    if rr1 + 1e-9 < config.min_underlying_rr:
        raise ScannerError("RR_BELOW_2R", f"Nearest opposing barrier {t1_level.price:.2f} provides {rr1:.2f}R; minimum is {config.min_underlying_rr:.2f}R")
    if t2_level is not None:
        t2 = t2_level.price
        t2_source = t2_level.source
    else:
        # T2 is explicitly an R-multiple projection only after structural T1
        # passes; it never substitutes for or bypasses T1.
        t2 = entry + (3.0 * risk if setup.direction == "BULLISH" else -3.0 * risk)
        t2_source = "3R_PROJECTION_NOT_A_STRUCTURAL_BARRIER"
    if setup.direction == "BULLISH" and t2 <= t1_level.price:
        t2 = t1_level.price + max(atr1, risk * 0.5)
        t2_source = "ABOVE_T1_ATR_PROJECTION"
    elif setup.direction == "BEARISH" and t2 >= t1_level.price:
        t2 = t1_level.price - max(atr1, risk * 0.5)
        t2_source = "BELOW_T1_ATR_PROJECTION"
    return {"entry_underlying": entry, "stop_underlying": stop, "t1_underlying": t1_level.price, "t1_source": t1_level.source, "t2_underlying": t2, "t2_source": t2_source, "risk_points": risk, "reward_t1_points": reward1, "underlying_rr": rr1, "stop_buffer_points": stop_buffer, "atr_1m": atr1}


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


def select_option_and_risk(
    direction: str, spot: float, spot_quote_time: Optional[datetime], chain_records: Sequence[OptionRecord], full_quotes: Mapping[str, Mapping[str, Any]],
    expiry: date, now: datetime, plan: Mapping[str, Any], structure: Mapping[str, Any], config: Config,
) -> dict[str, Any]:
    """Select the best liquid permitted strike; never calculate option-premium RR.

    Underlying spot levels alone determine 2:1 risk/reward. Option data is used
    for instrument eligibility, executable quote quality, delta suitability and
    time-decay-aware ranking only.
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
    offsets = config.strike_offsets_ce if side == "CE" else config.strike_offsets_pe
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
            quote_age, quote_clock_skew, quote_timestamp_status = quote_timing(
                quote.timestamp, local_now, error_code="OPTION_QUOTE_CLOCK_SKEW"
            )
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
        # Higher score favours executable depth, tight spreads, a useful delta,
        # and less decay relative to premium. No option RR is calculated.
        delta_score = max(0.0, 1.0 - abs(abs(quote.delta) - 0.55) / 0.35)
        spread_score = max(0.0, 1.0 - quote.spread_pct / max(config.max_spread_pct, 1e-9))
        depth_score = min(1.0, math.log1p(quote.bid_qty + quote.ask_qty) / math.log1p(5000.0))
        volume_score = min(1.0, math.log1p(quote.volume) / math.log1p(50000.0))
        decay_score = max(0.0, 1.0 - min(theta_fraction, 1.0))
        score = 0.34 * delta_score + 0.27 * spread_score + 0.16 * depth_score + 0.13 * volume_score + 0.10 * decay_score
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
            "selection_method": "LIQUIDITY_SPREAD_DELTA_AND_TIME_DECAY_SCORE_SPOT_RR_ONLY",
            "spot_risk_reward": plan.get("underlying_rr"),
            "_rank": (score, -quote.spread_pct, delta_score, volume_score, -abs(offset)),
        })
    if not candidates:
        reason = rejections.most_common(1)[0][0] if rejections else "NO_VALID_OPTION_QUOTES"
        details = ", ".join(f"{key}:{value}" for key, value in rejections.most_common(5))
        raise ScannerError(reason, f"No eligible {side} contract among allowed ATM offsets. {details}")
    candidates.sort(key=lambda candidate: candidate["_rank"], reverse=True)
    selected = candidates[0]
    selected.pop("_rank", None)
    selected["candidate_count_passed"] = len(candidates)
    selected["candidate_count_rejected"] = sum(rejections.values())
    selected["rejection_counts"] = dict(rejections)
    selected["spot_quote_timestamp"] = spot_quote_time.isoformat() if spot_quote_time else None
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
    """Walk newly completed candles chronologically and persist the most recent setup.

    Historical candle patterns update state only; they do not become historical
    fills. A later gate revalidates any watch against the current live quote.
    """
    pending = _setup_from_state(state.get("setup_watch"))
    for i, candle in enumerate(candles):
        if previous_processed is not None and candle.start <= previous_processed:
            continue
        if pending is not None:
            age = (candle.close_time - pending.confirmed_at).total_seconds()
            breached = (pending.direction == "BULLISH" and candle.low <= pending.invalidation) or (pending.direction == "BEARISH" and candle.high >= pending.invalidation)
            if age > config.setup_state_ttl_minutes * 60 or breached:
                pending = None
                state["setup_watch"] = None
        prefix = candles[:i + 1]
        atr_value = atr(prefix)
        # Current OI walls are the latest available positioning context for
        # this scan. Any reconstructed candidate is still revalidated against
        # the current live quote and is never treated as a historical fill.
        prefix_levels = build_levels(prefix, previous_daily, oi_evidence or _empty_oi(), None, atr_value, config)
        prefix_structure = price_regime(prefix, aggregate_candles(prefix, 5, candle.close_time))
        candidate = detect_setup(prefix, prefix_levels, prefix_structure, config, oi_evidence)
        if candidate is not None:
            replace_pending = pending is None
            if pending is not None and candidate.direction == pending.direction:
                # For bearish entries, a higher trigger is more favourable; for
                # bullish entries, a lower trigger is more favourable. Do not
                # chase a market by walking the trigger in the adverse direction.
                better_trigger = (candidate.trigger > pending.trigger + 0.25) if candidate.direction == "BEARISH" else (candidate.trigger < pending.trigger - 0.25)
                no_worse_entry = (candidate.trigger >= pending.trigger - 0.25) if candidate.direction == "BEARISH" else (candidate.trigger <= pending.trigger + 0.25)
                replace_pending = better_trigger or (no_worse_entry and candidate.price_confidence >= pending.price_confidence + 0.12)
            if replace_pending:
                pending = candidate
                state["setup_watch"] = {"direction": candidate.direction, "kind": candidate.kind,
                                        "confirmed_at": candidate.confirmed_at.isoformat(), "trigger": candidate.trigger,
                                        "invalidation": candidate.invalidation, "source_level": candidate.source_level,
                                        "source": candidate.source, "price_confidence": candidate.price_confidence}
    return pending



def select_active_setup(
    current: Optional[Setup], tracked: Optional[Setup], spot: float,
    oi: Mapping[str, Any], structure: Mapping[str, Any], now: datetime,
    config: Config,
) -> Optional[Setup]:
    """Preserve a valid watch; switch direction only on a confirmed OI/price reversal."""
    def valid(candidate: Optional[Setup]) -> bool:
        if candidate is None:
            return False
        age = (now - candidate.confirmed_at).total_seconds()
        if age < -1 or age > config.setup_max_age_minutes * 60:
            return False
        if candidate.direction == "BEARISH" and spot >= candidate.invalidation:
            return False
        if candidate.direction == "BULLISH" and spot <= candidate.invalidation:
            return False
        return True

    cur_valid, tracked_valid = valid(current), valid(tracked)
    if not tracked_valid:
        return current if cur_valid else None
    if not cur_valid:
        return tracked
    assert current is not None and tracked is not None
    if current.direction == tracked.direction:
        better = (current.trigger > tracked.trigger + 0.25) if current.direction == "BEARISH" else (current.trigger < tracked.trigger - 0.25)
        no_worse_entry = (current.trigger >= tracked.trigger - 0.25) if current.direction == "BEARISH" else (current.trigger <= tracked.trigger + 0.25)
        fresher = current.confirmed_at > tracked.confirmed_at
        if better or (no_worse_entry and fresher and current.price_confidence >= tracked.price_confidence + 0.10):
            return current
        return tracked
    raw = str(oi.get("raw_label", oi.get("label", "MISSING")))
    execution = str(structure.get("execution_direction", "UNKNOWN"))
    htf = str(structure.get("higher_timeframe_bias", "UNKNOWN"))
    reversal_confirmed = raw == current.direction and (execution == current.direction or htf == current.direction)
    strong_candidate = current.price_confidence >= max(0.72, config.min_mixed_price_confirmation)
    tracked_age = (now - tracked.confirmed_at).total_seconds()
    if reversal_confirmed and strong_candidate and tracked_age >= 60:
        return current
    return tracked

def authorize_direction(oi: Mapping[str, Any], setup: Setup, structure: Mapping[str, Any], config: Config) -> None:
    """OI-first authorization with explicit reversal and sideways-wall handling."""
    stable = str(oi.get("label", "MISSING"))
    raw = str(oi.get("raw_label", stable))
    if not oi.get("compared_to_previous_successful_snapshot"):
        raise ScannerError("OI_BASELINE_MISSING", "Two valid same-session snapshots are required before OI direction can be evaluated")
    age = oi.get("oi_age_seconds")
    if age is not None and float(age) > config.max_oi_age_seconds:
        raise ScannerError("OI_STALE", f"Latest OI snapshot is {float(age):.0f}s old")
    expected = setup.direction
    execution = str(structure.get("execution_direction", "UNKNOWN"))
    htf = str(structure.get("higher_timeframe_bias", "UNKNOWN"))
    confidence = float(oi.get("confidence") or 0.0)
    balance = abs(float(oi.get("directional_balance") or 0.0))

    # Strong first-snapshot reversal evidence is not forced to wait for a
    # second 3-minute cycle when current OI, price execution and setup agree.
    if raw == expected and confidence >= config.min_oi_direction_confidence:
        if execution == expected:
            return
        if htf == expected and setup.price_confidence >= config.min_mixed_price_confirmation:
            return
        if setup.price_confidence >= max(0.82, config.min_mixed_price_confirmation):
            return
        raise ScannerError("OI_WAIT_PRICE_ALIGNMENT", f"Raw OI is {raw}, but one-minute execution is {execution}; wait for price alignment")

    if stable == expected:
        if raw in {expected, "MIXED", "MISSING"}:
            if execution in {expected, "MIXED", "UNKNOWN"} or htf == expected:
                return
        raise ScannerError("OI_PRICE_DIRECTION_CONFLICT", f"Stable OI is {stable}, but market structure does not support {expected}")

    # Sideways markets are locally directional at a well-defined range edge.
    # Allow put-writing support bounces or call-writing resistance rejections
    # when the wall's own OI flow agrees and the candle setup is confirmed.
    if "SIDEWAYS" in str(structure.get("regime", "")) or htf == "SIDEWAYS":
        rows = [x for x in oi.get("oi_levels", []) if isinstance(x, Mapping)]
        source_level = setup.source_level if setup.source_level is not None else setup.trigger
        nearest = min(rows, key=lambda row: abs(float(row.get("strike", source_level)) - source_level), default=None)
        if nearest is not None and abs(float(nearest.get("strike", source_level)) - source_level) <= 0.55 * 50:
            local_strength = float(nearest.get("put_support_flow_strength" if expected == "BULLISH" else "call_resistance_flow_strength") or nearest.get("put_writer_strength" if expected == "BULLISH" else "call_writer_strength") or 0.0)
            if local_strength >= 0.20 and setup.price_confidence >= config.min_mixed_price_confirmation:
                return

    if raw in {"BULLISH", "BEARISH"} and raw != expected:
        code = "OI_REVERSAL_CONFLICT" if oi.get("transition_status") == "REVERSAL_WATCH" else "OI_RAW_DIRECTION_CONFLICT"
        raise ScannerError(code, f"Latest OI positioning points {raw}, while the setup points {expected}")
    if stable == "MIXED" or raw == "MIXED":
        if setup.price_confidence < config.min_mixed_price_confirmation:
            raise ScannerError("OI_MIXED_WAIT_PRICE_CONFIRMATION", f"Setup confidence {setup.price_confidence:.2f} is below {config.min_mixed_price_confirmation:.2f}")
        if execution != expected and htf != expected:
            raise ScannerError("OI_MIXED_WAIT_PRICE_CONFIRMATION", "OI is mixed and neither one-minute execution nor five-minute context aligns with the setup")
        if confidence < 0.25 and balance < 0.15:
            raise ScannerError("OI_MIXED_WAIT_PRICE_CONFIRMATION", "OI directional evidence is too weak to support the setup")
        return
    raise ScannerError("OI_BASELINE_MISSING", "No usable OI directional evidence is available")


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
    """Combine OI-first direction with independent price and futures context."""
    raw = str(oi.get("raw_label", oi.get("label", "MISSING")))
    stable = str(oi.get("label", "MISSING"))
    execution = str(structure.get("execution_direction", "UNKNOWN"))
    htf = str(structure.get("higher_timeframe_bias", "UNKNOWN"))
    previous = str(oi.get("previous_directional_label") or "")
    horizon_direction = str(oi.get("multi_horizon_direction") or "UNAVAILABLE")
    regime = "TRANSITION"
    if "SIDEWAYS" in str(structure.get("regime", "")) or htf == "SIDEWAYS":
        regime = "SIDEWAYS"
    elif raw == "BEARISH" and execution == "BEARISH":
        regime = "CONTINUOUS_BEARISH" if htf in {"BEARISH", "TRANSITION", "UNKNOWN"} else "BULLISH_TO_BEARISH_REVERSAL"
        if previous == "BULLISH" or horizon_direction == "BULLISH":
            regime = "BULLISH_TO_BEARISH_REVERSAL"
    elif raw == "BULLISH" and execution == "BULLISH":
        regime = "CONTINUOUS_BULLISH" if htf in {"BULLISH", "TRANSITION", "UNKNOWN"} else "BEARISH_TO_BULLISH_REVERSAL"
        if previous == "BEARISH" or horizon_direction == "BEARISH":
            regime = "BEARISH_TO_BULLISH_REVERSAL"
    elif htf == "BEARISH" and execution == "BULLISH":
        regime = "BEARISH_TO_BULLISH_REVERSAL_WATCH"
    elif htf == "BULLISH" and execution == "BEARISH":
        regime = "BULLISH_TO_BEARISH_REVERSAL_WATCH"
    elif execution in {"BULLISH", "BEARISH"} and raw == execution:
        regime = f"EARLY_SESSION_{'BULLISH' if execution == 'BULLISH' else 'BEARISH'}"
    elif execution == "MIXED" and raw in {"BULLISH", "BEARISH"}:
        regime = f"OI_LEADING_{raw}_WAIT_PRICE"
    elif htf == "SIDEWAYS":
        regime = "SIDEWAYS"
    maturity = str(structure.get("higher_timeframe_status") or "")
    if maturity == "PROVISIONAL_EARLY_SESSION" and not regime.startswith(("EARLY_SESSION_", "SIDEWAYS")):
        regime = f"EARLY_SESSION_{regime}"
    elif maturity == "DEVELOPING_CONTEXT" and not regime.startswith(("DEVELOPING_", "SIDEWAYS")):
        regime = f"DEVELOPING_{regime}"
    confidence = float(oi.get("confidence") or 0.0)
    futures_signal = str(futures.get("futures_oi_signal") or "UNAVAILABLE")
    # Futures OI is a corroborating vote, never a substitute for option OI.
    futures_bias = "BULLISH" if futures_signal in {"LONG_BUILDUP_BULLISH", "SHORT_COVERING_BULLISH"} else "BEARISH" if futures_signal in {"SHORT_BUILDUP_BEARISH", "LONG_UNWINDING_BEARISH"} else "UNKNOWN"
    return {
        "scenario": regime, "oi_raw_direction": raw, "oi_stable_direction": stable,
        "price_execution_direction": execution, "higher_timeframe_bias": htf,
        "futures_positioning": futures_signal, "futures_bias": futures_bias,
        "oi_confidence": confidence,
        "multi_horizon_direction": horizon_direction,
        "multi_horizon_balance": oi.get("multi_horizon_balance"),
        "alignment": "ALIGNED" if raw == execution and raw in {"BULLISH", "BEARISH"} else "PARTIAL_OR_CONFLICTING",
    }


def _oi_wall_score(level: Mapping[str, Any], side: str) -> float:
    """Score an OI target wall using concentration and the direction of its flow.

    Put support is strengthened by put writing/put-long unwinding and weakened
    by put buying/short covering. Call resistance is strengthened by call
    writing/call-long unwinding and weakened by call buying/short covering.
    """
    try:
        if side == "PE":
            relative = float(level.get("put_relative_oi") or 0.0)
            supportive = float(level.get("put_support_flow_strength", level.get("put_writer_strength", 0.0)) or 0.0)
            opposing = float(level.get("put_bearish_flow_strength") or 0.0)
            delta_pct = float(level.get("put_delta_oi_pct_snapshot") or 0.0)
            threshold = float(level.get("oi_material_threshold_pct") or 2.0)
        else:
            relative = float(level.get("call_relative_oi") or 0.0)
            supportive = float(level.get("call_resistance_flow_strength", level.get("call_writer_strength", 0.0)) or 0.0)
            opposing = float(level.get("call_bullish_flow_strength") or 0.0)
            delta_pct = float(level.get("call_delta_oi_pct_snapshot") or 0.0)
            threshold = float(level.get("oi_material_threshold_pct") or 2.0)
        values = (relative, supportive, opposing, delta_pct, threshold)
        if not all(math.isfinite(v) for v in values):
            return 0.0
    except (TypeError, ValueError, OverflowError):
        return 0.0
    fresh_build = min(1.0, abs(delta_pct) / max(threshold, 1e-9)) if delta_pct > 0 and supportive > opposing else 0.0
    score = 0.48 * relative + 0.37 * supportive + 0.15 * fresh_build - 0.22 * opposing
    return max(0.0, min(1.0, score))


def _price_is_in_direction(price: float, entry: float, direction: str, target: bool) -> bool:
    if target:
        return price > entry if direction == "BULLISH" else price < entry
    return price < entry if direction == "BULLISH" else price > entry


def _oi_wall_is_material(row: Mapping[str, Any], side: str) -> tuple[bool, float]:
    score = _oi_wall_score(row, side)
    relative = float(row.get("put_relative_oi" if side == "PE" else "call_relative_oi") or 0.0)
    supportive = float(row.get("put_support_flow_strength" if side == "PE" else "call_resistance_flow_strength") or 0.0)
    opposing = float(row.get("put_bearish_flow_strength" if side == "PE" else "call_bullish_flow_strength") or 0.0)
    threshold = float(row.get("oi_material_threshold_pct") or 2.0)
    materially_opposed = opposing >= supportive + 0.25 and relative < 0.75
    material = not materially_opposed and (score >= 0.20 or relative >= 0.38 or supportive >= 0.25)
    return material, score


def _combined_directional_levels(
    entry: float,
    direction: str,
    oi: Mapping[str, Any],
    levels: Sequence[PriceLevel],
    atr1: float,
    *,
    target: bool,
    minimum_strength: float = 1.0,
) -> list[dict[str, Any]]:
    """Combine independent OI walls and price-structure levels without inventing prices.

    Nearby evidence is clustered into one barrier. A level supported by both
    price structure and an eligible OI wall receives stronger provenance.
    Pure futures VWAP context is never promoted to a hard target or stop.
    """
    side = ("RESISTANCE" if direction == "BULLISH" else "SUPPORT") if target else ("SUPPORT" if direction == "BULLISH" else "RESISTANCE")
    candidates: list[dict[str, Any]] = []
    for level in levels:
        if level.side != side or not _price_is_in_direction(level.price, entry, direction, target):
            continue
        sources = [part.strip() for part in level.source.split("+") if part.strip()]
        structural_sources = [src for src in sources if not src.startswith("OI_") and src != "FUTURES_VWAP_CONTEXT_ONLY"]
        if structural_sources and level.strength >= minimum_strength:
            candidates.append({
                "price": float(level.price), "source": level.source,
                "structural_strength": float(level.strength), "oi_score": 0.0,
                "oi_value": 0.0, "flow": None, "has_structure": True,
                "has_oi": any(src.startswith("OI_") for src in sources),
            })

    oi_side = ("CE" if direction == "BULLISH" else "PE") if target else ("PE" if direction == "BULLISH" else "CE")
    oi_field = "call_oi" if oi_side == "CE" else "put_oi"
    for row in oi.get("oi_levels", []):
        if not isinstance(row, Mapping):
            continue
        try:
            price = float(row.get("strike"))
            oi_value = float(row.get(oi_field) or 0.0)
        except (TypeError, ValueError, OverflowError):
            continue
        if oi_value <= 0 or not _price_is_in_direction(price, entry, direction, target):
            continue
        material, score = _oi_wall_is_material(row, oi_side)
        if not material:
            continue
        candidates.append({
            "price": price,
            "source": f"OI_{oi_side}_WALL",
            "structural_strength": 0.0,
            "oi_score": score,
            "oi_value": oi_value,
            "flow": row.get("put_flow" if oi_side == "PE" else "call_flow"),
            "has_structure": False,
            "has_oi": True,
        })

    if not candidates:
        return []
    candidates.sort(key=lambda item: item["price"])
    tolerance = max(2.5, atr1 * 0.12)
    clusters: list[list[dict[str, Any]]] = []
    for item in candidates:
        if clusters and abs(item["price"] - median([x["price"] for x in clusters[-1]])) <= tolerance:
            clusters[-1].append(item)
        else:
            clusters.append([item])

    combined: list[dict[str, Any]] = []
    for cluster in clusters:
        weights = [max(0.1, x["structural_strength"] + x["oi_score"] * 2.0) for x in cluster]
        price = sum(x["price"] * weight for x, weight in zip(cluster, weights)) / sum(weights)
        sources = list(dict.fromkeys(src for x in cluster for src in x["source"].split("+") if src))
        has_structure = any(x["has_structure"] for x in cluster)
        has_oi = any(x["has_oi"] for x in cluster)
        combined.append({
            "price": price,
            "source": "+".join(sources),
            "structural_strength": max((x["structural_strength"] for x in cluster), default=0.0),
            "oi_score": max((x["oi_score"] for x in cluster), default=0.0),
            "oi_value": max((x["oi_value"] for x in cluster), default=0.0),
            "flow": next((x["flow"] for x in cluster if x.get("flow")), None),
            "has_structure": has_structure,
            "has_oi": has_oi,
            "confluence": "OI_AND_PRICE_STRUCTURE" if has_structure and has_oi else "OI_ONLY" if has_oi else "PRICE_STRUCTURE_ONLY",
            "strength": min(5.0, max((x["structural_strength"] for x in cluster), default=0.0) + max((x["oi_score"] for x in cluster), default=0.0) * 2.0),
        })
    # Sort by distance from entry in the direction of travel, nearest barrier first.
    combined.sort(key=lambda item: abs(item["price"] - entry))
    return combined


def choose_oi_targets_and_stop(
    entry: float,
    setup: Setup,
    oi: Mapping[str, Any],
    structure: Mapping[str, Any],
    config: Config,
    now: datetime,
    levels: Sequence[PriceLevel] = (),
) -> dict[str, Any]:
    """Plan stops and sequential targets from OI walls plus price structure.

    T1 is always the nearest qualified opposing barrier; T2 is the next
    distinct barrier beyond T1. The nearest barrier is never skipped to
    manufacture a better reward/risk ratio. Stops use the tighter valid
    structural/OI/setup invalidation reference plus an ATR buffer.
    """
    if not oi.get("oi_levels"):
        raise ScannerError("OI_LEVELS_UNAVAILABLE", "No same-expiry OI strike profile is available for risk planning")
    atr1 = float(structure.get("atr_1m") or 0.0)
    atr5 = float(structure.get("atr_5m") or atr1 or 0.0)
    if atr1 <= 0 or not math.isfinite(atr1):
        raise ScannerError("ATR_UNAVAILABLE", "One-minute ATR is unavailable for risk planning")
    buffer = max(config.minimum_stop_points, atr1 * max(config.stop_buffer_atr_fraction, 0.12), 2.0)
    max_relevant_distance = max(6.0 * 50.0, 5.0 * atr5, 250.0)

    stop_refs = _combined_directional_levels(
        entry, setup.direction, oi, levels, atr1, target=False,
        minimum_strength=config.min_level_strength,
    )
    eligible_stop_refs = [x for x in stop_refs if abs(float(x["price"]) - entry) <= max_relevant_distance]
    try:
        invalidation = float(setup.invalidation)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ScannerError("INVALID_OI_STOP", "Setup invalidation is not a valid numeric price") from exc
    if not math.isfinite(invalidation) or invalidation <= 0 or not _price_is_in_direction(invalidation, entry, setup.direction, False):
        raise ScannerError("INVALID_OI_STOP", "Setup invalidation must be finite, positive and on the risk side of entry")
    stop_reference = invalidation
    stop_reference_source = "SETUP_INVALIDATION"
    if eligible_stop_refs:
        nearest_stop_ref = min(eligible_stop_refs, key=lambda x: abs(float(x["price"]) - entry))
        candidate_price = float(nearest_stop_ref["price"])
        tighter = max(stop_reference, candidate_price) if setup.direction == "BULLISH" else min(stop_reference, candidate_price)
        if tighter == candidate_price:
            stop_reference_source = nearest_stop_ref["source"]
        stop_reference = tighter
    stop = stop_reference - buffer if setup.direction == "BULLISH" else stop_reference + buffer
    risk = abs(entry - stop)
    if not math.isfinite(risk) or risk <= 0:
        raise ScannerError("INVALID_OI_STOP", "Protective stop is not on the risk side of the current NIFTY entry")
    if risk > max(config.max_stop_atr * atr1, config.max_stop_atr * atr5):
        raise ScannerError("STOP_TOO_WIDE", f"Structural stop distance {risk:.1f} points exceeds the volatility limit")

    targets = _combined_directional_levels(
        entry, setup.direction, oi, levels, atr1, target=True,
        minimum_strength=config.min_level_strength,
    )
    min_target_distance = max(2.0, atr1 * 0.20)
    targets = [x for x in targets if abs(float(x["price"]) - entry) >= min_target_distance]
    if not targets:
        raise ScannerError("OI_STRUCTURE_TARGET_UNAVAILABLE", "No qualified opposing OI/price-structure barrier is available")
    t1_row = targets[0]
    t2_row = targets[1] if len(targets) > 1 else None
    t1 = float(t1_row["price"])
    t2 = float(t2_row["price"]) if t2_row else None
    reward = abs(t1 - entry)
    rr = reward / risk
    if rr + 1e-9 < config.min_underlying_rr:
        raise ScannerError(
            "RR_BELOW_2R_OI_STRUCTURE",
            f"Nearest opposing barrier {t1:.2f} gives {rr:.2f}R using entry {entry:.2f} and stop {stop:.2f}; minimum is {config.min_underlying_rr:.2f}R",
        )

    local_now = now.astimezone(IST)
    close_time = datetime.combine(local_now.date(), dtime(15, 30), tzinfo=IST)
    minutes_left = max(0.0, (close_time - local_now).total_seconds() / 60.0)
    usable_minutes = max(1.0, min(minutes_left, 180.0))
    expected_move = max(atr1 * math.sqrt(usable_minutes) * 1.15, atr5 * math.sqrt(usable_minutes / 5.0) * 0.85)
    t1_distance = abs(entry - t1)
    time_feasibility = expected_move / max(t1_distance, 1e-9)
    if minutes_left < 1.0 or time_feasibility < 0.45:
        raise ScannerError("OI_T1_TIME_FEASIBILITY_LOW", f"Nearest barrier is {t1_distance:.1f} points away with estimated remaining-session move {expected_move:.1f} points")

    return {
        "entry_underlying": entry,
        "stop_underlying": stop,
        "initial_stop_underlying": stop,
        "stop_source": "TIGHTER_OF_OI_PRICE_STRUCTURE_AND_SETUP_INVALIDATION",
        "stop_reference_price": stop_reference,
        "stop_reference_source": stop_reference_source,
        "risk_points": risk,
        "stop_buffer_points": buffer,
        "atr_1m": atr1,
        "atr_5m": atr5,
        "t1_underlying": t1,
        "t1_source": t1_row["source"],
        "t1_confluence": t1_row["confluence"],
        "t1_level_strength": t1_row["strength"],
        "t1_oi_score": t1_row["oi_score"],
        "t1_oi": t1_row["oi_value"],
        "t1_flow": t1_row["flow"],
        "t2_underlying": t2,
        "t2_source": t2_row["source"] if t2_row else None,
        "t2_confluence": t2_row["confluence"] if t2_row else None,
        "t2_level_strength": t2_row["strength"] if t2_row else None,
        "t2_oi_score": t2_row["oi_score"] if t2_row else None,
        "t2_oi": t2_row["oi_value"] if t2_row else None,
        "underlying_rr": rr,
        "t2_underlying_rr": abs(t2 - entry) / risk if t2 is not None else None,
        "estimated_remaining_session_move": expected_move,
        "t1_time_feasibility_ratio": time_feasibility,
        "minutes_to_market_close": minutes_left,
        "target_method": "NEAREST_OI_AND_PRICE_STRUCTURE_BARRIERS",
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
        "last_monitored_candle": latest_candle.start.isoformat(),
        "favourable_spot_extreme": float(risk_plan["entry_underlying"]),
        "recovered_from_legacy": bool(recovered),
        "recovered_at": opened.isoformat() if recovered else None,
        "created_at": now_ist().isoformat(),
    }


def _continuation_is_confirmed(
    direction: str,
    oi: Mapping[str, Any],
    structure: Mapping[str, Any],
    config: Config,
) -> bool:
    raw = str(oi.get("raw_label") or oi.get("label") or "MISSING").upper()
    stable = str(oi.get("label") or "MISSING").upper()
    execution = str(structure.get("execution_direction") or "UNKNOWN").upper()
    confidence = float(oi.get("confidence") or 0.0)
    return (
        raw == direction
        and stable in {direction, "MIXED"}
        and execution == direction
        and confidence >= config.min_oi_direction_confidence
        and bool(oi.get("compared_to_previous_successful_snapshot"))
        and (oi.get("oi_age_seconds") is None or float(oi.get("oi_age_seconds")) <= config.max_oi_age_seconds)
    )


def confirmed_opposite_reversal(
    active: Mapping[str, Any],
    setup: Optional[Setup],
    oi: Mapping[str, Any],
    structure: Mapping[str, Any],
    spot: float,
    quote_received_at: datetime,
    config: Config,
    *,
    chain_refresh_ok: bool,
) -> tuple[bool, dict[str, Any]]:
    """Require persistent fresh OI reversal plus a completed opposite price setup.

    OI-only and price-only reversals are watches, not position invalidations.
    Entry extension is deliberately not checked here: the old thesis can be
    invalidated even when the new trade is already too extended to enter.
    """
    old_direction = _position_direction(active)
    opposite = "BEARISH" if old_direction == "BULLISH" else "BULLISH"
    evidence = {
        "old_direction": old_direction,
        "reversal_direction": opposite,
        "oi_raw_label": oi.get("raw_label", oi.get("label")),
        "oi_stable_label": oi.get("label"),
        "oi_confidence": oi.get("confidence"),
        "oi_persistence_count": oi.get("persistence_count"),
        "price_execution_direction": structure.get("execution_direction"),
        "setup_direction": setup.direction if setup else None,
    }
    if not chain_refresh_ok or not oi.get("compared_to_previous_successful_snapshot"):
        return False, {**evidence, "reversal_status": "WAITING_FOR_FRESH_OI"}
    if (oi.get("oi_age_seconds") is not None and
            float(oi.get("oi_age_seconds")) > config.max_oi_age_seconds):
        return False, {**evidence, "reversal_status": "WAITING_FOR_FRESH_OI"}
    if str(oi.get("raw_label") or "").upper() != opposite or str(oi.get("label") or "").upper() != opposite:
        return False, {**evidence, "reversal_status": "OI_REVERSAL_NOT_PERSISTENT"}
    if int(oi.get("persistence_count") or 0) < 2 or oi.get("transition_status") != "DIRECTION_PERSISTENT":
        return False, {**evidence, "reversal_status": "OI_REVERSAL_NOT_PERSISTENT"}
    if float(oi.get("confidence") or 0.0) < config.min_oi_direction_confidence:
        return False, {**evidence, "reversal_status": "OI_REVERSAL_CONFIDENCE_LOW"}
    if str(structure.get("execution_direction") or "UNKNOWN").upper() != opposite:
        return False, {**evidence, "reversal_status": "PRICE_REVERSAL_NOT_CONFIRMED"}
    if setup is None or setup.direction != opposite:
        return False, {**evidence, "reversal_status": "OPPOSITE_SETUP_MISSING"}
    setup_age = (quote_received_at - setup.confirmed_at).total_seconds()
    if setup_age < -1 or setup_age > config.setup_max_age_minutes * 60:
        return False, {**evidence, "reversal_status": "OPPOSITE_SETUP_STALE", "setup_age_seconds": setup_age}
    if setup.price_confidence < config.min_mixed_price_confirmation:
        return False, {**evidence, "reversal_status": "OPPOSITE_SETUP_CONFIDENCE_LOW", "setup_age_seconds": setup_age}
    try:
        validate_live_setup_trigger(setup, spot, max(0.5, float(structure.get("atr_1m") or 0.0) * 0.15))
    except ScannerError as exc:
        return False, {**evidence, "reversal_status": exc.code, "reversal_message": str(exc), "setup_age_seconds": setup_age}
    return True, {
        **evidence,
        "reversal_status": "CONFIRMED",
        "setup_kind": setup.kind,
        "setup_confirmed_at": setup.confirmed_at.isoformat(),
        "setup_trigger": setup.trigger,
        "setup_invalidation": setup.invalidation,
        "setup_price_confidence": setup.price_confidence,
        "setup_age_seconds": setup_age,
        "spot": spot,
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


def _update_plan_target(active: dict[str, Any], name: str, row: Mapping[str, Any]) -> None:
    risk = dict(active.get("risk_plan") or {})
    active[f"{name}_underlying"] = float(row["price"])
    active[f"{name}_source"] = row.get("source")
    active[f"{name}_confluence"] = row.get("confluence")
    risk[f"{name}_underlying"] = float(row["price"])
    risk[f"{name}_source"] = row.get("source")
    risk[f"{name}_confluence"] = row.get("confluence")
    risk[f"{name}_level_strength"] = row.get("strength")
    risk[f"{name}_oi_score"] = row.get("oi_score")
    risk[f"{name}_oi"] = row.get("oi_value")
    risk[f"{name}_flow"] = row.get("flow")
    active["risk_plan"] = risk


def _refresh_active_targets(
    active: dict[str, Any], oi: Mapping[str, Any], levels: Sequence[PriceLevel],
    spot: float, structure: Mapping[str, Any], config: Config,
) -> list[dict[str, Any]]:
    """Reassess only nearer OI/structure barriers; never extend targets away from price.

    The original entry and minimum 2R T1 qualification remain immutable. A
    newly formed barrier may tighten an unhit target, but it cannot move T1/T2
    farther away or invent a projected price.
    """
    events: list[dict[str, Any]] = []
    direction = _position_direction(active)
    atr1 = float(structure.get("atr_1m") or (active.get("risk_plan") or {}).get("atr_1m") or 0.0)
    if atr1 <= 0:
        return events
    candidates = _combined_directional_levels(
        spot, direction, oi, levels, atr1, target=True,
        minimum_strength=config.min_level_strength,
    )
    entry = float(active["entry_spot"])
    initial_risk = abs(entry - float(active.get("initial_stop_underlying") or active["stop_underlying"]))
    min_t1_reward = config.min_underlying_rr * initial_risk
    t1 = float(active["t1_underlying"])
    t2_raw = active.get("t2_underlying")
    t2 = float(t2_raw) if t2_raw is not None else None

    if not active.get("t1_hit"):
        # T1 can tighten to a newly confirmed barrier only if it remains ahead
        # of the market and still preserves the original minimum 2R reward.
        eligible_t1 = [
            row for row in candidates
            if abs(float(row["price"]) - entry) + 1e-9 >= min_t1_reward
            and ((spot < float(row["price"]) < t1) if direction == "BULLISH"
                 else (t1 < float(row["price"]) < spot))
        ]
        if eligible_t1:
            row = eligible_t1[0]
            previous = t1
            _update_plan_target(active, "t1", row)
            events.append({"event_type": "TARGET_1_TIGHTENED", "previous_t1": previous,
                           "new_t1": float(row["price"]), "source": row.get("source"),
                           "confluence": row.get("confluence")})
            t1 = float(row["price"])

        # Refresh the second objective independently of whether T1 moved.
        # This allows newly confirmed OI/structure evidence to establish T2
        # while the original trade is still before T1.
        next_rows = [
            candidate for candidate in candidates
            if ((float(candidate["price"]) > t1) if direction == "BULLISH"
                else (float(candidate["price"]) < t1))
        ]
        if next_rows:
            next_row = next_rows[0]
            next_price = float(next_row["price"])
            should_update_t2 = (
                t2 is None
                or ((next_price < t2) if direction == "BULLISH" else (next_price > t2))
            )
            if should_update_t2:
                old_t2 = t2
                _update_plan_target(active, "t2", next_row)
                events.append({"event_type": "TARGET_2_ADDED" if old_t2 is None else "TARGET_2_REASSESSED",
                               "previous_t2": old_t2, "new_t2": next_price,
                               "source": next_row.get("source"),
                               "confluence": next_row.get("confluence")})
    elif t2 is not None:
        # After T1, only tighten the remaining runner's T2 objective. Require
        # a meaningful distance beyond current spot to avoid micro-noise levels.
        min_distance = max(2.0, atr1 * 0.20)
        eligible_t2 = [
            row for row in candidates
            if ((spot + min_distance < float(row["price"]) < t2) if direction == "BULLISH"
                else (t2 < float(row["price"]) < spot - min_distance))
        ]
        if eligible_t2:
            row = eligible_t2[0]
            previous = t2
            _update_plan_target(active, "t2", row)
            events.append({"event_type": "TARGET_2_TIGHTENED", "previous_t2": previous,
                           "new_t2": float(row["price"]), "source": row.get("source"),
                           "confluence": row.get("confluence")})
    return events


def _trail_active_stop(active: dict[str, Any], levels: Sequence[PriceLevel], spot: float,
                       structure: Mapping[str, Any], config: Config) -> Optional[dict[str, Any]]:
    """After T1, trail the stop only behind a confirmed structural level."""
    if not active.get("t1_hit"):
        return None
    direction = _position_direction(active)
    atr1 = float(structure.get("atr_1m") or (active.get("risk_plan") or {}).get("atr_1m") or 0.0)
    if atr1 <= 0:
        return None
    buffer = max(config.minimum_stop_points, atr1 * max(config.stop_buffer_atr_fraction, 0.12))
    side = "SUPPORT" if direction == "BULLISH" else "RESISTANCE"
    old_stop = float(active["stop_underlying"])
    qualifying = [
        level for level in levels
        if level.side == side and level.strength >= max(config.min_level_strength, 1.5)
        and _level_has_structural_provenance(level)
    ]
    candidates: list[tuple[float, PriceLevel]] = []
    for level in qualifying:
        candidate = float(level.price) - buffer if direction == "BULLISH" else float(level.price) + buffer
        improves = candidate > old_stop if direction == "BULLISH" else candidate < old_stop
        remains_behind_spot = candidate < spot if direction == "BULLISH" else candidate > spot
        if improves and remains_behind_spot:
            candidates.append((candidate, level))
    if not candidates:
        return None
    candidate, source = (max(candidates, key=lambda item: item[0]) if direction == "BULLISH"
                         else min(candidates, key=lambda item: item[0]))
    active["stop_underlying"] = candidate
    risk = dict(active.get("risk_plan") or {})
    risk.update({"stop_underlying": candidate, "trailing_stop_source": source.source,
                 "trailing_stop_buffer_points": buffer})
    active["risk_plan"] = risk
    return {"previous_stop": old_stop, "new_stop": candidate,
            "source": source.source, "buffer_points": buffer}


def manage_active_position(
    active: dict[str, Any],
    candles: Sequence[Candle],
    spot: float,
    quote_received_at: datetime,
    oi: Mapping[str, Any],
    structure: Mapping[str, Any],
    setup: Optional[Setup],
    config: Config,
    *,
    chain_refresh_ok: bool,
    option_quote: Optional[OptionQuote],
    levels: Sequence[PriceLevel] = (),
) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]], str, dict[str, Any]]:
    """Advance the one active signal position; no new strike can replace it while open."""
    active = dict(active)
    direction = _position_direction(active)
    opened_at = parse_datetime(active.get("opened_at"))
    last_candle = parse_datetime(active.get("last_monitored_candle"))
    if opened_at is None or last_candle is None:
        raise ScannerError("ACTIVE_POSITION_STATE_INVALID", "Active position has invalid opened_at or last_monitored_candle")
    if active.get("status") != "OPEN":
        raise ScannerError("ACTIVE_POSITION_STATE_INVALID", "Only OPEN positions can be managed")
    entry_spot = float(active.get("entry_spot") or 0.0)
    t1 = float(active.get("t1_underlying") or 0.0)
    t2_raw = active.get("t2_underlying")
    t2 = float(t2_raw) if t2_raw is not None else None
    stop = float(active.get("stop_underlying") or 0.0)
    if min(entry_spot, t1, stop) <= 0:
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

    target_revisions = _refresh_active_targets(active, oi, levels, spot, structure, config)
    for revision in target_revisions:
        event_type = str(revision.pop("event_type"))
        reason = "NEW_NEARER_OI_STRUCTURE_BARRIER"
        events.append(_position_event(active, event_type, reason, quote_received_at,
                                      spot, premium_bid=latest_bid, details=revision))
    t1 = float(active["t1_underlying"])
    t2_raw = active.get("t2_underlying")
    t2 = float(t2_raw) if t2_raw is not None else None

    def close(reason: str, at: datetime, price: float, detail: Optional[Mapping[str, Any]] = None):
        closed, event = close_active_position(active, reason, at, price, premium_bid=latest_bid, details=detail)
        events.append(event)
        return None, events, reason, {"position_closed": True, "exit_reason": reason,
                                      "closed_position": closed, **(dict(detail or {}))}

    # Process every completed one-minute candle since the prior persisted checkpoint.
    new_candles = [c for c in sorted(candles, key=lambda item: item.start)
                   if c.start > last_candle and c.start > opened_at.replace(second=0, microsecond=0)]
    if new_candles:
        first_gap = (new_candles[0].start - last_candle).total_seconds()
        if first_gap > 60.5:
            raise ScannerError(
                "POSITION_CANDLE_GAP",
                f"First available monitoring candle {new_candles[0].start.isoformat()} is more than one minute after checkpoint {last_candle.isoformat()}; position lock retained",
            )
    for previous, current in zip(new_candles, new_candles[1:]):
        gap = (current.start - previous.start).total_seconds()
        if gap > 60.5:
            raise ScannerError("POSITION_CANDLE_GAP", f"Missing one-minute monitoring candles between {previous.start.isoformat()} and {current.start.isoformat()}; position lock retained")
    for candle in new_candles:
        if candle.start <= last_candle or candle.start <= opened_at.replace(second=0, microsecond=0):
            continue
        stop_hit = (candle.low <= stop) if direction == "BULLISH" else (candle.high >= stop)
        if stop_hit:
            active["last_monitored_candle"] = candle.start.isoformat()
            return close("STOP_LOSS_HIT" if not active.get("t1_hit") else "BREAKEVEN_OR_TRAILING_STOP_HIT",
                         candle.close_time, stop, {"monitoring_candle": candle.start.isoformat(), "candle_high": candle.high, "candle_low": candle.low})

        t1_hit = (candle.high >= t1) if direction == "BULLISH" else (candle.low <= t1)
        t2_hit = t2 is not None and ((candle.high >= t2) if direction == "BULLISH" else (candle.low <= t2))
        if not active.get("t1_hit") and t1_hit:
            if t2 is None:
                return close(
                    "TARGET_1_HIT_NO_T2", candle.close_time, t1,
                    {"full_exit_pct": active.get("remaining_pct", 100.0),
                     "reason": "No second qualified OI/structure barrier was available; T1 is the final objective.",
                     "monitoring_candle": candle.start.isoformat()},
                )
            active["t1_hit"] = True
            active["t1_hit_at"] = candle.close_time.isoformat()
            partial_pct = float(active.get("t1_partial_exit_pct") or config.t1_partial_exit_pct)
            active["remaining_pct"] = max(0.0, 100.0 - partial_pct)
            active["stop_underlying"] = entry_spot
            events.append(_position_event(
                active, "TARGET_1_PARTIAL", "TARGET_1_HIT_CONTINUE_MANAGING", candle.close_time,
                t1, premium_bid=latest_bid,
                details={"partial_exit_pct": partial_pct, "remaining_pct": active["remaining_pct"],
                         "t1_underlying": t1, "t2_underlying": t2, "stop_moved_to_entry": True,
                         "continuation_status": "CONFIRMED" if _continuation_is_confirmed(direction, oi, structure, config) else "WAITING_FOR_OI_PRICE_ALIGNMENT",
                         "monitoring_candle": candle.start.isoformat()},
            ))
            continuation_ok = _continuation_is_confirmed(direction, oi, structure, config)
            active["continuation_status"] = "CONFIRMED" if continuation_ok else "WAITING_FOR_OI_PRICE_ALIGNMENT"
            # A temporary loss of alignment is not itself a reversal. Keep the
            # remaining runner protected at entry; a confirmed opposite reversal,
            # premium safeguard, breakeven stop or T2 will close it.
            # If a single candle trades through both sequential targets, the T1
            # partial is recorded first and the remaining quantity closes at T2.
            if t2_hit:
                return close("TARGET_2_HIT", candle.close_time, t2,
                             {"partial_exit_pct": partial_pct, "remaining_pct_before_exit": active["remaining_pct"],
                              "monitoring_candle": candle.start.isoformat()})
        elif active.get("t1_hit") and t2_hit:
            return close("TARGET_2_HIT", candle.close_time, t2,
                         {"remaining_pct_before_exit": active.get("remaining_pct"),
                          "monitoring_candle": candle.start.isoformat()})

        favourable = (candle.high - entry_spot) if direction == "BULLISH" else (entry_spot - candle.low)
        if favourable > 0:
            active["favourable_spot_extreme"] = max(
                float(active.get("favourable_spot_extreme") or entry_spot),
                entry_spot + favourable if direction == "BULLISH" else entry_spot - favourable,
            ) if direction == "BULLISH" else min(
                float(active.get("favourable_spot_extreme") or entry_spot),
                entry_spot - favourable,
            )
        active["last_monitored_candle"] = candle.start.isoformat()

    replay = active.get("pending_replay_reversal")
    if isinstance(replay, Mapping):
        replay_at = parse_datetime(replay.get("timestamp"))
        if replay_at is not None and replay_at <= quote_received_at:
            active.pop("pending_replay_reversal", None)
            return close("REVERSAL_CONFIRMED", replay_at, float(replay.get("spot") or spot),
                         {**dict(replay), "replayed_from_audit": True})

    # Check the current fresh NIFTY quote too; completed-candle monitoring above
    # catches intrainterval touches even when price has since retraced.
    spot_stop_hit = (spot <= float(active["stop_underlying"])) if direction == "BULLISH" else (spot >= float(active["stop_underlying"]))
    if spot_stop_hit:
        return close("STOP_LOSS_HIT" if not active.get("t1_hit") else "BREAKEVEN_OR_TRAILING_STOP_HIT",
                     quote_received_at, float(active["stop_underlying"]), {"touch_source": "LIVE_SPOT_QUOTE"})
    if not active.get("t1_hit"):
        spot_t1_hit = (spot >= t1) if direction == "BULLISH" else (spot <= t1)
        if spot_t1_hit:
            if t2 is None:
                return close(
                    "TARGET_1_HIT_NO_T2", quote_received_at, t1,
                    {"full_exit_pct": active.get("remaining_pct", 100.0),
                     "reason": "No second qualified OI/structure barrier was available; T1 is the final objective.",
                     "touch_source": "LIVE_SPOT_QUOTE"},
                )
            active["t1_hit"] = True
            active["t1_hit_at"] = quote_received_at.isoformat()
            partial_pct = float(active.get("t1_partial_exit_pct") or config.t1_partial_exit_pct)
            active["remaining_pct"] = max(0.0, 100.0 - partial_pct)
            active["stop_underlying"] = entry_spot
            events.append(_position_event(active, "TARGET_1_PARTIAL", "TARGET_1_HIT_CONTINUE_MANAGING",
                                          quote_received_at, t1, premium_bid=latest_bid,
                                          details={"partial_exit_pct": partial_pct, "remaining_pct": active["remaining_pct"],
                                                   "t1_underlying": t1, "t2_underlying": t2,
                                                   "stop_moved_to_entry": True,
                                                   "continuation_status": "CONFIRMED" if _continuation_is_confirmed(direction, oi, structure, config) else "WAITING_FOR_OI_PRICE_ALIGNMENT",
                                                   "touch_source": "LIVE_SPOT_QUOTE"}))
            spot_t2_hit_same_quote = (spot >= t2) if direction == "BULLISH" else (spot <= t2)
            if spot_t2_hit_same_quote:
                return close("TARGET_2_HIT", quote_received_at, t2,
                             {"partial_exit_pct": partial_pct, "remaining_pct_before_exit": active["remaining_pct"],
                              "touch_source": "LIVE_SPOT_QUOTE_CROSSED_T1_AND_T2"})
            continuation_ok = _continuation_is_confirmed(direction, oi, structure, config)
            active["continuation_status"] = "CONFIRMED" if continuation_ok else "WAITING_FOR_OI_PRICE_ALIGNMENT"
    elif t2 is not None:
        spot_t2_hit = (spot >= t2) if direction == "BULLISH" else (spot <= t2)
        if spot_t2_hit:
            return close("TARGET_2_HIT", quote_received_at, t2, {"touch_source": "LIVE_SPOT_QUOTE"})

    if active.get("t1_hit"):
        active["continuation_status"] = (
            "CONFIRMED" if _continuation_is_confirmed(direction, oi, structure, config)
            else "WAITING_FOR_OI_PRICE_ALIGNMENT"
        )
        stop_revision = _trail_active_stop(active, levels, spot, structure, config)
        if stop_revision:
            events.append(_position_event(
                active, "STOP_TRAILED", "NEW_CONFIRMED_STRUCTURAL_STOP", quote_received_at,
                spot, premium_bid=latest_bid, details=stop_revision,
            ))

    reversed_now, reversal_evidence = confirmed_opposite_reversal(
        active, setup, oi, structure, spot, quote_received_at, config,
        chain_refresh_ok=chain_refresh_ok,
    )
    if reversed_now:
        return close("REVERSAL_CONFIRMED", quote_received_at, spot, reversal_evidence)

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
        if active.get("t1_hit") and peak_drawdown_pct >= config.premium_trailing_drawdown_pct:
            return close("PREMIUM_TRAILING_PROTECTION", quote_received_at, spot,
                         {"premium_bid": latest_bid, "peak_bid": peak_bid, "peak_drawdown_pct": peak_drawdown_pct})
        elapsed_minutes = max(0.0, (quote_received_at - opened_at).total_seconds() / 60.0)
        atr1 = float(structure.get("atr_1m") or active.get("risk_plan", {}).get("atr_1m") or 0.0)
        best_spot = float(active.get("favourable_spot_extreme") or entry_spot)
        if direction == "BULLISH":
            best_spot = max(best_spot, spot)
            active["favourable_spot_extreme"] = best_spot
            best_favourable_move = best_spot - entry_spot
        else:
            best_spot = min(best_spot, spot)
            active["favourable_spot_extreme"] = best_spot
            best_favourable_move = entry_spot - best_spot
        if (elapsed_minutes >= config.premium_decay_review_minutes
                and best_favourable_move < config.no_progress_min_spot_move_atr * atr1
                and premium_loss_pct >= config.premium_decay_min_loss_pct):
            return close("PREMIUM_DECAY_NO_PROGRESS", quote_received_at, spot,
                         {"premium_bid": latest_bid, "premium_loss_pct": premium_loss_pct,
                          "elapsed_minutes": elapsed_minutes, "best_favourable_spot_move": best_favourable_move,
                          "atr_1m": atr1})

    active["last_checked_at"] = quote_received_at.isoformat()
    active["last_spot"] = spot
    active["last_oi_direction"] = oi.get("raw_label", oi.get("label"))
    active["last_price_execution"] = structure.get("execution_direction")
    active["monitoring_status"] = "ACTIVE" if latest_bid is not None else "SPOT_ONLY_OPTION_QUOTE_UNAVAILABLE"
    summary = {
        "position_open": True,
        "position_id": active.get("position_id"),
        "instrument_key": active.get("instrument_key"),
        "side": active.get("side"),
        "strike": active.get("strike"),
        "direction": direction,
        "entry_spot": entry_spot,
        "stop_underlying": active.get("stop_underlying"),
        "t1_underlying": t1,
        "t2_underlying": t2,
        "t1_hit": active.get("t1_hit"),
        "remaining_pct": active.get("remaining_pct"),
        "premium_bid": latest_bid,
        "premium_loss_pct": active.get("premium_loss_pct"),
        "monitoring_status": active.get("monitoring_status"),
        "reversal_status": reversal_evidence.get("reversal_status") if 'reversal_evidence' in locals() else "NOT_CONFIRMED",
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


def _nearest_quote_key(full_quotes: Mapping[str, Mapping[str, Any]], instrument_key: str) -> Optional[Mapping[str, Any]]:
    return full_quotes.get(instrument_key)


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
        }
    for collection in (
        "chain_snapshots", "seen_signal_keys", "pending_notifications",
        "delivered_signal_keys", "notification_history", "oi_evidence_history", "position_history",
    ):
        _ensure_state_list(state, collection)
    state.setdefault("active_position", None)
    state.setdefault("position_reconciliation_required", False)
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
        bars_5m = aggregate_candles(index_candles, 5, now)
        structure = price_regime(index_candles, bars_5m)
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
        levels = build_levels(index_candles, daily_candles, oi, futures_vwap, structure.get("atr_1m"), config)
        level_summary = _levels_summary(levels, spot)
        # Reconstruct setup state chronologically from every candle not yet
        # processed by the prior workflow run. This is not historical execution.
        tracked_setup = advance_setup_watch(index_candles, previous_processed, daily_candles, state, config, oi)
        current_setup = detect_setup(index_candles, levels, structure, config, oi)
        setup = select_active_setup(current_setup, tracked_setup, spot, oi, structure, quote_received_at, config)
        detected_new_setup = setup is not None and (tracked_setup is None or setup.confirmed_at != tracked_setup.confirmed_at or setup.direction != tracked_setup.direction)
        state["last_processed_candle"] = index_candles[-1].start.isoformat()
        # Freshness-validated futures quote/VWAP context was built before levels.
        if oi.get("raw_label") in {"BULLISH", "BEARISH"} and oi.get("label") == "MIXED":
            transition = oi.get("transition_status") or "PENDING_PERSISTENCE"
            oi_state = f"{transition}_{oi.get('raw_label')}"
        else:
            oi_state = oi.get("label", "MISSING")
        market_scenario = classify_market_scenario(oi, structure, future_context)
        base_result.update({"expiry": expiry.isoformat(), "underlying_key": index_key, "spot": spot, "spot_context": spot_context, "oi": {k: v for k, v in oi.items() if k != "features"}, "oi_label": oi.get("label", "MISSING"), "oi_state": oi_state, "oi_raw_label": oi.get("raw_label", oi.get("label", "MISSING")), "option_chain_status": oi.get("source_refresh_status", "SUCCESS" if chain_refresh_ok else "UNKNOWN"), "option_chain_error": chain_refresh_error.code if chain_refresh_error else None, "structure": structure, "regime": structure.get("regime"), "market_scenario": market_scenario, "levels": level_summary, "futures": future_context, "setup": json_safe(setup) if setup else None, "decision": "NO_TRADE", "reason_code": "NO_CONFIRMED_SETUP"})
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
                        "details": {k: v for k, v in management_detail.items() if k != "closed_position"},
                    }
                    if exit_reason == "REVERSAL_CONFIRMED":
                        allow_reversal_entry = True
                        can_evaluate_new_entry = True
                    else:
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
            else:
                setup_age = (quote_received_at - setup.confirmed_at).total_seconds()
                if setup_age < -1 or setup_age > config.setup_max_age_minutes * 60:
                    raise ScannerError("MISSED_OR_STALE_SETUP", f"Setup confirmation is {setup_age:.0f}s old; no backdated entry allowed")
                validate_live_setup_trigger(setup, spot, max(0.5, float(structure.get("atr_1m") or 0.0) * 0.15))
                extension = abs(spot - setup.trigger)
                if structure.get("atr_1m") and extension > float(structure["atr_1m"]) * config.max_entry_extension_atr:
                    raise ScannerError("ENTRY_TOO_EXTENDED", f"Current spot is {extension:.2f} points from setup trigger")
                if not chain_refresh_ok:
                    detail = chain_refresh_error.code if chain_refresh_error else "UNKNOWN_REFRESH_FAILURE"
                    raise ScannerError("OPTION_CHAIN_REFRESH_FAILED", f"A fresh option chain/Greeks snapshot is required before entry; latest refresh failed with {detail}")
                authorize_direction(oi, setup, structure, config)
                plan = choose_oi_targets_and_stop(spot, setup, oi, structure, config, quote_received_at, levels=levels)
                base_result["risk_plan"] = plan
                selected = select_option_and_risk(setup.direction, spot, spot_quote_time, chain_records, full_quotes, expiry, quote_received_at, plan, structure, config)
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
                        "candidate_offsets_allowed": list(config.strike_offsets_ce if setup.direction == "BULLISH" else config.strike_offsets_pe),
                        "notification_status": "QUEUED" if config.email_configured else "NOT_CONFIGURED",
                        "active_position_summary": {
                            "position_id": signal_key, "direction": setup.direction,
                            "side": selected["side"], "strike": selected["strike"],
                            "entry_spot": plan["entry_underlying"], "stop_underlying": plan["stop_underlying"],
                            "t1_underlying": plan["t1_underlying"], "t2_underlying": plan.get("t2_underlying"),
                            "t1_partial_exit_pct": config.t1_partial_exit_pct,
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
        base_result.update({"decision": "NO_TRADE", "error_type": "ScannerError", "reason_code": exc.code, "message": str(exc), "expiry": expiry.isoformat() if expiry else None, "underlying_key": index_row.get("instrument_key") if index_row else None, "oi_label": oi.get("label", "MISSING"), "regime": base_result.get("regime", "UNKNOWN"), "spot": base_result.get("spot", spot_chain or None)})
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
            base_result["message"] = f"{exc}; state persistence failed"
        base_result["audit_persistence"] = persist_audit_records(
            config, session_date, base_result, oi_diagnostics=oi
        )
        return json_safe(base_result)
    except Exception as exc:
        LOG.exception("Unexpected scanner failure")
        base_result.update({"decision": "NO_TRADE", "error_type": type(exc).__name__, "reason_code": "UNEXPECTED_ERROR", "message": str(exc)[:500]})
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
        f"Price execution: {structure.get('execution_direction', '—')}",
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
      ('Price execution', str(structure.get('execution_direction') or '—')),
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
        message["Message-ID"] = f"<nifty-v107-{signal_key}@market-scanner.local>"
    message.set_content(text_body)
    message.add_alternative(html_body, subtype="html")
    attachment = dict(data)
    attachment["notification_status"] = "SENT"
    message.add_attachment(
        json.dumps(json_safe(attachment), indent=2, allow_nan=False).encode("utf-8"),
        maintype="application", subtype="json",
        filename=f"nifty_v107_signal_{signal_short}.json",
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
        description="NIFTY 50 intraday OI + price-structure scanner (no order execution)"
    )
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--config-check", action="store_true", help="Validate Upstox and Gmail configuration")
    modes.add_argument("--prepare-only", action="store_true", help="Run scan and queue alerts without sending")
    modes.add_argument("--scan-and-claim", action="store_true", help="Run one scan and claim its queued alerts for this GitHub run attempt")
    modes.add_argument("--claim-notifications", action="store_true", help="Claim queued alerts for this GitHub run attempt")
    modes.add_argument("--deliver-claimed", action="store_true", help="Send only alerts claimed by this GitHub run attempt")
    modes.add_argument("--requeue-notification", metavar="SIGNAL_KEY", help="Manually requeue one uncertain alert after checking Gmail")
    modes.add_argument("--reconcile-position", metavar="FLAT_OR_SIGNAL_KEY", help="First v107 deployment: explicitly confirm flat or recover one legacy signal position")
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
            failure_codes = {
                "UNEXPECTED_ERROR", "STATE_SAVE_FAILED", "API_AUTH_FAILED",
                "API_PERMISSION_DENIED", "API_HTTP_ERROR", "API_HTTP_403", "API_HTTP_401",
            }
            if scan_result.get("reason_code") in failure_codes:
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
        failure_codes = {
            "UNEXPECTED_ERROR", "STATE_SAVE_FAILED", "API_AUTH_FAILED",
            "API_PERMISSION_DENIED", "API_HTTP_ERROR", "API_HTTP_403", "API_HTTP_401",
        }
        return 0 if result.get("reason_code") not in failure_codes else 1
    except ScannerError as exc:
        result = {
            "scanner_version": VERSION,
            "timestamp": now_ist().isoformat(),
            "decision": "NO_TRADE",
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
            "reason_code": "UNEXPECTED_ERROR",
            "error_type": type(exc).__name__,
            "message": str(exc)[:500],
        }, separators=(",", ":"), sort_keys=True))
        return 1

if __name__ == "__main__":
    raise SystemExit(main())
