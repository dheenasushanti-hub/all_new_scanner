#!/usr/bin/env python3
"""Offline regression tests for the NIFTY v107 position manager.

No Upstox API or live SMTP calls are made by this suite.
"""
from __future__ import annotations

import json
import tempfile
import unittest
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import market_scanner_v107 as scanner

IST = ZoneInfo("Asia/Kolkata")


def dt(hour: int = 10, minute: int = 0, second: int = 0) -> datetime:
    return datetime(2026, 10, 30, hour, minute, second, tzinfo=IST)


def config(tmp: Path | None = None, **overrides) -> scanner.Config:
    base = {
        "token": "offline-test-token",
        "state_file": (tmp / "state.json") if tmp else Path("/tmp/v107-test-state.json"),
        "audit_dir": (tmp / "audit") if tmp else Path("/tmp/v107-test-audit"),
        "instrument_cache": (tmp / "cache.gz") if tmp else Path("/tmp/v107-test-cache.gz"),
        "min_underlying_rr": 2.0,
        "t1_partial_exit_pct": 50.0,
        "max_premium_loss_pct": 20.0,
        "premium_trailing_drawdown_pct": 25.0,
        "premium_decay_review_minutes": 15.0,
        "premium_decay_min_loss_pct": 12.0,
        "no_progress_min_spot_move_atr": 0.25,
    }
    base.update(overrides)
    return scanner.Config(**base)


def candle(start: datetime, open_: float, high: float, low: float, close: float) -> scanner.Candle:
    return scanner.Candle(start, open_, high, low, close, 1000.0, 0.0)


def selected(side: str = "CE", strike: float = 23000.0, entry: float = 100.0) -> dict:
    return {
        "instrument_key": "NSE_FO|TEST_CE" if side == "CE" else "NSE_FO|TEST_PE",
        "side": side,
        "strike": strike,
        "expiry": "2026-11-03",
        "reference_entry_ask": entry,
        "reference_bid": entry - 0.5,
        "quote_timestamp": dt().isoformat(),
        "ltp": entry,
        "volume": 100000,
        "oi": 500000,
        "bid_qty": 1000,
        "ask_qty": 1000,
        "delta": 0.55 if side == "CE" else -0.55,
        "iv_percent": 14.0,
        "theta": -10.0,
    }


def risk_plan(direction: str = "BULLISH") -> dict:
    if direction == "BULLISH":
        return {
            "entry_underlying": 100.0, "stop_underlying": 90.0,
            "initial_stop_underlying": 90.0, "t1_underlying": 110.0,
            "t1_source": "OI_CE_WALL+SWING_HIGH", "t1_confluence": "OI_AND_PRICE_STRUCTURE",
            "t2_underlying": 120.0, "t2_source": "OI_CE_WALL+SESSION_HIGH",
            "t2_confluence": "OI_AND_PRICE_STRUCTURE", "underlying_rr": 1.0,
            "atr_1m": 2.0, "atr_5m": 3.0,
        }
    return {
        "entry_underlying": 100.0, "stop_underlying": 110.0,
        "initial_stop_underlying": 110.0, "t1_underlying": 90.0,
        "t1_source": "OI_PE_WALL+SWING_LOW", "t1_confluence": "OI_AND_PRICE_STRUCTURE",
        "t2_underlying": 80.0, "t2_source": "OI_PE_WALL+SESSION_LOW",
        "t2_confluence": "OI_AND_PRICE_STRUCTURE", "underlying_rr": 1.0,
        "atr_1m": 2.0, "atr_5m": 3.0,
    }


def setup_dict(direction: str = "BULLISH") -> dict:
    return {
        "direction": direction,
        "kind": "BREAKOUT_RETEST" if direction == "BULLISH" else "BREAKDOWN_RETEST",
        "trigger": 100.0,
        "invalidation": 95.0 if direction == "BULLISH" else 105.0,
        "confirmed_at": dt().isoformat(),
        "source_level": 99.0 if direction == "BULLISH" else 101.0,
        "source": "TEST_STRUCTURE",
        "price_confidence": 0.8,
    }


def active_position(cfg=None, direction: str = "BULLISH") -> dict:
    cfg = cfg or config()
    start = dt()
    base_candle = candle(start, 100, 101, 99, 100)
    return scanner.create_active_position(
        "test-signal-key", start, setup_dict(direction),
        selected("CE" if direction == "BULLISH" else "PE"),
        risk_plan(direction), base_candle, cfg,
    )


def bullish_oi(**overrides) -> dict:
    result = {
        "raw_label": "BULLISH", "label": "BULLISH", "confidence": 0.8,
        "compared_to_previous_successful_snapshot": True,
        "oi_age_seconds": 15, "persistence_count": 2,
        "transition_status": "DIRECTION_PERSISTENT",
    }
    result.update(overrides)
    return result


def bearish_oi(**overrides) -> dict:
    result = {
        "raw_label": "BEARISH", "label": "BEARISH", "confidence": 0.85,
        "compared_to_previous_successful_snapshot": True,
        "oi_age_seconds": 15, "persistence_count": 2,
        "transition_status": "DIRECTION_PERSISTENT",
    }
    result.update(overrides)
    return result


def bullish_structure(**overrides) -> dict:
    result = {"execution_direction": "BULLISH", "atr_1m": 2.0, "atr_5m": 3.0}
    result.update(overrides)
    return result


def bearish_structure(**overrides) -> dict:
    result = {"execution_direction": "BEARISH", "atr_1m": 2.0, "atr_5m": 3.0}
    result.update(overrides)
    return result


class PositionLifecycleTests(unittest.TestCase):
    def test_same_direction_fresh_signal_does_not_replace_active_contract(self):
        cfg = config()
        active = active_position(cfg)
        # A same-direction setup is not an opposite reversal. The active contract remains CE 23000.
        same_direction_setup = scanner.Setup(
            "BREAKOUT_RETEST", "BULLISH", 104.0, 98.0, dt(10, 1),
            103.0, "NEW_HIGHER_LEVEL", 0.9,
        )
        still_open, events, code, _ = scanner.manage_active_position(
            active, [candle(dt(10, 1), 101, 104, 100, 103)], 103.0, dt(10, 2),
            bullish_oi(), bullish_structure(), same_direction_setup, cfg,
            chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNotNone(still_open)
        self.assertEqual(still_open["instrument_key"], active["instrument_key"])
        self.assertEqual(still_open["strike"], 23000.0)
        self.assertEqual(code, "POSITION_ACTIVE")
        self.assertFalse(events)

    def test_t1_partially_exits_and_keeps_same_strike_for_t2(self):
        cfg = config()
        active = active_position(cfg)
        t1_bar = candle(dt(10, 1), 101, 111, 100.5, 109)
        managed, events, code, detail = scanner.manage_active_position(
            active, [t1_bar], 109.0, dt(10, 2), bullish_oi(),
            bullish_structure(), None, cfg, chain_refresh_ok=True,
            option_quote=None,
        )
        self.assertIsNotNone(managed)
        self.assertTrue(managed["t1_hit"])
        self.assertEqual(managed["remaining_pct"], 50.0)
        self.assertEqual(managed["instrument_key"], active["instrument_key"])
        self.assertEqual(managed["stop_underlying"], 100.0)
        self.assertEqual(code, "POSITION_ACTIVE")
        self.assertEqual(events[0]["event_type"], "TARGET_1_PARTIAL")
        self.assertEqual(detail["t2_underlying"], 120.0)

    def test_t1_runner_is_not_closed_for_temporary_oi_price_misalignment(self):
        cfg = config()
        active = active_position(cfg)
        managed, events, code, _ = scanner.manage_active_position(
            active, [candle(dt(10, 1), 101, 111, 100.5, 109)], 109.0,
            dt(10, 2), bullish_oi(), bullish_structure(execution_direction="MIXED"),
            None, cfg, chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNotNone(managed)
        self.assertEqual(managed["remaining_pct"], 50.0)
        self.assertEqual(managed["continuation_status"], "WAITING_FOR_OI_PRICE_ALIGNMENT")
        self.assertEqual(code, "POSITION_ACTIVE")

    def test_t2_closes_remaining_runner(self):
        cfg = config()
        active = active_position(cfg)
        active["t1_hit"] = True
        active["t1_hit_at"] = dt(10, 1).isoformat()
        active["remaining_pct"] = 50.0
        active["stop_underlying"] = 100.0
        active["last_monitored_candle"] = dt(10, 1).isoformat()
        managed, events, code, detail = scanner.manage_active_position(
            active, [candle(dt(10, 2), 118, 121, 117, 120)], 120.0,
            dt(10, 3), bullish_oi(), bullish_structure(), None, cfg,
            chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "TARGET_2_HIT")
        self.assertEqual(detail["closed_position"]["remaining_pct"], 0.0)
        self.assertEqual(events[-1]["event_type"], "POSITION_EXIT")

    def test_both_t1_and_t2_in_one_candle_record_t1_then_t2(self):
        cfg = config()
        active = active_position(cfg)
        managed, events, code, _ = scanner.manage_active_position(
            active, [candle(dt(10, 1), 101, 121, 100.5, 120)], 120.0,
            dt(10, 2), bullish_oi(), bullish_structure(), None, cfg,
            chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "TARGET_2_HIT")
        self.assertEqual([event["event_type"] for event in events], ["TARGET_1_PARTIAL", "POSITION_EXIT"])

    def test_no_qualified_t2_makes_t1_a_full_exit(self):
        cfg = config()
        active = active_position(cfg)
        active["t2_underlying"] = None
        active["risk_plan"]["t2_underlying"] = None
        managed, events, code, detail = scanner.manage_active_position(
            active, [candle(dt(10, 1), 101, 111, 100.5, 109)], 109.0,
            dt(10, 2), bullish_oi(), bullish_structure(), None, cfg,
            chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "TARGET_1_HIT_NO_T2")
        self.assertEqual(len(events), 1)
        self.assertEqual(events[0]["event_type"], "POSITION_EXIT")
        self.assertEqual(detail["closed_position"]["remaining_pct"], 0.0)

    def test_live_quote_crossing_t1_and_t2_records_both_stages(self):
        cfg = config()
        active = active_position(cfg)
        managed, events, code, detail = scanner.manage_active_position(
            active, [], 121.0, dt(10, 2), bullish_oi(), bullish_structure(), None,
            cfg, chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "TARGET_2_HIT")
        self.assertEqual([event["event_type"] for event in events], ["TARGET_1_PARTIAL", "POSITION_EXIT"])
        self.assertEqual(events[0]["remaining_pct"], 50.0)
        self.assertEqual(detail["closed_position"]["remaining_pct"], 0.0)

    def test_first_candle_gap_from_checkpoint_fails_closed(self):
        cfg = config()
        active = active_position(cfg)
        with self.assertRaises(scanner.ScannerError) as context:
            scanner.manage_active_position(
                active, [candle(dt(10, 2), 100, 101, 99, 100)], 100,
                dt(10, 3), bullish_oi(), bullish_structure(), None, cfg,
                chain_refresh_ok=True, option_quote=None,
            )
        self.assertEqual(context.exception.code, "POSITION_CANDLE_GAP")

    def test_same_candle_stop_and_target_uses_conservative_stop_first(self):
        cfg = config()
        active = active_position(cfg)
        managed, events, code, _ = scanner.manage_active_position(
            active, [candle(dt(10, 1), 100, 112, 89, 105)], 105.0,
            dt(10, 2), bullish_oi(), bullish_structure(), None, cfg,
            chain_refresh_ok=True, option_quote=None,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "STOP_LOSS_HIT")
        self.assertEqual(len(events), 1)
        self.assertFalse(events[0].get("t1_hit"))

    def test_persistent_oi_and_opposite_price_setup_confirms_reversal(self):
        cfg = config()
        active = active_position(cfg)
        reversal_setup = scanner.Setup(
            "BREAKDOWN_RETEST", "BEARISH", 98.0, 102.0, dt(10, 1),
            100.0, "SWING_LOW", 0.82,
        )
        confirmed, evidence = scanner.confirmed_opposite_reversal(
            active, reversal_setup, bearish_oi(), bearish_structure(), 97.0,
            dt(10, 2), cfg, chain_refresh_ok=True,
        )
        self.assertTrue(confirmed)
        self.assertEqual(evidence["reversal_status"], "CONFIRMED")

    def test_oi_only_or_price_only_reversal_does_not_invalidate_position(self):
        cfg = config()
        active = active_position(cfg)
        setup = scanner.Setup("BREAKDOWN_RETEST", "BEARISH", 98, 102, dt(10, 1), 100, "TEST", 0.9)
        oi_only, _ = scanner.confirmed_opposite_reversal(
            active, setup, bearish_oi(), bullish_structure(), 97,
            dt(10, 2), cfg, chain_refresh_ok=True,
        )
        price_only, _ = scanner.confirmed_opposite_reversal(
            active, setup, bullish_oi(), bearish_structure(), 97,
            dt(10, 2), cfg, chain_refresh_ok=True,
        )
        self.assertFalse(oi_only)
        self.assertFalse(price_only)

    def test_first_opposite_oi_snapshot_is_only_reversal_watch(self):
        cfg = config()
        active = active_position(cfg)
        setup = scanner.Setup("BREAKDOWN_RETEST", "BEARISH", 98, 102, dt(10, 1), 100, "TEST", 0.9)
        confirmed, evidence = scanner.confirmed_opposite_reversal(
            active, setup, bearish_oi(persistence_count=1, label="MIXED", transition_status="REVERSAL_WATCH"),
            bearish_structure(), 97, dt(10, 2), cfg, chain_refresh_ok=True,
        )
        self.assertFalse(confirmed)
        self.assertEqual(evidence["reversal_status"], "OI_REVERSAL_NOT_PERSISTENT")

    def test_premium_max_loss_closes_exact_active_contract(self):
        cfg = config()
        active = active_position(cfg)
        q = scanner.OptionQuote(
            instrument_key=active["instrument_key"], timestamp=dt(10, 1),
            ltp=79.0, bid=79.0, ask=79.5, bid_qty=100, ask_qty=100,
            volume=10000, oi=500000, strike=23000, side="CE",
            expiry=date(2026, 11, 3), delta=0.55, gamma=0.001,
            theta=-10, vega=10, iv=14,
        )
        managed, events, code, detail = scanner.manage_active_position(
            active, [], 100.0, dt(10, 1, 5), bullish_oi(), bullish_structure(),
            None, cfg, chain_refresh_ok=True, option_quote=q,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "PREMIUM_MAX_LOSS")
        self.assertEqual(detail["closed_position"]["instrument_key"], active["instrument_key"])

    def test_premium_trailing_protection_applies_after_t1(self):
        cfg = config()
        active = active_position(cfg)
        active.update({"t1_hit": True, "remaining_pct": 50.0,
                       "stop_underlying": 100.0, "peak_premium_bid": 120.0,
                       "last_monitored_candle": dt(10, 0).isoformat()})
        q = scanner.OptionQuote(
            instrument_key=active["instrument_key"], timestamp=dt(10, 1),
            ltp=85.0, bid=85.0, ask=85.5, bid_qty=100, ask_qty=100,
            volume=10000, oi=500000, strike=23000, side="CE",
            expiry=date(2026, 11, 3), delta=0.55, gamma=0.001,
            theta=-10, vega=10, iv=14,
        )
        managed, events, code, detail = scanner.manage_active_position(
            active, [], 115.0, dt(10, 1, 5), bullish_oi(), bullish_structure(),
            None, cfg, chain_refresh_ok=True, option_quote=q,
        )
        self.assertIsNone(managed)
        self.assertEqual(code, "PREMIUM_TRAILING_PROTECTION")

    def test_structural_t2_can_only_tighten_not_extend(self):
        cfg = config()
        active = active_position(cfg)
        active.update({"t1_hit": True, "remaining_pct": 50.0, "stop_underlying": 100.0})
        levels = [
            scanner.PriceLevel(112.0, "RESISTANCE", "SWING_HIGH", 2.0),
            scanner.PriceLevel(125.0, "RESISTANCE", "SESSION_HIGH", 2.0),
        ]
        events = scanner._refresh_active_targets(
            active, bullish_oi(), levels, 109.5, bullish_structure(), cfg,
        )
        self.assertEqual(active["t2_underlying"], 112.0)
        self.assertEqual(events[0]["event_type"], "TARGET_2_TIGHTENED")
        # Existing T2 never moves farther away just because a new distant wall appears.
        distant = [scanner.PriceLevel(140.0, "RESISTANCE", "NEW_SESSION_HIGH", 3.0)]
        no_change = scanner._refresh_active_targets(
            active, bullish_oi(), distant, 109.5, bullish_structure(), cfg,
        )
        self.assertEqual(no_change, [])
        self.assertEqual(active["t2_underlying"], 112.0)

    def test_new_second_barrier_can_add_t2_before_t1(self):
        cfg = config()
        active = active_position(cfg)
        active["t2_underlying"] = None
        active["risk_plan"]["t2_underlying"] = None
        levels = [
            scanner.PriceLevel(125.0, "RESISTANCE", "SWING_HIGH", 2.0),
            scanner.PriceLevel(135.0, "RESISTANCE", "SESSION_HIGH", 2.0),
        ]
        events = scanner._refresh_active_targets(
            active, bullish_oi(), levels, 105.0, bullish_structure(), cfg,
        )
        self.assertEqual(active["t2_underlying"], 125.0)
        self.assertEqual(events[0]["event_type"], "TARGET_2_ADDED")

    def test_t1_and_t2_are_planned_from_nearest_oi_structure_barriers(self):
        cfg = config()
        setup = scanner.Setup("BREAKOUT_RETEST", "BULLISH", 100, 95, dt(), 99, "TEST", 0.8)
        oi = {"oi_levels": [
            {"strike": 115, "call_oi": 100000, "call_relative_oi": 0.8, "call_resistance_flow_strength": 0.7, "call_bullish_flow_strength": 0.0, "call_delta_oi_pct_snapshot": 5.0},
            {"strike": 130, "call_oi": 90000, "call_relative_oi": 0.7, "call_resistance_flow_strength": 0.6, "call_bullish_flow_strength": 0.0, "call_delta_oi_pct_snapshot": 4.0},
            {"strike": 90, "put_oi": 90000, "put_relative_oi": 0.8, "put_support_flow_strength": 0.7, "put_bearish_flow_strength": 0.0, "put_delta_oi_pct_snapshot": 4.0},
        ]}
        levels = [
            scanner.PriceLevel(95.0, "SUPPORT", "SWING_LOW", 2.0),
            scanner.PriceLevel(120.0, "RESISTANCE", "SWING_HIGH", 2.0),
            scanner.PriceLevel(135.0, "RESISTANCE", "SESSION_HIGH", 2.0),
        ]
        oi["oi_levels"][0]["strike"] = 120
        oi["oi_levels"][1]["strike"] = 135
        plan = scanner.choose_oi_targets_and_stop(
            100.0, setup, oi, {"atr_1m": 4.0, "atr_5m": 4.0}, cfg, dt(10), levels,
        )
        self.assertEqual(plan["t1_underlying"], 120.0)
        self.assertEqual(plan["t2_underlying"], 135.0)
        self.assertGreaterEqual(plan["underlying_rr"], 2.0)
        self.assertIn("OI_AND_PRICE_STRUCTURE", {plan["t1_confluence"], plan["t2_confluence"]})

    def test_active_monitoring_rejects_missing_minute_candle_gap(self):
        cfg = config()
        active = active_position(cfg)
        candles = [
            candle(dt(10, 1), 100, 101, 99, 100),
            candle(dt(10, 3), 100, 101, 99, 100),
        ]
        with self.assertRaises(scanner.ScannerError) as context:
            scanner.manage_active_position(
                active, candles, 100, dt(10, 4), bullish_oi(), bullish_structure(),
                None, cfg, chain_refresh_ok=True, option_quote=None,
            )
        self.assertEqual(context.exception.code, "POSITION_CANDLE_GAP")


class StateNotificationAndRecoveryTests(unittest.TestCase):
    def test_notification_queue_deduplicates_entry_and_position_events(self):
        state = {"pending_notifications": [], "delivered_signal_keys": []}
        payload = {"decision": "POSITION_EVENT", "reason_code": "TARGET_1_PARTIAL"}
        self.assertTrue(scanner.queue_notification(state, "event-key", payload, dt()))
        self.assertFalse(scanner.queue_notification(state, "event-key", payload, dt(10, 1)))
        self.assertEqual(len(state["pending_notifications"]), 1)

    def test_html_email_has_event_and_target_evidence_and_json_attachment(self):
        payload = {
            "timestamp": dt().isoformat(), "signal_key": "event-key", "decision": "POSITION_EVENT",
            "reason_code": "TARGET_1_PARTIAL", "event_type": "TARGET_1_PARTIAL",
            "setup_direction": "BULLISH", "position_status": "OPEN", "remaining_pct": 50.0,
            "premium_bid": 120.0, "original_signal_key": "old-signal",
            "selected_contract": selected(),
            "risk_plan": {"entry_underlying": 100, "stop_underlying": 100,
                          "t1_underlying": 110, "t2_underlying": 120,
                          "t1_source": "OI_CE_WALL", "t2_source": "SWING_HIGH",
                          "t1_confluence": "OI_AND_PRICE_STRUCTURE", "t2_confluence": "PRICE_STRUCTURE_ONLY"},
            "position_event_details": {"partial_exit_pct": 50, "continuation_status": "CONFIRMED"},
            "oi": {"raw_label": "BULLISH", "label": "BULLISH", "confidence": 0.8},
            "structure": {"execution_direction": "BULLISH", "regime": "CONTINUOUS_BULLISH"},
        }
        message = scanner.build_trade_email(payload)
        self.assertIn("POSITION EVENT", message["Subject"])
        html_part = next(part for part in message.walk() if part.get_content_subtype() == "html")
        body = html_part.get_content()
        self.assertIn("Position management", body)
        self.assertIn("Target 2 evidence", body)
        attachment = next(part for part in message.iter_attachments() if part.get_content_type() == "application/json")
        decoded = json.loads(attachment.get_content())
        self.assertEqual(decoded["event_type"], "TARGET_1_PARTIAL")

    def test_v106_schema_migration_requires_explicit_position_reconciliation(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "state.json"
            path.write_text(json.dumps({
                "schema_version": 106, "scanner_version": "106.0.0",
                "session_date": "2026-10-30", "seen_signal_keys": [],
                "pending_notifications": [{"signal_key": "old-alert", "payload": {}, "attempts": 0}],
                "delivered_signal_keys": [], "chain_snapshots": [],
            }))
            migrated = scanner.read_state(path)
            self.assertEqual(migrated["schema_version"], 107)
            self.assertTrue(migrated["position_reconciliation_required"])
            self.assertIsNone(migrated["active_position"])
            self.assertEqual(migrated["pending_notifications"][0]["status"], "LEGACY_UNCERTAIN")

    def test_legacy_audit_replays_confirmed_reversal_not_oi_only_watch(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "market_scan_2026-10-30.jsonl"
            base_oi = bearish_oi()
            row_watch = {
                "timestamp": dt(10, 3).isoformat(), "spot": 98.0,
                "option_chain_status": "SUCCESS", "oi": {**base_oi, "label": "MIXED", "persistence_count": 1, "transition_status": "REVERSAL_WATCH"},
                "structure": bearish_structure(),
                "setup": {**setup_dict("BEARISH"), "confirmed_at": dt(10, 2).isoformat(), "trigger": 99.0, "invalidation": 102.0},
            }
            row_confirmed = {
                "timestamp": dt(10, 6).isoformat(), "spot": 97.0,
                "option_chain_status": "SUCCESS", "oi": base_oi,
                "structure": bearish_structure(),
                "setup": {**setup_dict("BEARISH"), "confirmed_at": dt(10, 5).isoformat(), "trigger": 98.0, "invalidation": 102.0},
            }
            path.write_text(json.dumps(row_watch) + "\n" + json.dumps(row_confirmed) + "\n")
            found = scanner._find_confirmed_reversal_in_audit(path, dt(10), "BULLISH", config())
            self.assertIsNotNone(found)
            self.assertEqual(found["timestamp"], dt(10, 6).isoformat())
            self.assertEqual(found["direction"], "BEARISH")

    def test_legacy_position_reconciliation_can_be_flat_or_exact_signal(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "audit").mkdir()
            (root / "state").mkdir()
            cfg = config(root)
            state = {"schema_version": 106, "session_date": "2026-10-30",
                     "chain_snapshots": [], "seen_signal_keys": [], "pending_notifications": [],
                     "delivered_signal_keys": [], "position_history": []}
            old_state = root / "market_state_v106.json"
            old_state.write_text(json.dumps(state))
            audit_record = {
                "timestamp": dt().isoformat(), "session_date": "2026-10-30", "decision": "QUALIFIED",
                "signal_key": "legacy-signal", "spot": 100.0,
                "selected_contract": selected(), "risk_plan": risk_plan(), "setup": setup_dict(),
            }
            (root / "audit" / "market_scan_2026-10-30.jsonl").write_text(json.dumps(audit_record) + "\n")
            result = scanner.reconcile_legacy_position(cfg, "legacy-signal")
            self.assertEqual(result["reconciled"], "ACTIVE")
            self.assertEqual(result["strike"], 23000.0)
            persisted = scanner.read_state(cfg.state_file)
            self.assertFalse(persisted["position_reconciliation_required"])
            self.assertEqual(persisted["active_position"]["signal_key"], "legacy-signal")

    def test_flat_reconciliation_clears_legacy_position_lock(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            root.mkdir(exist_ok=True)
            cfg = config(root)
            (root / "market_state_v106.json").write_text(json.dumps({
                "schema_version": 106, "session_date": "2026-10-30", "chain_snapshots": [],
                "seen_signal_keys": [], "pending_notifications": [], "delivered_signal_keys": [],
            }))
            result = scanner.reconcile_legacy_position(cfg, "flat")
            self.assertEqual(result["reconciled"], "FLAT")
            persisted = scanner.read_state(cfg.state_file)
            self.assertFalse(persisted["position_reconciliation_required"])
            self.assertIsNone(persisted["active_position"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
