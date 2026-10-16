"""Focused CI checks for V68 migration, structure gating, and email policy."""
from __future__ import annotations

import json
import tempfile
import unittest
from datetime import date
from pathlib import Path

import market_scanner_v68 as scanner


class V68CriticalPolicyTests(unittest.TestCase):
    def test_legacy_active_trade_migrates_once_with_forward_only_baseline(self):
        today = date(2026, 10, 16)
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "state.json"
            path.write_text(json.dumps({
                "session_date": today.isoformat(),
                "schema_version": 30,
                "last_run_timestamp": "2026-10-16T13:37:00+05:30",
                "last_scan_timestamp": "2026-10-16T13:37:00+05:30",
                "active_trade": {
                    "status": "ACTIVE", "direction": "BULLISH", "instrument_key": "NSE_FO|47167",
                    "trading_symbol": "NSE_FO|47167", "option_type": "CE", "strike": 23100,
                    "entry": 126.3, "entry_underlying": 23132.7,
                    "underlying_stop": 23087.5, "underlying_target_1": 23200,
                    "underlying_target_2": 23250,
                },
                "last_signal": {
                    "timestamp": "2026-10-16 10:22:19 IST", "direction": "BULLISH",
                    "instrument_key": "NSE_FO|47167", "option_type": "CE", "strike": 23100,
                    "entry": 126.3, "entry_underlying": 23132.7,
                    "underlying_stop": 23087.5, "underlying_target_1": 23200,
                    "underlying_target_2": 23250,
                },
                "recommendation_trackers": [], "recommendation_tracker": None,
                "chain_snapshots": [], "alert_outbox": [], "alert_dedupe": {},
            }), encoding="utf-8")
            store = scanner.StateStore(path)
            state = store.load(today)
            trackers = [t for t in state["recommendation_trackers"] if t.get("legacy_state_migration")]
            self.assertEqual(len(trackers), 1)
            tracker = trackers[0]
            self.assertEqual(tracker["status"], "TRACKING")
            self.assertEqual(tracker["target_1"], 23200.0)
            self.assertEqual(tracker["stop_loss"], 23087.5)
            self.assertEqual(tracker["last_intrabar_bar_timestamp"], "2026-10-16T13:37:00+05:30")
            self.assertTrue(tracker["migration_baseline_reset_at"])
            self.assertIn("Historical crossings", tracker["migration_note"])
            self.assertEqual(state["alert_outbox"], [], "Migration must not invent a selection or failure email")
            self.assertEqual(state["schema_version"], 68)
            store.save()
            reloaded = scanner.StateStore(path).load(today)
            self.assertEqual(len([t for t in reloaded["recommendation_trackers"] if t.get("legacy_state_migration")]), 1)

    def test_invalid_legacy_stop_target_geometry_is_not_migrated(self):
        today = date(2026, 10, 16)
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "state.json"
            path.write_text(json.dumps({
                "session_date": today.isoformat(),
                "active_trade": {
                    "status": "ACTIVE", "direction": "BULLISH", "instrument_key": "NSE_FO|1",
                    "option_type": "CE", "strike": 23100, "entry": 100,
                    "entry_underlying": 23132, "underlying_stop": 23150,
                    "underlying_target_1": 23200,
                },
                "last_signal": {"timestamp": "2026-10-16 10:22:19 IST", "direction": "BULLISH"},
                "recommendation_trackers": [], "alert_outbox": [], "alert_dedupe": {},
            }), encoding="utf-8")
            state = scanner.StateStore(path).load(today)
            self.assertEqual(state["recommendation_trackers"], [])
            self.assertEqual(state["active_trade"]["v68_tracker_migration_status"], "SKIPPED_INVALID_LEGACY_LEVELS")
            self.assertEqual(state["alert_outbox"], [])

    def test_literal_ist_timestamp_is_normalized_to_ist(self):
        parsed = scanner.parse_timestamp("2026-10-16 10:22:19 IST")
        self.assertIsNotNone(parsed)
        self.assertEqual(parsed.tzinfo, scanner.IST)
        self.assertEqual((parsed.hour, parsed.minute, parsed.second), (10, 22, 19))

    def test_generic_continuation_cannot_route_strike_without_wall_trigger(self):
        ind = scanner.IndicatorSet(
            spot=23120, vwap=23100, vwap_slope=1, stddev=20,
            upper_1sd=23120, lower_1sd=23080, upper_2sd=23140, lower_2sd=23060,
            atr=20, adx=28, plus_di=23, minus_di=11, rsi=58,
            momentum_3m_pct=0.001, recent_range=30, prior_range=35, compressed=False,
            swing_low=23090, swing_high=23130, previous_close=23080, session_open=23100,
            candles_count=45, indicators_seeded=True, volume_source="TEST",
            momentum_1m_pct=0.0005, swing_low_5m=23070, swing_high_5m=23140,
            session_high=23150, session_low=23060,
        )
        oi = scanner.OIAnalysis(
            rows={}, call_total=1000, put_total=1000, pcr=1.0, pcr_previous=1.0,
            pcr_spiking=False, call_coi_pct=-0.003, put_coi_pct=0.001,
            session_call_coi_pct=float("nan"), session_put_coi_pct=float("nan"),
            tactical_source="3M", tactical_available=True, tactical_age_minutes=3,
            pin_market_veto=False, pin_strikes=[], both_sides_building=False,
            call_unwind_dominates=True, put_unwind_dominates=False,
            walls_resistance=[], walls_support=[], baseline_quality="VALID", reasons=[],
        )
        scenario = scanner.Scenario("BULLISH_CONTINUATION", "BULLISH", 80,
                                    "trend only", 23150, "STABLE", True, None, {})
        ok, reason = scanner.selection_trigger_confirmation(
            scenario, ind, oi, scanner.Config(token="test"), future_regime="LONG_BUILDUP"
        )
        self.assertFalse(ok)
        self.assertIn("NO_CONFIRMED_SUPPORT_RESISTANCE_INTERACTION", reason)

    def test_watch_events_are_never_queued_as_email(self):
        state = {"alert_outbox": [], "alert_dedupe": {}}
        alert = scanner.enqueue_email_alert(
            state, now=scanner.parse_timestamp("2026-10-16T12:00:00+05:30"),
            event_type="PREDICTIVE_WATCH", dedupe_key="test-watch",
            subject="watch", payload={"strike": 23100},
        )
        self.assertIsNone(alert)
        self.assertEqual(state["alert_outbox"], [])

    def test_only_selection_and_confirmed_failure_event_types_are_allowed(self):
        self.assertEqual(scanner.EMAIL_ALLOWED_EVENT_TYPES, frozenset({
            "SIGNAL_READY", "MARKET_REVERSAL_CONFIRMED",
            "INITIAL_STOP_LOSS_REACHED", "TRAILING_STOP_REACHED",
        }))

    def test_legacy_pending_watch_alerts_are_suppressed(self):
        state = {"alert_outbox": [{"event_id": "old", "event_type": "PREDICTIVE_WATCH",
                                   "status": "PENDING", "payload": {}}]}
        config = scanner.Config(token="test", email_sender="", email_password="", email_receiver="")
        delivery = scanner.deliver_email_outbox(
            state, config, scanner.parse_timestamp("2026-10-16T12:00:00+05:30")
        )
        self.assertEqual(delivery["status"], "IDLE")
        self.assertEqual(state["alert_outbox"][0]["status"], "SUPPRESSED_POLICY")


if __name__ == "__main__":
    unittest.main()
