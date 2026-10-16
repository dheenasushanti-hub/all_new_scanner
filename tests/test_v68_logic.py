import unittest
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import pandas as pd

import market_scanner as scanner


IST = ZoneInfo("Asia/Kolkata")


def make_indicators(**overrides):
    values = dict(
        spot=97.5, vwap=98.5, vwap_slope=-0.3, stddev=3.0,
        upper_1sd=101.5, lower_1sd=95.5, upper_2sd=104.5, lower_2sd=92.5,
        atr=5.0, adx=27.0, plus_di=10.0, minus_di=30.0, rsi=40.0,
        momentum_3m_pct=-0.0020, recent_range=5.0, prior_range=5.0,
        compressed=False, swing_low=96.0, swing_high=102.0,
        previous_close=101.0, session_open=101.0, candles_count=20,
        indicators_seeded=True, volume_source="TEST", momentum_1m_pct=-0.0010,
        swing_low_5m=95.0, swing_high_5m=104.0, session_high=104.0, session_low=95.0,
    )
    values.update(overrides)
    return scanner.IndicatorSet(**values)


def make_oi(**overrides):
    values = dict(
        rows={}, call_total=1000.0, put_total=1200.0, pcr=1.2, pcr_previous=1.1,
        pcr_spiking=False, call_coi_pct=-0.0030, put_coi_pct=-0.0030,
        session_call_coi_pct=0.0, session_put_coi_pct=0.0,
        tactical_source="3M", tactical_available=True, tactical_age_minutes=1.0,
        pin_market_veto=False, pin_strikes=[], both_sides_building=False,
        call_unwind_dominates=False, put_unwind_dominates=False,
        walls_resistance=[], walls_support=[], baseline_quality="VALID",
        reasons=[], call_coi_acceleration_pct=float("nan"),
        put_coi_acceleration_pct=float("nan"), acceleration_available=False,
    )
    values.update(overrides)
    return scanner.OIAnalysis(**values)


def make_downside_bars(now):
    # Six completed 1m bars; latest close decisively breaks the prior local low.
    opens  = [100.5, 100.5, 100.1, 100.0, 99.8, 98.5]
    highs  = [101.5, 101.3, 101.0, 100.8, 100.2, 98.8]
    lows   = [99.8, 99.5, 99.5, 99.2, 99.0, 97.2]
    closes = [101.0, 100.5, 100.0, 99.8, 99.5, 97.5]
    times = [now - timedelta(minutes=6-i) for i in range(6)]
    return pd.DataFrame({
        "timestamp": [t.astimezone(ZoneInfo("UTC")).isoformat() for t in times],
        "open": opens, "high": highs, "low": lows, "close": closes, "volume": [100]*6,
    })


class V68IntegrationTests(unittest.TestCase):
    def test_completed_candle_downside_break_promotes_bearish_route(self):
        now = datetime(2026, 10, 16, 14, 6, tzinfo=IST)
        oi = make_oi()
        indicators = make_indicators()
        candidate = scanner.detect_price_structure_candidate(
            make_downside_bars(now), indicators, oi, now, "UNKNOWN", scanner.Config()
        )
        self.assertIsNotNone(candidate)
        self.assertEqual(candidate.state, "CONFIRMED_BEARISH_CONTINUATION")
        ok, reason = scanner.selection_trigger_confirmation(candidate, indicators, oi, scanner.Config(), "UNKNOWN")
        self.assertTrue(ok, reason)
        self.assertEqual(reason, "CONFIRMED_PRICE_STRUCTURE_CONTINUATION")

    def test_price_led_oi_unwind_is_neutral_not_mislabelled_as_bearish_confirmation(self):
        score = scanner._coi_score("BEARISH", make_oi(), scanner.Config(),
                                   scenario_state="CONFIRMED_BEARISH_CONTINUATION")
        self.assertAlmostEqual(score, 0.5)

    def test_low_adx_two_sided_oi_build_keeps_sideways_veto(self):
        indicators = make_indicators(adx=18.0)
        oi = make_oi(both_sides_building=True)
        primary = scanner.Scenario("WATCH_NO_CONFIRMED_SETUP", "NEUTRAL", 0.0, "watch", None, "", False, None, {})
        resolved = scanner.resolve_v68_direction(primary, None, None, indicators, oi, "UNKNOWN")
        self.assertEqual(resolved.state, "SIDEWAYS_CHOP")
        self.assertEqual(resolved.direction, "NEUTRAL")
        self.assertEqual(resolved.hard_veto, "SIDEWAYS_ADX_DUAL_SIDE_OI_BUILD")

    def test_reversal_watch_alone_does_not_authorize_a_strike(self):
        indicators = make_indicators()
        oi = make_oi()
        primary = scanner.Scenario("WATCH_NO_CONFIRMED_SETUP", "NEUTRAL", 0.0, "watch", None, "", False, None, {})
        reversal = scanner.Scenario("BEARISH_REVERSAL_WATCH", "BEARISH", 65.0, "watch only", None, "", False, None, {})
        resolved = scanner.resolve_v68_direction(primary, None, reversal, indicators, oi, "UNKNOWN")
        self.assertEqual(resolved.state, "DIRECTIONAL_REVERSAL_WATCH")
        self.assertEqual(resolved.direction, "NEUTRAL")
        ok, reason = scanner.selection_trigger_confirmation(resolved, indicators, oi, scanner.Config(), "UNKNOWN")
        self.assertFalse(ok)
        self.assertEqual(reason, "NO_DIRECTIONAL_SETUP")


if __name__ == "__main__":
    unittest.main(verbosity=2)
