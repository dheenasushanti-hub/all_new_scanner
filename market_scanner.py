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
    ce = select_directional_option(chain, "BULLISH", 74100.0)
    pe = select_directional_option(chain, "BEARISH", 74100.0)
    assert ce.option_type == "CE"
    assert pe.option_type == "PE"
    assert ce.strike in {74000.0, 74050.0, 74100.0}
    assert pe.strike in {74100.0, 74150.0, 74200.0}

    # Active expiry discovery regression.
    original_api_get = api_get
    original_now_ist = now_ist
    def _fake_expiry_api_get(url: str, params: Optional[dict[str, Any]] = None, retries: int = 3) -> dict[str, Any]:
        assert url == OPTION_CONTRACT_URL
        return {"status": "success", "data": [
            {"expiry": "2026-10-01"},
            {"expiry": "2026-10-06"},
            {"expiry": "2026-10-13"},
        ]}
    def _fake_now_ist() -> datetime:
        return datetime(2026, 10, 5, 10, 0, tzinfo=IST)
    try:
        globals()["api_get"] = _fake_expiry_api_get
        globals()["now_ist"] = _fake_now_ist
        assert _nearest_active_option_expiry() == "2026-10-06"
    finally:
        globals()["api_get"] = original_api_get
        globals()["now_ist"] = original_now_ist

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
            "reversal_confirmations": 0,
            "last_market_direction": signal.direction,
            "last_market_confidence": signal.confidence,
            "last_ltp": signal.entry,
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
