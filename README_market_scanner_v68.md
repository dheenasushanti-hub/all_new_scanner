# NIFTY Scanner V68 — Repository Audit Fix

## Why V68

The connected repository's recent Actions runs completed cleanly but showed no confirmed directional setup. Review of the committed state JSON found a legacy `active_trade` with status `ACTIVE` while V67's `recommendation_trackers` list was empty. V67 imported the singular `recommendation_tracker`, but not the older `active_trade` format, so that legacy virtual recommendation was not monitored by the current stop/reversal tracker.

V65 historical runs also confirm that the previous code sent `PREDICTIVE_WATCH` emails with `signal_ready=false`; V67 now suppresses those events and keeps the failure-only email allowlist.

## Changes

- Adds V68 as a new versioned scanner file; leaves `market_scanner.py` (V67) untouched for rollback.
- Migrates only a same-session, structurally valid legacy virtual recommendation into one V68 tracker.
- Marks/deduplicates migration so repeated scans cannot create duplicate trackers.
- Resets the intrabar baseline to the last run; it does not invent historical SL/target events beyond the hard 15-minute OHLC lookback. That limitation is persisted in state and written to logs.
- Normalizes legacy timestamps ending in literal `IST` before pandas parsing.
- Preserves the V67 email allowlist: only `SIGNAL_READY`, `MARKET_REVERSAL_CONFIRMED`, `INITIAL_STOP_LOSS_REACHED`, and `TRAILING_STOP_REACHED` can be emailed. Watch/target/quote/stagnation events remain internal.
- Updates the existing Cloudflare-dispatched workflow to run `market_scanner_v68.py`, while keeping the workflow path, `workflow_dispatch` trigger, secrets, and JSON state path unchanged.
- Upgrades `actions/checkout` and `actions/setup-python` to v7, which removes the Node 20 deprecation warnings seen in current logs.
- Adds a separate push/PR regression workflow, so unit tests do not run every three-minute production scan.

## Testing

Offline validation completed: Python compilation passed; the existing full local regression suite passed 39/39 tests; the focused repository CI suite passed 7/7 tests; CLI `--help` startup passed. The focused suite tests legacy migration/idempotency, invalid geometry fail-closed behavior, legacy IST parsing, structural entry gating, and strict email suppression.

Live Upstox API behavior and SMTP delivery were not tested. The scanner remains virtual-only and does not place broker orders.

## Deployment

The PR updates `.github/workflows/market-scanner.yml` to run `python market_scanner_v68.py`. Cloudflare should continue targeting the exact same workflow filename; no Worker schedule change is needed. Production `main` remains on V67 until the PR is merged.
