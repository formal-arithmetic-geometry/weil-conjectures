# Maintenance report: Sheaf.Paper.FiniteDiscreteCoefficientSections

## Cause

The ten counted failures were launcher failures, not Lean proof failures. The
runs under `/home/ubuntu/weil-launcher-all/run/R3/` ended with no answer after
the Codex provider returned `ERROR: exceeded retry limit, last status: 429 Too
Many Requests`. The same burst affected many unrelated groups at
08:25:03–08:25:34 on 2026-10-17. `dispatch_all.py` launched the Codex binary
without a temporary-rate-limit supervisor; when the stream ended before
`last.txt` was written, it recorded `NOANSWER` and immediately retried the
item. Thus this item was repeatedly re-dispatched into the same provider
outage. The retained Lean sandbox and the server return are a separate stale
post-upstream-sync proof repair; they were never reached reliably by these ten
attempts.

## Changes

Installed the existing tested retry supervisor from the launcher maintenance
work under `/home/ubuntu/weil-launcher-all/codex_retry.py`, and changed
`/home/ubuntu/.local/bin/codex` to point to it. The supervisor passes through
ordinary Codex calls, but for dispatcher invocations that write a run's
`last.txt` it retries temporary HTTP 429 failures with exponential jitter,
resumes an interrupted session when a session id was received, preserves the
worker budget, and writes a diagnostic `BLOCKED` result after exhaustion. The
original package binary remains available at
`/home/ubuntu/.codex/packages/standalone/current/bin/codex`; the old launcher
link is saved as
`/home/ubuntu/.local/bin/codex.bak-maint-R3-FiniteDiscreteCoefficientSections`.
The supervisor's 11 regression tests pass.

No Lean source, DAG record, or mathematical statement was changed. The server
recorded this report so the next worker can distinguish provider outages from
the pending source-sync repair.

## Validation

- All ten item run logs show the same terminal provider 429 diagnostic (or an
  empty answer immediately after that diagnostic).
- A large cross-project wave logged `NOANSWER` at the same timestamp, confirming
  the failure was systemic.
- `python3 -m unittest discover -s /home/ubuntu/weil-launcher-all/maint/NK-lem-coef-mapping-simplex-final-edge-1792196275 -p test_codex_retry.py`
  passes: 11 tests.
- `/home/ubuntu/.local/bin/codex --version` still reports `codex-cli 0.162.1`.

## Next worker

After the provider recovers, continue the existing repair in
`/home/ubuntu/weil-sandbox/R3/Sheaf.Paper.FiniteDiscreteCoefficientSections`.
Rebase the retained proof against the current `sheaf-dag`; preserve the
original theorem signature (do not keep the experimental extra `f` hypothesis),
compile the module alone with the prescribed 60-second tool, and run the normal
stage-3 delivery dry run. The current server return is the upstream-sync
return at head `0265ae580`; it does not describe the provider failure.
