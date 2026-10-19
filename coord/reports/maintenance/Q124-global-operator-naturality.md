# Q124 maintenance: lem-trf-global-operator-naturality

## Cause

The repeated failures were model-provider failures. Fourteen archived worker
runs from `1792192931` through `1792196895` end with
`ERROR: exceeded retry limit, last status: 429 Too Many Requests` from the
configured gateway (`https://the project server`, provider `OpenAI`). Several
failed before doing any work. The previous maintenance attempt also ended in
429. No `last.txt` was written, so the dispatcher reduced these diagnostics to
`NOANSWER:` and started another author session. See `evidence/attempts.json`.

The configured worker ceiling was 700. Its contribution to gateway saturation
is plausible, but the gateway's actual quota is not available here. The
concrete verified cause is the terminal HTTP 429, not a theorem failure,
permission denial, Lean error, or a returned delivery. The server had no Q124
return entry or landing record for this item.

The retry brief compounded the interruption: step 1 said to copy the original
node again, and the dispatcher said to "complete or redo" the retained work.
Retries repeatedly reread sources and reran searches despite a prepared packet.
One historical citation failure was real: the admissibility statement changed
after an earlier dry run. The current quotes pass the delivery citation check.

## Changes

Server commit **86f2f1262534213d6eb189aa066f497469fba1fa**, made on
`/home/ubuntu/weil-newtargets` under `SHEAF_LEAD=L-only flock coord/.merge.lock`
with the requested author:

- `tools/launcher/dispatch_all.py`: the retained-sandbox prompt now says to keep
  the work, check current sources, start with the required dry run, and follow
  the current role's answer protocol. Only this prompt hunk was staged; other
  maintainers' concurrent dispatcher edits were excluded.
- `tools/launcher/stage1-worker-brief.md`: archived corrected worker brief.
  Its active installation is `/home/ubuntu/weil-launcher-nt/worker-brief.md`,
  reached through `weil-launcher-all/briefs/batch2/stage1-worker.md`. It copies
  the original node only for an empty sandbox and reuses verified search logs.
- `tools/launcher/route-notes/lem-trf-global-operator-naturality.md`: installed
  at the matching active launcher path; records the transport diagnosis,
  packet contents, dry-run command, and independent-reader requirement.

Local and server `test_dispatch_reader_retry.py` fixture adjustments supply
the admission and durable-handoff interfaces introduced by concurrent maintenance. Existing
reader retry, failure-classification, and handoff tests pass together.

Adjacent `.bak` files preserve every preexisting file changed here:
`dispatch_all.py.maint-Q124-rate-limit.bak`,
`dispatch_all.py.maint-Q124-resume-first.bak`,
`worker-brief.md.maint-Q124-resume-first.bak`, and
`test_dispatch_reader_retry.py.maint-Q124-capacity-mock.bak`. The server's
dispatcher backup uses `.maint-Q124-resume-first.bak`. New route/brief/report
files had no prior contents to back up.

Other maintenance sessions concurrently installed shared provider recovery;
these are not changes authored by this maintenance run. Server commit
**a1a68055f2** installs `tools/launcher/codex_retry.py` and tests. The active
`/home/ubuntu/.local/bin/codex` now points at that supervisor. It retries
temporary provider failures with jitter, resumes the exact session, retains
the sandbox, and keeps the original worker budget. Other shared changes
preserve reader handoffs and durable dry-run receipts. I avoided duplicating
their implementation. The dispatcher prompt source is updated on disk; its
already-running process was not signalled or killed. The active brief and
route note are read for subsequent workers without requiring a restart.

No DAG statement, proof, Lean file, dispatcher state, claim, failure count, or
existing worker output was changed by this maintenance run. No agents were
started and no unrelated process was killed.

## Validation and current status

- Local citation check: all five quotes match current dependency statements.
- Active author run `1792196979`: current server preflight passed at
  **90ea0d11b6**; it returned `READY ...: 0 new nodes, 0 Mathlib leaves`.
- Independent maintenance dry run, using the standard `deliver.py --no-push`:
  server preflight passed at **6578faf2fc**, exit 0. It waited normally for the
  existing delivery lock, worktree capacity, and shared fetch. No push was made.
- The dispatcher then started independent second reader `1792197587`
  (`kind: check`). The maintenance task does not certify or replace that review.
- Existing local classifier/reader/handoff regression suites: **21 tests pass**.
  Installed shared supervisor suite: **14 tests pass**.
- Python syntax checks pass for the edited dispatcher and test fixture.
- No Lean compilation or Lake build was necessary.

## Next worker

Preserve `/home/ubuntu/weil-newtargets-sandbox/Q124/lem-trf-global-operator-naturality`.
It contains the three-step split, report, citations, and actual search log.
Start with the required dry run; update any citation that drifted against the
current server snapshot. Reuse completed searches after reading their results.
An author returns READY after validation; a fresh second reader completes its
independent review and delivers. A 429 is an infrastructure interruption and
does not invalidate the mathematics. Failure counts must remain diagnostic
and must never disable dispatch of this item.
