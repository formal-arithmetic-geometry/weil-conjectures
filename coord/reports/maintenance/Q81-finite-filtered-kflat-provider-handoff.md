# Q81 maintenance: lem-kun-finite-filtered-kflat-replacement

Project: `/home/ubuntu/weil-newtargets`, stage 1. Date: 2026-10-17.
Dispatcher key: `lem-kun-finite-filtered-kflat-replacement@`.

## Cause

The repeated blank `NOANSWER` results were provider transport failures. All
eight completed runs from `1792196115` through `1792196953` ended with
`ERROR: exceeded retry limit, last status: 429 Too Many Requests`. Two retries
failed before doing any item work. The dispatcher read only the missing
`last.txt`, discarded the terminal diagnostic, and launched another worker
within seconds. After author run `1792193487` returned READY, the interrupted
second reader was incorrectly replaced by an author/repair worker. This lost
the review handoff and repeated already completed work.

The returned B3 repair was already present in the sandbox: the two surplus
statement dependencies `lem-kun-filtered-tensor-graded-comparison` and
`lem-sp-finite-filtration-induction` had been removed. The retained statement,
eight proof steps, proof dependencies and 17 citation quotes were not the cause
of the provider failures. Maintenance did not perform their mathematical review.

A separate full dry run during diagnosis exposed a moving Git baseline: it
reported unrelated NG files as Q81 changes and said HEAD was not on top of
`origin/newtargets-dag`. Concurrent Q130 maintenance fixed that race by passing
an immutable base commit to preflight. The original author's log had shown the
same intermittent error between successful dry runs.

The observed rate limit does not establish a provider/account limit or prove
that the configured 700-slot ceiling caused the incident. This session did not
change global concurrency, models, failure counters, dispatcher state or claims.

## Repair

Installed an item-specific handoff at:

- Launcher: `/home/ubuntu/weil-launcher-nt/route-notes/lem-kun-finite-filtered-kflat-replacement.md`.
- Server source: `/home/ubuntu/weil-newtargets/tools/launcher/route-notes/lem-kun-finite-filtered-kflat-replacement.md`.
- Server diagnosis: `/home/ubuntu/weil-newtargets/coord/reports/maintenance/Q81-finite-filtered-kflat-provider-handoff.md`.

The existing dispatcher reads this route note on subsequent author/repair
launches. It tells a fresh worker to resume the independent second reading,
inspect the current sources and citations, write its own review, and use the
normal delivery tool. It neither approves the mathematics nor bypasses review.
No sandbox node, proof, citation or report was edited by this maintenance.

Concurrent maintenance repaired the shared failure mechanisms while this
investigation was in progress. Those fixes were reused, not overwritten:

| Server commit | Relevant fix |
| --- | --- |
| `a1a68055f2b73fe62674754cb95071667bd798ac` | NK: CLI supervisor retains diagnostics, resumes known sessions, and retries transient 429s with bounded jitter. Deployed through `/home/ubuntu/.local/bin/codex` to `/home/ubuntu/weil-launcher-all/codex_retry.py`; new executions from the existing dispatcher use it. |
| `6fb280508f` | Q53: persist the author-to-second-reader handoff and retain exited worker records until reaping. |
| `0abb765411` | NC: retain interrupted second-reader reports within the same delivery round. |
| `783eefd22616654c6d85f4f5f7d107772caa9533` | Q130: preserve stage-1 metadata ownership and pin the preflight baseline. |

Source changes to the long-running dispatcher take effect on its next normal
start. The CLI supervisor already applies to new worker executions without a
dispatcher restart. No process belonging to another session was stopped.

The server handoff and diagnosis are committed with the requested Bin Wu
identity under `SHEAF_LEAD=L-only flock coord/.merge.lock`. Exact task paths
only are staged and committed. Existing unrelated server changes are preserved.
The task commit is `3583354586b3b4cf243e3d328108127334ad54bd`.
The local handoff has adjacent `.maint-Q81-1792196921-final.bak` and the server
handoff/diagnosis have adjacent `.maint-Q81-1792196921.bak` snapshots. Drafts of
this report are retained before revisions.

## Validation and current state

- The current author run `1792197037` passed server `check_dag` and
  `review_split` (PASS, zero new nodes), then the full delivery preflight at
  `b29b1ddc75`. It returned `READY lem-kun-finite-filtered-kflat-replacement:
  0 new nodes, 0 Mathlib leaves`.
- The dispatcher advanced the item to the actual stage-1 second-reader run
  `1792198057`, PID 3231562, rather than another author. Its prompt is the
  second-reader brief. Its adjacent `codex-retry.json` and
  `[codex-admission]` lines confirm the installed recovery path. At inspection
  it was waiting for provider capacity while existing children drain naturally.
- The supervisor's fake-CLI regression suite passed: 11 tests, no model calls.
  The dedicated reader-retry, durable stage-1 handoff and failure-classification
  suites passed together: 21 tests, no SSH, Lean builds or model calls.
- The overlapping transport suite initially had two test-fixture errors during
  concurrent integration. After its owner updated the fixture, all eight tests
  in `test_worker_transport.py` passed. This session did not replace shared
  dispatcher/test sources while other maintenance was integrating them.
- `evidence/attempts.json`, `evidence/state-before.json` and
  `evidence/sandbox-inputs.json` retain the diagnosis inputs.
- The independent maintenance dry run with the pinned baseline passed:
  `OK (not pushed) deliver/Q81/lem-kun-finite-filtered-kflat-replacement at
  1f8b0d56cd: preflight passed`. Nothing was pushed by maintenance. The next
  reader still performs the required independent review and delivery.

No Lean files changed, no compiler was required, and no `lake build` was run.
Provider recovery cannot guarantee service availability. The official
[OpenAI rate-limit guidance](https://developers.openai.com/api/docs/guides/rate-limits)
supports jittered exponential retries; local logs establish this incident's
cause.

## Next worker

Continue the retained Q81 sandbox and the second-reader workflow. Read the
installed item handoff and `/home/ubuntu/weil-launcher-nt/check-brief.md`.
Check whether a delivery has appeared or merged before publishing another one.
Review the eight steps and every cited statement, append your own
`## Second reading by Q81`, then dry-run and deliver normally. Keep the two
surplus statement dependencies removed. Capacity waits and a 429 are tool
conditions, not a reason to change the theorem or abandon the item. Historical
failure counts remain counts and never disable dispatch.
