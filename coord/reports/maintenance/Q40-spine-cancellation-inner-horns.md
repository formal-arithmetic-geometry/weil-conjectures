# Q40 maintenance: spine cancellation and inner horns

Item: `lem-coef-spine-cancellation-inner-horns`, stage 1,
dispatcher key `lem-coef-spine-cancellation-inner-horns@new`.

## Cause

All ten completed failed worker attempts ended with a fatal provider HTTP 429
and no final-answer file. The first failed attempt was the second reader
(`1792195899`); the nine subsequent attempts were authors. See the adjacent
`Q40-spine-cancellation-inner-horns-evidence.json` for exact runs and request
IDs. `NOANSWER:` described the missing output, but hid the service failure.

The initial author (`1792194644`) had completed its split, passed server
preflight at `262e3ab8ed`, and answered `READY`. The dispatcher correctly
started a reader, but after that reader's HTTP 429 it restarted an author,
removing `.check` and losing the pending review phase. This caused unnecessary
revalidation and fresh sessions. Repeated immediate dispatch during provider
congestion amplified the problem; failure count is not evidence of a false
statement and remains no reason to stop dispatching.

There is no return entry or landing attempt for this item in
`coord/returns/Q40.md`, `coord/deliveries.log`, or the searched `~/cc1/*.log`.
The live node is still unsplit because its delivery has not completed. The
retained author sandbox has a split and required citation/search evidence.
Author run `1792197005` passed a fresh server preflight at `b186596770` while
this investigation was running. These facts identify an execution and handoff
failure; this maintenance did not undertake a mathematical review.

## Repair and deployment

Concurrent maintenance fixed the shared mechanism while this investigation
was running. Reuse those fixes rather than overwrite the shared dispatcher:

- `6fb280508f56f3ab9401bdc8651a572b0e6bee43`: Q53's transport classification,
  bounded retry within the same role, and persistent reader handoff.
- `a1a68055f2`: NK's provider retry supervisor and regression tests. The live
  entry point `/home/ubuntu/.local/bin/codex` now points to
  `/home/ubuntu/weil-launcher-all/codex_retry.py`, preserving the original
  package binary. Its original symlink backup is
  `/home/ubuntu/.local/bin/codex.maint-NK-1792196275.bak`.

The supervisor retries temporary provider errors with jitter inside the
original deadline, resumes the exact session, preserves the sandbox, and
writes an explicit `BLOCKED` diagnostic if recovery is exhausted. It applies
to newly launched workers without restarting the current dispatcher. Source
changes to the dispatcher itself apply at its next normal start. Current
workers were not stopped or modified by this maintenance.

This Q40 maintenance installs the item-specific continuation brief at
`tools/launcher/route-notes/lem-coef-spine-cancellation-inner-horns.md` and its
active copy at
`/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-spine-cancellation-inner-horns.md`.
The running dispatcher's existing route-note hook reads it for subsequent
author/repair attempts. It records the accepted split and the real failure,
and keeps author and independent reader duties explicit. The adjacent
evidence file preserves run diagnostics and observed sandbox hashes.

New files have `.bak` snapshots; an existing file is backed up before any
replacement. The server installation and exact-path commit use
`SHEAF_LEAD=L-only flock coord/.merge.lock` and the requested Bin Wu identity.
Only this maintenance's three new files are staged and committed.

## Verification and next worker

The committed server versions passed 11 supervisor tests, 8 worker transport
tests, and 6 failure-classification tests (25 total). Tests use fake child
processes and do not contact the provider or compile Lean. The first local
supervisor discovery invocation failed only its subprocess fixture's import
because it was run from a different working directory; the documented direct
server invocation and rerun in the test directory passed all 11.

Continue the retained sandbox. Read the route note, the author report, node,
citations, and actual search evidence. Validate against current DAG/source
state. An author answers `READY` after a successful dry run; its fresh reader
completes independent reading, dry run, and delivery. Do not infer independent
approval from a maintenance report or from a dry-run commit. If HTTP 429
persists, retain work and report it accurately. Do not reset failure counts,
retire this item, or change its mathematics to address a provider error.

No Lean source, node, unit, claim, return, dispatcher state, or existing worker
sandbox file was changed here. No compiler, Lake build, or process kill was
run. The local `REPORT.md` records this maintenance's resulting commit and
the latest observed worker status.
