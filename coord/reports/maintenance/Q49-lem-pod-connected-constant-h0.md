# Q49 maintenance: lem-pod-connected-constant-h0

Date: 2026-10-17. Project: `/home/ubuntu/weil-newtargets`, stage 1,
dispatcher key `lem-pod-connected-constant-h0@new`.

## Cause

The repeated failures were terminal model-provider HTTP 429 responses. Of the
16 retained attempts inspected, 13 logs end with
`ERROR: exceeded retry limit, last status: 429 Too Many Requests`, and have no
`last.txt`. The empty dispatcher note `NOANSWER:` hid this diagnostic. The first
maintenance attempt at the five-failure threshold also failed with HTTP 429.
There was no item return, failed Lean compile, permission refusal, or landing
rejection responsible for these attempts.

The first reader had already completed the split. Attempt `1792192938` recorded
server preflight success for temporary commit `15e45e47f5` and answered
`READY ...: 1 new nodes, 0 Mathlib leaves` at 08:02:55 Asia/Shanghai. The
dispatcher correctly launched an independent reader (`1792195375`). That reader
was interrupted by HTTP 429 at 08:15; the old dispatcher then launched a new
first reader and removed `.check`, losing its reader handoff. Immediate fresh
sessions amplified the retry loop and repeatedly reread completed work.

Historical `NameError: clone_prefix` traces in `dispatch_all.out` predate this
incident; the quoted dictionary key is already correct in the current source,
and current logs demonstrate successful reader launches. No change to that
expression was necessary.

## Repair and deployment

Concurrent maintenance has already committed the shared infrastructure repair:

- `6fb280508f`: `tools/launcher/worker_transport.py`, its tests, and dispatcher
  integration retain the worker role and retry transient transport failures.
- `a1a68055f2`: `tools/launcher/codex_retry.py`, tests and deployment instructions
  provide bounded, jittered recovery of the exact interrupted Codex session
  within its original worker deadline.
- `0abb765411`: dispatcher reader resumption preserves an unfinished review
  section within the same delivery round.

The Codex entry point on the dispatcher host now points to
`/home/ubuntu/weil-launcher-all/codex_retry.py`; the original package binary is
retained. This entry-point deployment covers new workers from the already
running dispatcher, so it needs no signal or restart. A process already running
the original binary continues normally. Other maintenance sessions are editing
the general dispatcher; this maintenance does not overwrite their work.

This Q49 maintenance installs
`/home/ubuntu/weil-launcher-nt/route-notes/lem-pod-connected-constant-h0.md`,
versions it at `tools/launcher/route-notes/lem-pod-connected-constant-h0.md`,
and records this report and sanitized attempt metadata at
`coord/reports/maintenance/Q49-lem-pod-connected-constant-h0-attempts.json`.
The route note is read dynamically by the running dispatcher's next first-reader
launch. It identifies the completed work, explains the HTTP 429s, and directs
the next reader to retain and validate the existing split.

Every installed existing file is backed up before replacement; new files also
have adjacent `.maint-Q49-connected-h0-1792196920.bak` snapshots. Backups are
retained outside the commit. Only explicitly named report, evidence and route
paths are committed, under `SHEAF_LEAD=L-only` and `coord/.merge.lock`, using
`Bin Wu <844524296@qq.com>`.

## Validation

The committed server tests passed: 8 worker-transport tests, 11 Codex recovery
tests, and 6 dispatcher reader-resumption tests (25 total). Tests start fake CLI
children only; they make no model calls. They cover terminal-error detection,
same-role retries, exact-session resume, permanent-error exclusion, final-answer
precedence, original budgets and second-reader persistence. Python syntax and
the dispatcher's existing failure-classification tests also passed locally.

At the final inspection, the original 08:29:13 Q49 first-reader process was
still working and writing new search records. Its sandbox was retained and the
live node was still stage-1 `unsplit`; this maintenance does not claim it has
been delivered, independently reviewed or landed. Provider availability is an
external condition; the repair preserves work and handles its interruption.

No mathematical statement, proof, Lean source, item claim, dispatcher counter
or active worker state was changed. No Lean compiler or Lake build was run.
No process was stopped.

## Next worker

Retain both JSON nodes, citations.json, searches.jsonl and report.md in
`/home/ubuntu/weil-newtargets-sandbox/Q49/lem-pod-connected-constant-h0`.
Compare the split with the current DAG and source and rerun the normal server
preflight. The old preflight success is historical evidence, not a substitute
for current validation or independent review. A first reader answers READY;
only the dispatched independent reader signs the second reading and delivers.

Verify whether an interrupted delivery already succeeded before repeating it.
Use `codex-retry.json` beside the worker log for provider-recovery metadata.
If the provider remains unavailable, preserve the sandbox and report the actual
transport diagnostic. Failure totals remain historical counts and do not
disqualify the item.
