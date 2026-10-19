# Q91 maintenance: lem-trf-iterated-weil-cocycle

2026-10-17. Dispatcher key `lem-trf-iterated-weil-cocycle@434bdc495`.

## Cause

The five attempts counted when maintenance started all ended in provider HTTP
429 with no `last.txt`: 1792196064, 1792196282, 1792196320, 1792196369 and
1792196408. See the request IDs and terminal errors in the adjacent evidence
directory. Repeated provider failure was incorrectly reduced to empty
`NOANSWER: `, then immediately retried as a fresh worker, losing the session.
Several attempts never reached a tool call. The gateway independently
reported `gateway_concurrency_limit` and `gateway_queue_full` during
maintenance. The launcher was configured for 700 worker slots, with
additional maintenance sessions. No inference about a failed proof follows
from these counts.

The earlier delivery did pass preflight and was approved by its reader.
Landing refused head `434bdc4950` because the full statement of cited node
`def-trf-strict-weil-complex` changed after the reviewed branch was built.
That guard is correct. The definition is in `sec-six-functors`; only its
explanatory discussion of categories of pairs and its Jordan-block example
changed. Its pair/isomorphism clause used here remained intact. The other
two original cited statements were unchanged. The evidence records the
exact committed comparison and hashes; it does not replace the worker's
revalidation against the latest DAG.

The generic return brief also says both "then compile" (in a stage-1 job)
and "A rebase ... is not a repair" (for a return specifically requiring a
rebase and citation revalidation). The item handoff resolves both points:
stage 1 runs DAG/preflight checks, and substantive citation review followed
by rebasing is the required repair when the used statement still suffices.

## Repair and validation

The common 429 supervisor was developed by NK maintenance and installed
during the parallel maintenance work. Server commit `a1a68055f2` tracks
`tools/launcher/codex_retry.py`, its regression tests and installation notes.
The active local entry point `/home/ubuntu/.local/bin/codex` now resolves to
`/home/ubuntu/weil-launcher-all/codex_retry.py`. This Q91 session checked that
installation and independently ran all 11 regressions against the installed
module: startup retry, exact-session resume, configuration preservation,
bounded randomized delays, deadline exhaustion, permanent errors, real
answers, and cancellation of the supervisor's own child. All passed, with
no provider requests. It resumes dispatch workers within their existing
budget and produces a useful BLOCKED result on exhausted temporary 429s.
Its original binary and symlink backups are owned by that maintenance.

Q91 maintenance installs the item-specific handoff at the launcher's dynamic
`route-notes/lem-trf-iterated-weil-cocycle.md` path, and tracks the same text
under `tools/launcher/route-notes/` here. The already-running dispatcher
reads this file for each newly started repair, so that clarification needs
no dispatcher restart. The evidence and this report are committed alongside
it. Existing paths are backed up before changes; new paths receive final
`.bak` snapshots. No Lean module, node, citation manifest or running
worker's report was edited by this maintenance session. No process was
stopped. Failure counts and the stale-citation landing guard are retained.

The official OpenAI configuration reference confirms separate HTTP-request
and stream-interruption retry settings; the dispatcher already supplied 30
of each, so merely raising those values was not the missing repair:
https://developers.openai.com/codex/config-reference/ . Persistent gateway
overload can still exhaust a worker's budget; recovery is not a promise of
account capacity.

## Next worker

Continue the retained sandbox. Attempt `1792197005` has already re-read the
changed definition and expanded the report/citations to justify the derived
pullback comparisons; its server dry run was in progress when this note was
prepared. Inspect the latest output before repeating it, and read the
actual current files because that worker may have progressed further.
Follow the normal READY, second-reading, delivery and independent landing
workflow. Do not redo the mathematics because older sessions ended with
NOANSWER. Do not compile Lean for stage 1, weaken a statement, or disable
the changed-citation landing check.

## Additional preflight race observed during verification

The running Q91 worker's first dry-run package was prepared before the
maintenance commit and reached server preflight after that commit. The old
packager invocation used the moving `origin/newtargets-dag` baseline and
therefore reported this maintenance's five files as outside the delivery.
They were not sandbox residue: it was a diff against the wrong commit.
The worker correctly repeated the dry run rather than deleting evidence or
editing unrelated files.

Parallel Q130 maintenance fixed this shared-ref race in server commit
`783eefd22616654c6d85f4f5f7d107772caa9533`: `tools/launcher/deliver.py`
captures the actual checkout SHA, and `tools/launcher/srvpreflight.py` pins
that SHA for transport and any fallback. Both active local scripts match
the committed server copies byte for byte. Six real-Git regressions pass,
including a ref advancing before preflight and during bundle creation.
The stale-citation landing check remains intact. The required Q91 rerun
uses this installed repair.

The current server recovery regression suite also passes all 18 tests,
including explicit dispatcher resumes and missing saved sessions, after
parallel commits `a5ae0952c31d887797156fd16ea7208a894cae05` and
`0fa398c792` extended the original supervisor. The earlier 11-test evidence
is retained; `retry-tests-current.txt` and `preflight-base-tests.txt` record
the newer verification. No live model calls or Lean compilation were used
for these tests.

## Successful actual-item verification

At 2026-10-17 00:51 UTC, Q91 attempt `1792197005` finished the required
server dry run successfully: `OK (not pushed)
deliver/Q91/lem-trf-iterated-weil-cocycle at aabfee28a6: preflight passed`.
It saved a durable stage-1 receipt and answered `READY
lem-trf-iterated-weil-cocycle: 0 new nodes, 0 Mathlib leaves`.
`q91-ready.txt` records the actual output. The independent second reader
should now follow the normal review and delivery path. Maintenance did not
push or merge the mathematical item.
