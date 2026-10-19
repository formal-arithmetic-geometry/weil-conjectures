# Q86: qbar idempotent-completeness pipeline maintenance

Date: 2026-10-17. Item: `lem-weil-qbar-idempotent-complete`, stage 1.

The repeated empty `NOANSWER` results were terminal model-service HTTP 429s.
The Q86 run `1792194998` completed much of its independent second reading but
lost its final answer to request `a410f3a3-5505-4d0b-9b16-79d00fab2d55`.
Nine subsequent repair runs also ended in HTTP 429s; several failed at startup.
The dispatcher inspected only `last.txt`, hid the terminal diagnostics and
restarted fresh authors. A worker that exited between reap and scheduling
could also be discarded before its failure was counted. The five recorded
failures therefore understate the ten observed provider failures.

The existing sandbox contains the node, 14 verbatim citation entries, search
records and author/reader reports. Its earlier no-push checks succeeded at
`15ac569e77` and `db946514de`. The original C4/E1 content return still needs the
normal independent review: the candidate scope correction and downstream
analysis are not endorsed by this maintenance investigation.

Concurrent maintenance has already supplied the shared fixes:

- `a1a68055f2b73fe62674754cb95071667bd798ac`: bounded, jittered provider retries,
  exact-session resume and explicit exhaustion diagnostics in `codex_retry.py`.
  The installed `/home/ubuntu/.local/bin/codex` entry points to
  `/home/ubuntu/weil-launcher-all/codex_retry.py`, and its bytes match that
  maintenance's tested source. New dispatched workers use it immediately.
- `6fb280508f`: dispatcher handoff persistence, diagnostic recovery and the
  reap/scheduling race repair. This source applies on a normal dispatcher
  start; no existing process was killed to reload it.

The active older run `1792197005` also encountered a moving-ref preflight
failure: it was blamed for NG kernel-pushforward files absent from its sandbox.
The installed delivery and server-preflight wrappers now pin the checked-out
base SHA. The worker is rerunning its normal no-push check. This is a tool
baseline failure, not evidence for editing the item's mathematics.

This maintenance adds an item route note at
`tools/launcher/route-notes/lem-weil-qbar-idempotent-complete.md`, installed as
`/home/ubuntu/weil-launcher-nt/route-notes/lem-weil-qbar-idempotent-complete.md`,
and operational handoff fields in
`coord/repair-notes/lem-weil-qbar-idempotent-complete.json`. The original return
reason remains in force. The route note tells authors to validate the retained
packet and return READY; the independent reader must recheck the later step-3
edit, the statement correction and its downstream consequences before delivery.

Validation: 25 server regression tests passed from `tools/launcher` with
`python3 -m unittest -v test_codex_retry test_worker_transport
test_dispatch_failure_classification`. These tests use fake CLI processes and
temporary repositories; no model request or Lean compiler is run. The recovery
supervisor's 11 tests also passed locally. The first root-level module invocation
of `test_codex_retry` had an import-path error; the documented direct/script
invocation and the combined suite from its directory pass.

Every installed replacement has a `.bak`. No Lean source, node mathematics,
sandbox report, dispatcher state, concurrency setting or running process was
changed by this maintenance. Failure counts remain counts and never disable
dispatch. No library build was run. Provider availability is external; the
recovery code handles interruptions and preserves evidence, rather than
guaranteeing that a future request succeeds.

Detailed evidence: the launcher's maintenance directory
`/home/ubuntu/weil-launcher-all/maint/Q86-lem-weil-qbar-idempotent-complete-1792197004/`.
The final `REPORT.md` there records this maintenance commit and the final worker
status. Official error guidance:
https://developers.openai.com/api/docs/guides/error-codes .


## Verified recovery

The active worker's retry passed server preflight at `66ce2a32f0` on
2026-10-17 at approximately 08:47 +08, with a durable stage-1 dry-run receipt.
It used the retained packet and added no nodes. This verifies recovery from the
moving-baseline failure; it is not a maintainer mathematical acceptance.
The base-pinning fix is committed as
`783eefd22616654c6d85f4f5f7d107772caa9533`. Its six preflight-base regressions
and three stage-1 packaging regressions passed on the server. Together with
the provider/reader/classification suite, 34 server regression tests passed.

The Q86 diagnosis and handoff were committed as
`efdbcfe9f234f8e7d141b7ad0a5516f3dc601812` under the required merge lock and
identity. The next phase is the normal independent second reader, which must
read the latest packet before a no-push check and delivery. Maintenance has
not supplied a mathematical approval, fabricated a worker answer, or changed
dispatcher state.
