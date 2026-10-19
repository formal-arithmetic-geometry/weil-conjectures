# Q31: lem-coef-segal-interval-cover maintenance

2026-10-17. Stage 1, `/home/ubuntu/weil-newtargets`.

## Cause

The repeated failures were model-provider transport failures. All twelve
completed worker logs from `1792195041` through `1792196772` end with HTTP 429
retry exhaustion and have no `last.txt`. Attempt `1792196229` explicitly
reports `gateway_queue_full` / "Too many pending requests". Even the maintenance
session dispatched after five failures died with HTTP 429. The original
dispatcher inspected only `last.txt`, discarded these diagnostics and wrote
the empty note `NOANSWER:`. Immediate redispatch repeated the same failure.

The original launcher configuration allowed 700 workers and launched maintenance
outside that worker limit. An observation during this investigation counted
426 worker and 75 maintenance Codex processes. The gateway rejected this load;
there is no evidence that ten mathematical attempts or ten delivery reviews
failed. The server returns, deliveries and landing logs had no item-specific
return explaining these attempts. The first worker had already retained a
six-step split, report, ten citation quotes and search evidence in its sandbox.

## Repair and deployment

Several maintenance sessions repaired the same shared infrastructure concurrently.
Q31 reused and verified their installed fixes instead of replacing their code:

* `tools/launcher/codex_retry.py` and `codex_admission.py`, installed through
  `/home/ubuntu/.local/bin/codex`, supervise new dispatched workers immediately.
  The live gate uses 64 children, one-second launch spacing and a 60-second
  provider cooldown. Existing workers drain naturally. Relevant shared commits
  include `440cf59d09` (provider throttling), `7aa72985b8` (explicit session
  recovery) and `f89683929f` (cancel obsolete retries).
* `tools/launcher/codex_capacity.py` and `dispatch_all.py` classify provider
  failures, adapt admission and retain pending reader/attachment phases.
  Maintenance reservations count toward admission. Relevant commits include
  `ecbefbec53` and `359f0b6b5f`. Dispatcher source changes load at its next normal
  start. The running process was not killed or restarted.
* `tools/launcher/stage1_handoff.py`, committed in `f2419b5883`, preserves successful
  server preflight receipts with input hashes. Edits invalidate an earlier
  receipt; recovery starts the independent reader and does not push a delivery.

This Q31 maintenance installed
`/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-segal-interval-cover.md`
(versioned as `tools/launcher/route-notes/lem-coef-segal-interval-cover.md`).
It explains the actual provider failures, preserves the saved packet, requires
a fresh dry run after citation edits, and retains the independent reader stage.
The running dispatcher reads route notes on its next author launch.

It also installed `test_q31_transport_recovery.py` beside the local dispatcher
and in `tools/launcher/`. Its three tests exercise the real reaper: HTTP 429
classification and packet preservation, receipt invalidation after a report
edit followed by a fresh validated handoff, and admission after legacy workers
drain without using failure counts as a cutoff.

Q31 briefly copied the earlier Q33 capacity draft while other sessions were
installing it. Their completed shared code superseded that copy. Q31 also
temporarily set the launcher ceiling to 400/startup 32, then reconciled its
configuration edit with the lower 210-slot ceiling another session had already
installed, retaining the current startup 8/cooldown 60 settings. Snapshots of
the final settings are in this report's evidence directory. The running
dispatcher retains its loaded configuration; the live Codex admission gate
supplies the immediate concurrency control. Every replaced file has a Q31
`.bak`; no unrelated server changes were staged.

A temporary Q31 `stage1_handoff.py --watch-seconds 1800` observer was started
to recover an absent answer only after natural worker exit and a matching
receipt. The worker wrote READY itself; the observer made no change and was
terminated by Q31. No pre-existing process was signaled.

## Verification and current item state

The active worker completed server `check_dag`, `review_split` and two full
delivery dry runs. Its first preflight passed at `eeb2497787`. After its own
bibliographic/report correction, its final preflight passed at `68deb14b19`.
It answered `READY lem-coef-segal-interval-cover: 0 new nodes, 0 Mathlib leaves`.
The dispatcher then started an independent stage-1 second reader in
`run/Q31/lem-coef-segal-interval-cover.1792198610` (PID 3488621). The new reader
is subject to provider admission while older sessions drain; this is a capacity
queue, not a new mathematical failure. No Q31 maintenance edited the node or
performed the item's mathematics. No Lean file was changed or compiled.

The three Q31 regressions passed locally and on the server. Another 21 installed
provider-admission, stage-1-handoff and worker-transport tests passed locally.
These tests use temporary files and fake children, with no model API calls or
Lean build. The attempted dispatcher `--dry` was correctly refused by the
existing dispatch lock, so no second dispatcher was started.

## Next worker

Retain the sandbox at
`/home/ubuntu/weil-newtargets-sandbox/Q31/lem-coef-segal-interval-cover`.
The latest accepted packet has six proof steps and zero new nodes; citation and
search evidence remain there. For the current second-reader assignment, retain
`.check`, independently review the packet and sources, validate any changes,
and deliver using the second-reader brief. An author retry must inspect and
dry-run the prepared packet before restarting broad searches. A prior receipt
does not validate changed files. Failure totals never disqualify the item.

Evidence: `Q31-segal-interval-cover-evidence/attempts.json`,
`successful-preflights.txt`, `final-receipt.json`, `q31-handoff.json`, both
configuration snapshots and `q31-regressions.txt` beside this report.
