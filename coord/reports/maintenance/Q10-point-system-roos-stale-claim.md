# Q10 point-system Roos transport: obsolete claim repaired

Item: `lem-trf-point-system-roos-transport`, dispatcher key `lem-trf-point-system-roos-transport@new`.
Maintenance: 2026-10-22T11:10:40Z.

## Cause

Q130's accepted re-split merged as `888863b0f86` at 2026-10-22T06:50:21Z
(`coord/ledger.md`, original line 25821). The stage-1 repair note is resolved.
The item's existing stage-2 Lean record also passed review. Q10 acquired its
claim at 2026-10-22T06:51:03Z, after that merge. The claim survived after the
item disappeared from `coord/queue.tsv`. Both the current queue and the
committed queue in `888863b0f86` omit this item.

The launcher's `Group.server()` enumerates every unexpired held claim and
updates its stage only when `claim.queue_stage()` returns a value. With no
queue row, the saved stage remains 1. `Group.work()` retries that held claim
without checking stage-1 completion. Its off-queue completion checks cover
stage 3. Thus each worker correctly follows `coord/brief-stage1.md` and refuses
to duplicate Q130's accepted split. Failure counts do not cause this defect.
The exact queue contents at the instant Q10 acquired the claim were not logged;
the initial admission race is inferred, while the stale-claim retry path is
directly confirmed by the current claim, state, prompts, and dispatcher code.

## Repair

Released only Q10's obsolete claim through `tools/claim.py release`, with the
completion reason recorded in `coord/deliveries.log`. Committed the claim
deletion, this record, and a ledger entry under `coord/.merge.lock`. Backups of
the removed claim, the append-only delivery log, and the ledger use suffix
`.maintenance-Q10-1792666994.bak`. The accepted node, its Lean module, and resolved repair note retain
their previous bytes. No launcher tool, queue, failure count, concurrency
setting, or worker process was changed directly.

## Validation and handoff

The live server reports stage-1 and stage-2 completion, no open Q10 return, no
Q10 delivery branch, and no queue row. After release, Q10 no longer holds the
item. Fresh explicit stage-1 and stage-2 claims are refused because this work
is complete. No Lean file changed, so no compiler or Lake command was needed.

A future stage-1 worker needs a newly released stage-1 repair order. Preserve
Q130's split and its dependencies `lem-trf-point-system-normalized-comparison-data`
and `lem-trf-point-restriction-whole-roos-square`. Proof work on the existing
Lean module is a separate stage-3 assignment.

## Launcher follow-up (protected file; not edited)

`/home/ubuntu/weil-launcher-all/dispatch_all.py` should reconcile held stage-1
assignments against the current queue and the live completion predicate before
starting another worker. If the item is absent from the queue, completed for
stage 1, has no released repair order, and has no delivery/return to service,
release its stale claim with a completion reason. Keep dispatching listed or
genuinely unfinished tasks regardless of failure count. This needs no pause,
throttle, retry limit, or provider change. The current incident is repaired by
the claim release; prevention for future stale held assignments belongs to
the launcher owner.
