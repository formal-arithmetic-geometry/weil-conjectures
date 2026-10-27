# Q91 normalized-realization stale stage-1 claim reconciliation

The obsolete Q91 claim was released under coord/.merge.lock on 2026-10-23.
O1's accepted split is server commit 291c21c7a3576f50d2aa2188d3191e1fb6020740,
reviewed PASS by NT-cc-O1-03b5f9782 and recorded done at 2026-10-22T06:18:09Z.
Q91 acquired the stale claim at 2026-10-22T06:19:34Z. Its 72-hour claim TTL had
not expired. Stage 1 is complete, the stage-1 repair is resolved, and no current
queue row, open Q91 return or Q91 delivery branch exists. The latest worker
answered normally (zero provider recoveries) and preflight correctly rejected
the unchanged item. This is stale coordination data, not a mathematical failure.

Protected launcher dispatch_all.py retains a remembered stage when
claim.queue_stage returns no row (Group.server / Group.stage). Group.work then
retries the held item as new stage-1 work without checking live completion.
That explains 60 attempts at lem-coef-compact-support-normalized-realization@new.

Changes: normal tools/claim.py release removed only the obsolete claim and
appended its reason to coord/deliveries.log; this record documents the repair.
Existing claim/log files have .maint-Q91-1792743345.bak backups. This new record
also has a .bak snapshot. No launcher code, dispatcher state, worker sandbox,
DAG node, accepted repair or Lean source was changed. No retry cutoff, cap,
throttle, admission limit or pause was introduced; no processes were killed.

Validation under the same merge lock: owner/timestamp rechecked; queue stage
None; live stage-1 completion true; repair resolved; no open return or delivery;
claim absent after release; Q91 no longer holds the item; a real stage-aware
claim.take(Q91, item, stage='1') refused it as completed. Node, repair and Lean
SHA-256 values were equal before and after reconciliation:

- dag/nodes/sec-six-functors/lem-coef-compact-support-normalized-realization.json: `575c8b207b2c68d932afcdc79132e557c648165342e076f45cdea49c6b56ef9f`
- coord/repair-notes/lem-coef-compact-support-normalized-realization.json: `2fdff2d88791251a183bc1943b0e2aa2626f94b21a1e0b92c747ab7e0c2dc9f0`
- lean/Sheaf/Paper/CompactSupportNormalizedRealization.lean: `82555ec8ea77f7e7a2c26c9483c4f7ec9c3705ca64af2b2608cbe871739ea10d`

Launcher-owner follow-up (implementation protected by the maintenance brief):
after a successful authoritative server read, reconcile held stage-1 claims
that have no queue row, are live-complete, and have no released repair, return
or pending delivery. Release obsolete assignments instead of restarting their
remembered stage. Carry the requested stage through claim/start and refresh
from current queue rows. Failed/incomplete reads are unknown. Preserve listed
unclaimed work, released repairs, returns and genuine open work. Never gate by
failure count or add concurrency/admission limits.

Next worker: preserve O1's four-step accepted assembly and its three dependency
nodes: lem-coef-compact-support-quotient-cocycle,
lem-coef-compact-support-reduction-adjoint, and
lem-coef-sequential-varying-ring-realization. Stage 1 requires no redelivery.
Do not manufacture a node diff or ATTACH to satisfy the obsolete assignment.
Future work follows a current queue assignment or newly released repair and
its appropriate stage brief. Retain the historical sandbox and attempt counts.
No Lean compilation was needed for this bookkeeping-only repair.
