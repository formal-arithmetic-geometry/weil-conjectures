# Q23 local Frobenius stale claim reconciliation (2026-10-23)

Q128's stage-1 re-split landed at cde49ec184d9847959621505e80f89a6eeba6dd8
at 2026-10-22T06:51:54Z (delivery log), reviewed PASS by
NT-cc-Q128-7b5c11226 after reviewer fixes. The parent has three steps,
2805 proof characters and three extracted children:
lem-trf-finite-return-frobenius-cancellation,
lem-trf-local-normalization-strict-realization,
lem-trf-iterated-return-transport-scalar-calculus.
Its stage-1 repair record is resolved.

Q23's claim was created at 2026-10-22T06:52:12Z, 18 seconds after the
recorded landing. The authoritative queues no longer list the item. There is
no open Q23 return or delivery branch. All 74 retained Q23 attempt responses
say BLOCKED because the split is already live or the item is unchanged;
the dispatcher recorded 69 counted failures under the @new key.

The surviving claim was the immediate cause. Group.server() in protected
dispatch_all.py retains the old stage when claim.queue_stage() returns None;
Group.work() retries undelivered held claims without checking stage-1
completion. The short claim/landing interval is consistent with claiming
from a queue that had not yet refreshed. Current claim.take() intentionally
permits listed work on the human's authority, so that rule was not changed.

Under SHEAF_LEAD=L-only and coord/.merge.lock, backed up the claim and log,
then used tools/claim.py release with a non-abandonment maintenance reason.
Only the removed claim, the release log line and this record were committed.
Any unrelated preexisting log appends were preserved outside this commit.
The parent, all three children, resolved repair record and Lean module were
verified byte-for-byte unchanged. No Lean compile or Lake build is needed.

Backups:
- coord/claims/lem-trf-local-frobenius-transport-normalization.lock.maint-Q23-1792699724.bak
- coord/deliveries.log.maint-Q23-1792699724.bak
- coord/changes/maint-Q23-local-frobenius-stale-claim-20261023.md.maint-Q23-1792699724.bak

Launcher-owner follow-up (report only): reconcile held stage-1 claims whose
authoritative queue row disappeared against stage1_completed and repair
state before starting another worker. Preserve newer returns, pending
deliveries and explicitly released repairs, and use any later queued stage.
Listed work must continue to dispatch. No failure-count cutoff, cap, throttle,
admission limit, wait or pause is called for.

Next worker: there is currently no stage-1 task for this parent. Preserve
Q128's reviewed split. Do not resplit, claim a new attachment or push an
unchanged delivery. Follow the current queue and a new explicit repair if one
appears. Completion at stage 1 does not certify the Lean proof or its children.
