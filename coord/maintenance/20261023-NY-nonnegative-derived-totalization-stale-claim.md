# NY obsolete stage-1 assignment: nonnegative derived totalization

Maintenance 2026-10-23 for `lem-sfb-nonnegative-derived-totalization@new`.

Q52's reviewed four-node repair, delivery `50963f19c65`, landed in commit
`6aaa2b00388f74c8545057439a111634f0109303`. `coord/deliveries.log` records
completion at 2026-10-22T11:05:03Z. NY's claim was created at 11:05:25Z,
22 seconds later, and survived after the item disappeared from the live queue.
The initial five BLOCKED attempts and the following fifteen counted failures
all reported the same correct preflight rejection: the item's node file is
unchanged. The sandbox item equals the accepted live item.

Before this repair, server checks confirmed: status split, reviewed PASS by
NT-cc-Q52-50963f19c; repair state resolved; no owed stage-1 repair; stage 1
and stage 2 completed; queue_stage returned None; NY held the claim; no NY
delivery branch or open return existed. The recorded Lean interface is
Sheaf.CategoryTheory.NonnegativeDerivedTotalization.

The launcher's Group.server() keeps its saved stage when queue_stage is absent.
Group.work() restarts held stage-1 claims without reconciling live completion.
Thus this obsolete claim repeatedly received a stage-1 brief, while the brief's
live-wins rule correctly forbade replacing the accepted split. Neither the
mathematics nor preflight's unchanged-item check caused the failure.

Under SHEAF_LEAD=L-only and coord/.merge.lock, maintenance used the supported
tools/claim.py release NY command with an explicit completed-work reason.
It removed only NY's obsolete claim and appended one release event. Backups:

- coord/claims/lem-sfb-nonnegative-derived-totalization.lock.maint-NY-1792695687.bak
- coord/deliveries.log.maint-NY-1792695687.bak

No node, repair note, Lean module, launcher file, dispatcher state or failure
count was changed. No process was killed and no limit, throttle or pause was
introduced. No Lean compilation was needed because no Lean file changed.

The reusable dispatcher correction belongs to its owner: reconcile a held
stage-1 assignment that is absent from the current queue against live
completion, released repairs, pending deliveries and open returns, and release
obsolete completed assignments instead of retaining their old stage forever.
Preserve genuinely listed tasks and explicit released repairs regardless of
failure counts. Protected dispatch_all.py was not edited.

There is no outstanding stage-1 split to deliver on this item. Preserve Q52's
four-node split and the resolved repair. Its dependency nodes are
lem-sfb-cosimplicial-injective-total-replacement,
lem-sfb-injective-finite-total-derived-comparison,
lem-sfb-resolved-total-comparison-descent, and
lem-sfb-resolved-total-augmentation-square. They remain independent work as
their own records and queue stages dictate. A future worker on the parent
must follow a new live assignment or explicit released repair, not replay the
historical NY dry run or report DELIVERED without a new delivery.
