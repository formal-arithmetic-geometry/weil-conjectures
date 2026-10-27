# Q25 maintenance: obsolete cohomological-smoothness claim

Item: thm-pur-cohomological-smoothness@new, stage 1. Investigated 2026-10-23 Asia/Shanghai (2026-10-22 UTC).

## Cause and evidence

The assignment was complete; a stale held claim caused repeated dispatch. This is a coordination-state failure, not an unfinished mathematical split.

- Accepted stage-1 landing: afbc96edf7f, Q117, reviewer NT-cc-Q117-634318365, 2026-10-22T07:42:44Z, three new statement-only nodes. The live node is split with reviewed.result=pass and retains its stage-2 Lean record.
- coord/repair-notes/thm-pur-cohomological-smoothness.json has state=resolved. Its historical released timestamp does not authorize another split.
- The obsolete coord/claims/thm-pur-cohomological-smoothness.lock named Q25, since 2026-10-22T07:43:05Z, timestamp 1792654985.1888807. It was acquired 21 seconds after the accepted landing. Its exact acquisition race cannot be established from the claim alone.
- The live queue no longer lists the item. claim.queue_stage returns None; claim.node_finished(item, '1') and claim.node_finished(item, '2') both return True. Q25 had no open return or delivery branch for it.
- The local dispatcher state retained stage=1 and 91 counted tries. All 96 retained Q25 worker last.txt files say BLOCKED on the accepted Q117 split (the first five tool-failure dispositions are counted separately).
- dispatch_all.py Group.server (around lines 322-339) returns every live held claim and updates the remembered stage only for a numeric queue stage. Group.work (around lines 790-839) dispatches the held claim again without a stage-1/2 completion check when no queue stage exists. Thus the old stage survives indefinitely. The 72-hour claim TTL prolongs this stale assignment.

Recovered provider errors occur in some retry metadata, but every retained final disposition is the same stale-assignment BLOCKED. Provider handling is not the cause fixed here and was not changed.

## Repair

Released the completed Q25 claim through tools/claim.py under coord/.merge.lock, then committed its tracked deletion and this report under that lock. The release record is ordinary `released`, not abandonment: the initially tool-written abandonment label was corrected before validation, so this repair creates no stage-2 parking condition. The accepted node, proof, review, repair note, Lean module, queues, worker sandbox, failure counts, limits, launcher code, review service and landing tools were not changed.

The normal deliveries.log append was already captured by concurrent landing commit 2ed90898c2d6cfaa85b8fd64938fc2aff1d3e095 before this maintenance commit. No unrelated working-tree changes were staged.

Backups retained on this server (ignored by git):

- coord/claims/thm-pur-cohomological-smoothness.lock.bak-maint-Q25-stale-20261023: exact original claim, copied before release.
- coord/deliveries.log.bak-maint-Q25-release-label-20261023: complete tool-produced log before correction of this maintenance line's label.
- coord/deliveries.log.bak-maint-Q25-before-release-20261023: log content before this release, reconstructed from the exact prefix preceding the appended release line.

## Validation

Live assertions passed: accepted Q117 review and resolved repair preserved; no queue row, held Q25 claim, Q25 return or Q25/Q117 delivery branch; fresh stage-1 and stage-2 claim.take calls both refuse the item as already completed and create no claim; claim.stage2_parked(item) is False. No Lean file changed, so no compilation was needed or run. No build, process termination, cap, throttle, admission limit or pause was introduced.

## Launcher-owner follow-up

Do not edit dispatch_all.py in this maintenance scope. Its owner should reconcile an existing held stage-1/2 claim when the live queue reports no stage: if the live node is completed for the remembered stage, there is no applicable released repair, no open return and no pending delivery, release the obsolete claim instead of dispatching it with the remembered brief. Preserve the human's rule that queue-listed work is dispatched, and preserve explicit released repairs. Failure counts must remain irrelevant to dispatch eligibility. This is a completion check, not a concurrency restriction.

## Next worker

There is no authorized stage-1 work on this item now. Preserve Q117's accepted split and the resolved repair. A historical released timestamp is not a current repair order. Continue the remaining open obligations through their own live queue entries. If this parent is dispatched again without a new released stage-1 repair, inspect for a newly stale claim and the missing dispatcher reconciliation; do not manufacture another split or a new repair order.
