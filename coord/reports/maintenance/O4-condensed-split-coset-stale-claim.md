# O4 maintenance: completed condensed split-coset stage-1 claim

The obsolete O4 claim is reconciled. This is coordination repair of already
accepted stage-1 work; no replacement split or mathematical change was needed.

## Cause and evidence

Q31 delivery 49d08d601b4 landed at 2026-10-22T07:55:50Z in commit
04d18130e36c992a5fd728153bccb408a41eda12, reviewed PASS by
NT-cc-Q31-49d08d601. The parent has status split, four assembly steps, and
two statement-only helpers: lem-sfb-condensed-tensor-induction-adjunction and
lem-sfb-condensed-coset-tensor-normal-form. The stage-1 repair is resolved.
The landing is independently recorded in coord/ledger.md:26669 and
coord/deliveries.log:51033.

O4 acquired coord/claims/lem-sfb-condensed-split-coset-induction.lock at
2026-10-22T07:56:01Z, eleven seconds after that landing. The claim remained
held after the item disappeared from coord/queue.tsv, coord/queue-batches.tsv
and coord/queue-batches-all.tsv. claim.queue_stage(item) returns None;
claim.node_finished(item, "1") and dag_queue.stage1_completed(node) return True.
There is no O4 return or delivery branch for this item.

The protected launcher's dispatch_all.py Group.server() retains its old cached
stage when claim.queue_stage returns no stage. Group.work() then restarts a
held stage-1 claim without reconciling live completion. Its stage-3 completion
reconciliation does not cover this case. The worker reports correctly obeyed
coord/brief-stage1.md's live-wins rule; repeated retries cannot create an owed
delivery. The failure count is evidence of this stale input, not a dispatch gate.

## Repair and validation

Under SHEAF_LEAD=L-only flock coord/.merge.lock, tools/claim.py release O4
removed only this obsolete claim and appended the explicit maintenance reason
to coord/deliveries.log. This report records the existing accepted completion.
The transaction commits the claim deletion, this report and its own log line
with Bin Wu <844524296@qq.com> identity. A temporary index keeps unrelated
staged files and concurrent uncommitted log entries out of the commit.

Backups (not committed):
- coord/claims/lem-sfb-condensed-split-coset-induction.lock.O4-maint-1792659738.bak
- coord/deliveries.log.O4-maint-1792659738.bak
- coord/reports/maintenance/O4-condensed-split-coset-stale-claim.md.bak

After release the claim is absent and O4 no longer holds the item. The actual
claim.take("O4", item, stage="1") rejects it as already completed for stage 1;
a mock guarding claim.create verifies no claim creation was attempted. SHA-256
checks confirm the parent node, resolved repair note and Lean module are
unchanged. No Lean compilation is required for this coordination-only repair.
No Lake build, process kill, failure-count reset, pause, concurrency/admission
change, protected launcher edit or review/landing-tool edit was performed.

## Launcher-owner follow-up

Reconcile already-held stage-1 claims against live completion when no live
queue row, active repair, return or delivery remains. Preserve the human's rule
that listed, unclaimed work is dispatched and failures never stop retries.
Cover a reviewed split landing immediately before a claim is acquired, then
leaving the queue. dispatch_all.py is protected by this maintenance assignment
and was not edited. The item is repaired through its obsolete claim record;
the general launcher defect needs its owner's change.

## Next worker

There is no outstanding stage-1 repair of this parent. Preserve Q31's reviewed
two-node split; do not copy or redeliver it because of an old O4 BLOCKED note.
The existing sandbox report is historical verification and is left intact.
Child-node work and genuine stage-2/3 work follow the normal live queues.
Only a new live assignment or explicitly reopened repair can authorize new work.
