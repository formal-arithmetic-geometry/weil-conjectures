# Q03 obsolete stage-1 claim repair

Recorded 2026-10-22T10:50:45.447384+00:00; maintenance run 1792665974.

Item: `lem-sf-open-external-tensor-normalization`.

Q142's re-split was accepted in commit `2b45edf27db` at 2026-10-22T08:25:55Z
(review NT-cc-Q142-98cb16459). The repair note is resolved. Q03 acquired
its claim at 2026-10-22T08:26:00Z, five seconds after that completion.
The first Q03 worker already reported the accepted live split.

At repair time `claim.queue_stage(item)` is None, `stage1_completed(node)`
and `node_finished(item, "1")` are true, and no released stage-1 repair,
Q03 return entry or Q03 delivery branch exists. The sandbox node matches
the accepted live node. Preflight correctly rejects an unchanged node.

Cause: a claim obtained across queue refresh retained stage 1 after the
item left the queue. `dispatch_all.py` Group.server updates saved stages
only when queue_stage returns 1/2/3; a missing row retains the saved stage.
Group.work then treats the held claim as new work and restarts it after
each BLOCKED answer without testing stage-1 completion. Counts do not gate
work and were not changed.

Repair: released only the obsolete Q03 claim with tools/claim.py release.
Backups of the claim and delivery log are beside the original paths with
suffix `.maint-Q03-1792665974.bak`. Only this release line is staged from deliveries.log;
other uncommitted log entries and unrelated work are preserved.

Launcher follow-up (outside this maintenance run's edit authority): reconcile
held stage-1 claims whose queue row disappeared against the live stage-1
completion predicate. When complete with no released repair or outstanding
return/delivery, release the obsolete claim and omit it from worker starts.
Respect queue authority for items still listed, preserve genuinely released
repair work, and keep failure counts out of eligibility decisions. No cap,
throttle, admission limit or pause is needed.

Next worker: this accepted stage-1 item has no current assignment. Use its
accepted proof and review. Work on a future released repair only if one
exists; use the actual live queue stage for any future assignment. The Lean
module is already stated, so do not manufacture a split change or attachment
to satisfy the unchanged-item gate. No Lean was changed or compiled.

Release entry:
2026-10-22T10:50:45Z Q03 released lem-sf-open-external-tensor-normalization: maintenance Q03/1792665974: obsolete stage-1 claim acquired after accepted Q142 split 2b45edf27db; live stage 1 completed, repair resolved, no queue row, return or delivery; release duplicate assignment

Preserved file SHA-256 values:
- `/home/ubuntu/weil-conjectures-sheaf/dag/nodes/sec-six-functors/lem-sf-open-external-tensor-normalization.json`: `dd0ed8840d7ec047f82f57d05608df4cb3b427c75acce252ba1a29cf7135fa23`
- `coord/repair-notes/lem-sf-open-external-tensor-normalization.json`: `005a438bcdcec0db09ee22e76fd18884a191a9268908281fd1d464d090916c93`
- `lean/Sheaf/SixFunctors/OpenExternalTensorNormalization.lean`: `41fb9cd35ad8487754f3090209f215a021d27da7b5e377d57a3627d9ec2acf86`
