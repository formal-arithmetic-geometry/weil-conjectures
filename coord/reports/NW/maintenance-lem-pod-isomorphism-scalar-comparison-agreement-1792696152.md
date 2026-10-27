# Maintenance: lem-pod-isomorphism-scalar-comparison-agreement

2026-10-22T19:12:06Z, NW maintenance.

Cause: Q137's accepted stage-1 re-split was committed as
5b1a2f0be63f7d4af633dc4b848ce5bdab25da93 at 2026-10-22 11:05:21 UTC.
That commit still lists the parent in coord/queue.tsv:656 as stage 1.
NW's claim was created at 2026-10-22T11:05:26Z, five seconds after the commit.
The human's 2026-10-22 listed-item policy permits this claim. The item later
left the queue, but dispatch_all.py Group.server retains the previous stage
when claim.queue_stage returns None. Group.work reschedules held, undelivered
stage-1 claims without reconciling stage-1 completion. The 20 retained NW
attempts all correctly answered BLOCKED because the reviewed split and resolved
repair note prohibit another split; unchanged-item preflight correctly refused it.
The dispatcher state reported 15 failures. No mathematical repair was needed.

Repair: under SHEAF_LEAD=L-only flock coord/.merge.lock, verified live completion,
resolved repair note, no queue row, no delivery branch and no open NW return.
Released only the obsolete NW claim through tools/claim.py release, recorded
that release in coord/deliveries.log and appended coord/ledger.md. No node,
repair note, Lean source, worker sandbox or launcher-owned code was edited.
The other 5 NW claims and all three protected item files were verified unchanged.
Commit only this claim deletion, this report, and the two maintenance log additions;
retain any pre-existing uncommitted log additions in the working tree.

Backups: /home/ubuntu/weil-maint-bak/NW-lem-pod-isomorphism-scalar-comparison-agreement-1792696152/, preserving the original relative paths with .bak suffixes.
The new report also has a .bak snapshot there.

Next worker: stage 1 is complete. Do not manufacture a changed split or claim
ATTACH from the still-sorried Lean theorem. The accepted child nodes are
lem-pod-counit-scalar-word-coordinates and
lem-pod-explicit-scalar-cone-word-coordinates. A future assignment must follow
its current stage and brief, or a newly released stage-1 repair order.

Protected-code follow-up for the launcher owner: reconcile held stage-1 claims
with current completion and repair state before scheduling. Retire completed
off-queue claims through the claim protocol after checking branches and returns;
missing queue stage must not preserve an obsolete stage forever. The landing/queue
publication path should avoid completed-parent/stale-queue snapshots. Preserve
the listed-item policy and all genuine work; add no throttle or admission limit.
These protected files were not edited.

No Lean source changed, so no compiler or build was run.
