# Q52 stale stage-1 claim repaired

Item: `lem-sf-weil-lisse-internal-hom-tensor-dual`.

Q08's stage-1 delivery `325eef7187a` was reviewed by
`NT-cc-Q08-325eef718` and merged as `3cd83a8f932`.
`coord/deliveries.log` records Q08 done at 2026-10-22T04:22:44Z.
Q52 acquired the same item at 2026-10-22T04:22:57Z, while a stale queue
still listed it. The current live queue no longer lists the item.

Q52's newer claim survived the earlier landing's claim cleanup. The
launcher's held-claim retry path keeps stage-1 assignments after they
leave the queue and does not check completion again. Workers obeyed
`coord/brief-stage1.md:105` (preserve a live reviewed split), leaving no
new node to deliver; their mandatory dry runs therefore failed with
`FAILED: no node files`. This is stale assignment data, not missing
mathematics or a provider failure. Failure counts do not justify stopping
an open assignment.

Under `coord/.merge.lock`, maintenance verified the committed passing Q08
review, absence from the current queue, absence of a repair note, delivery
branch or Q52 return, and the exact Q52 claim timestamp. It backed up and
removed only that superseded claim. The reviewed DAG node and all Lean
files are preserved. No process is stopped by this repair.

Claim backup: `/home/ubuntu/weil-maint-bak/Q52-lisse-internal-hom-20261022T050031Z/lem-sf-weil-lisse-internal-hom-tensor-dual.lock.bak`.
The only other changed file is this audit record. Commit uses the merge
lock and Bin Wu identity. Pre-existing uncommitted bookkeeping is excluded.

Launcher follow-up (documented, not edited): `dispatch_all.py`,
`Group.candidates()`, needs to retire held stage-1 claims when the live
committed node is completed and no current stage-1 assignment or repair
is owed. Recheck the current stage before releasing, preserving real
later-stage work. Preserve the human's rule that queued unclaimed tasks
are dispatched. Do not change failure-count policy, admission, or capacity.

A future worker should retain Q08's reviewed split, avoid another split
or an empty delivery, and follow any genuinely reopened assignment's
stage and repair record. The single-resolution dependency remains normal
separate work; this maintenance does not prove the upstream theorem.
