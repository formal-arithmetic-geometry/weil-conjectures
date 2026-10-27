# Q29 Tate-submodule stale assignment (2026-10-24T11:48:09Z)

Item: `lem-trf-tate-submodule-norm-controlled-generators`. Maintenance baseline: `d298fecf8fcd5938c480ad0c95403e7d8502c8d1`.

The delivery passed preflight and the reader approved it, but it is no longer
stage-1 work. Both tools/dag_queue.py nodes_dir() and queue_nodes_dir() resolve
to this repository's dag/nodes; tools/livedag.py is retired. The live item is
unsplit and stage1_completed is false. There is no side completion to promote.

The raw stage-1 reach includes the item through the human-excluded
lem-per-gabber-absolute-equivariant-modification and
lem-per-complete-local-rigidification-comparison. Queue reach correctly excludes
those routes after 987f97e422e. The remaining uncut target reach includes it,
but stage-1 reach stops at completed ancestors, including sk-thm-trace-transport
and thm-trf-grothendieck-lefschetz-qbar. Thus dist1 and queue_dist contain the
item, queue_dist1 and stage1() do not. The generated queue has no row for it.
The item itself is not in route-pivot-dropped.txt.

The first worker was stopped as off-queue at 18:05 +08, but its delivery branch
prevented release. A stale actionable return then kept dispatching repair
workers. tools/nt_land_batch.py classifies any item absent from stage1() as
notopen; when retire_completed rejects an unsplit node, its fallback infers
side-completion mismatch from the queue node being incomplete, without checking
completion in the project copy. This is a false diagnosis for an off-queue,
unfinished item. Rebase or proof edits cannot change its work eligibility.

Maintenance removes only this obsolete return and its Q29 claim, preserving
the approved packet at `refs/superseded/Q29/lem-trf-tate-submodule-norm-controlled-generators/4e831ef3bc01dcd4f4f6ac634b868a762a1e0e42` and removing the exact matching delivery
branch with a Git compare-and-delete transaction. A resolved repair note
records this disposition. It does not mark the theorem split, proved or
completed, add an exclusion, reopen a route, or discard the worker sandbox.

The landing and dispatcher tools are launcher-owned and were not edited.
Their owners should distinguish off-queue unfinished work from completed work,
retire obsolete repair records while preserving the packet, and require actual
project/live completion disagreement before reporting a promotion failure.
Do not use failure counts as an eligibility gate.

Next worker: read the resolved repair note. No resubmission is requested while
stage1() excludes the item. If an active target or statement-prerequisite route
later makes it eligible, issue a fresh brief and reuse the archived split and
retained sandbox after validating the current dependencies and normal review.

## Original stale return

## lem-trf-tate-submodule-norm-controlled-generators (2026-10-24 11:03 UTC, branch head 4e831ef3bc0)

L: approved by the reader, but the landing refused it: NOT MERGED lem-trf-tate-submodule-norm-controlled-generators: lem-trf-tate-submodule-norm-controlled-generators: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
