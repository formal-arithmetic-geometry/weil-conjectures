# Q03 strict DVR reduction triangles: dependency record repair

The independent return on immutable head df60101867dc (coord/returns/Q03.md,
2026-10-21 09:02 UTC) requires two helper definition ownership nodes, a citation
to def-weil-integral-derived-reduction, and both higher theorem nodes in
proof_deps only. The worker has already prepared that repair and its unchanged
Lean module compiles.

The repeated failure is a delivery-policy mismatch: launcher batch2/deliver2.py
preserves additive proof_deps repairs, but server node_fields.correction_fields
classifies a proof_deps delta as a statement correction. Its statement-change
check then rejects the unchanged statement. Merely relaxing that check would
also be insufficient: stage2_delivery and merge_delivery must preserve the
dependency update on landing. Those protected tools are left unchanged.

Maintenance records the reviewer's two required proof dependencies on the
authoritative DAG, with their interface citations in existing proof step 6:

- lem-weil-derived-scalar-extension-restriction-adjunction
- lem-weil-integral-reduction-tower-well-defined

proof_deps remains exactly the union of proof-step uses. The mathematical
statement, statement dependencies, original mathematical arguments and Lean
interfaces are unchanged. This is the existing reviewer's dependency bookkeeping;
no theorem is implemented and no Lean module or new definition is landed here.
The node's original bytes are preserved in the adjacent
.json.maint-Q03-1792580599.bak file.

Next worker: refresh the authoritative item metadata from main, retaining the
sandbox lean record, added definition ownership nodes and added stmt_deps.
deliver2 already rebases non-worker-owned fields from main. The two proof_deps
now match main, so do not fabricate statement_change or a Statement corrected
section. Keep the reviewed Lean module unchanged. Re-run deliver2 --no-push,
then deliver through the normal independent review/landing workflow. The old
report's preflight failures describe the state before this metadata commit.

No dispatcher counters, claims, return entries, concurrency controls, launcher
code, review service or landing tools were changed. A general policy for
stage-2 dependency-only repairs requires a coordinated change by their owner;
this item no longer needs that broader tooling change.
