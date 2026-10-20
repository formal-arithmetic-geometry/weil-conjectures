## What changed

Withdrew `Sheaf.AlgebraicGeometry.MixedCommutatorTangent` and its sole consumer,
`Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket`, using deleted.txt (brief step 8d).
The consumer is unclaimed and has no importers in either library root. Both have completed
counterparts under WeilConjectures, whose declarations, signatures, attributes, imports and
proofs remain untouched. The two existing DAG lean attachments are repointed to the adopted
upstream twins;
both nodes, their statements and their proof plans are preserved.

Change record: `coord/changes/retire-mixed-commutator-tangent-sheaf-twins.md`.
`coord/queue.tsv` marks the assigned module `retire`, consumers 1. The earlier retirement
record retained both files only because a consumer was in a pending landing. Current searches
find just the consumer importing the item, and no importers of the consumer. The downstream
--uses checks list no declaration users.

## Proved and sorry left

Original assigned holes: 1, in
`AlgebraicGeometry.GeneralLinearGroup.mixedCommutator_tangent`
(node `lem-wf-mixed-commutator-tangent`). Proved in final packet: 0. Retired: 1.
Remaining assigned holes: 0. Added holes: 0. Split off: 0.

Also retired the one existing hole in
`AlgebraicGeometry.GeneralLinearGroup.exists_tangentMatrixSubmodule_differential`
(node `lem-wf-lie-algebra-derivation-bracket`) by withdrawing its unreferenced Sheaf module.
No sorries remain in delivered Lean files; there are no retained or new Lean declarations.
These are two pruned holes, not two newly proved theorems.

Before discovering the retirement route, a full proof of the assigned conjunction was written
and compiled cleanly in 40.3 seconds from the existing intrinsic tangent-bracket API. That proof
is not the final delivery, and is not counted as a proved hole here. The final packet follows
the brief's requirement to withdraw an unnecessary item.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.MixedCommutatorTangent` and
`Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket`, including the private import of the former
in the latter. No remaining module imports either file. The Sheaf declarations are no longer
needed; the DAG nodes now point at their adopted upstream twins.
Both original DAG mathematical statements and all adopted source declarations remain in place. No
upstream dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The generic brief described this as a proof item; the live queue marks it for retirement.
The initial targeted searches missed the completed adopted source modules at
WeilConjectures.AlgebraicGeometry.MixedCommutatorTangent and
WeilConjectures.AlgebraicGeometry.MatrixSubgroupLieBracket. The source consumer theorem is
stronger (all fields); the source mixed-commutator theorem has a smaller conjunction than the
old Sheaf statement. We do not change either source statement or claim exact signature equality.
The consumer's own absence of importers makes withdrawal of both Sheaf modules valid.
The earlier pending-consumer condition in the retirement audit no longer applies to the
current import graph. The retirement rule requires DAG attachments to point at the upstream twins
rather than be cleared; the packet now does so. No source-library deletion, forced adaptation,
new statement, new node, or target change is involved.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
