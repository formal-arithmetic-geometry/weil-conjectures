## What changed

Proved `IntegralLatticeCubical.partitionBoundaryExpansion` from the new proof-only import
`Sheaf.AlgebraicTopology.CubicalPartitionDifferentialFaces`. The existing statement and both
face definitions are unchanged. All inversion-count, parity, local face, index-bijection,
position-count, cancellation, and empty-case arguments are proved in the item module.

The new lemma isolates the total tensor differential expanded into four uncancelled face
terms, indexed by a removed direction and a partition of the remainder. It keeps the
original coefficients; it asserts none of the shuffle-sign identities, middle-face
cancellation, bijection clauses, or final outer-face formula of the item. Updated the
item node to follow this reduction and supplied the new node's source and complete proof
in words. No existing dependency module or public interface was changed.

Remote validation: the new expansion module compiled in 2.4 seconds; the final item
compiled in 5.0 seconds, with no errors or warnings. Checked that both existing face
definitions and the full original theorem signature are unchanged. The existing node
changes only `proof`, `proof_deps`, and `proof_origin`.

## Proved and sorry left

Closed the original hole in `IntegralLatticeCubical.partitionBoundaryExpansion`
(`lem-sfb-cubical-partition-boundary-expansion`). Its six local identities, both bijections,
and cancellation to the outer sum have complete Lean proofs.

Added one hole: `IntegralLatticeCubical.partitionDifferentialFaces`
(`lem-sfb-cubical-partition-differential-faces`), in its own new module. It is the raw
expansion/reindexing step of the original proof plan. This delivery is a decomposition:
one original hole closed, one strictly smaller hole added, net zero. No other holes are
left in the delivered files, and no definition or private helper contains a hole.

## No longer needed

No existing imports or modules are pruned. The original contraction and tensor-product
nodes remain needed by the new differential-expansion lemma. The item's direct proof
now depends on that lemma; the former direct dependencies are retained transitively.
All statements and steps of the unit route remain in place.

## Where the brief, the DAG or earlier work was wrong

The DAG calls each original step elementary, but the first expansion requires working
through Mathlib's bundled total-complex inclusions, zero-degree boundaries, finite sums,
and the two face reindexings. That step is now an explicit separate obligation; no new
mathematical assumption is made. The current blueprint paragraph (3) only locates this
branch of the route and does not state the cubical calculation. The existing source's
agent-written status and WANTED external reference are preserved.

The new statement was checked on empty directions (both degree-zero boundaries and the
outer sum vanish), rank zero (only that case exists), and a singleton direction (the two
original vertex-edge/edge-vertex partitions supply its two raw terms). The erasure and
insertion arguments explicitly derive absence of the removed coordinate from both
remaining parts; they do not assume the removed direction belongs to either part.

## New nodes

`lem-sfb-cubical-partition-differential-faces`: the uncancelled tensor-boundary expansion,
original proof-plan steps 1–2. It uses the same cubical boundary and Mathlib tensor product,
with no sign simplification or middle-term cancellation. Semantic, type-name, and source
searches found the generic total-differential API but no cubical specialization. Blueprint
search returned no cubical node and ancestor lookup returned None, matching the existing
item's provenance. No change record is required: existing statements, definitions,
attributes, and public imports are unchanged.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
