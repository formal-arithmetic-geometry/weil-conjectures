## What changed

Completed `AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_cover_and_point_topology`
without changing its statement or public imports. The proof follows the four current DAG
steps. It chooses the atlas from `E.property`, applies
`space_atlas_open_refinement_pullback`, and takes the coproduct in `Over S`. Mathlib's
`isColimitOfHasCoproductOfPreservesColimit` transfers the coproduct cocone to schemes;
`Over.w` gives each required factorization through the chosen affine base open.

The topology is explicitly `TopologicalSpace.coinduced (schemePointMap w) inferInstance`.
`exists_atlas_point_comparison` proves its independence by equality of open-set predicates.
`exists_atlas_test_open_subsets` supplies descent of openness for continuity and the
inverse image of an étale image for openness. The open range follows from `IsOpenMap`.
All three existing dependencies are imported privately. The assembly compiled cleanly
in 3.7 seconds through `lcompile.py`; redundant explicit Mathlib imports were then
removed because their declarations are already supplied by the public import closure. No definition uses a chosen
witness of an unproved existence theorem: the atlas and refinement witnesses are unpacked
only inside the theorem proof, and the topology is explicitly constructed there.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_cover_and_point_topology`
(node `lem-a1-space-affine-etale-cover`). There are zero holes left in the item and
zero holes added. This proves the item from the existing, separately stated atlas
refinement, atlas comparison, and scheme-test subset theorems; their proofs remain
outside this delivery.

## No longer needed

Removed the direct private imports
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`, and
`Sheaf.AlgebraicGeometry.AlgebraicSpace`. Their facts are already encapsulated in the
three planned atlas lemmas or supplied through `AlgebraicSpacePointClasses`.
No DAG proof dependency is pruned: every dependency in the current four-step plan is
used. In particular the fibre-product point lemma remains needed by the atlas lemmas;
its module is not withdrawn. No modules or nodes are withdrawn, and no unit route is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The existing declaration docstring expands the same
argument that the current DAG packages into the three atlas lemmas. The proof uses
those stated lemmas rather than reproving their underlying scheme geometry.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
