## What changed

Retained the complete proof of
`AlgebraicGeometry.fibre_dimension_after_base_change` in
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`, with its statement and
docstring unchanged. Mathlib's fibre pullback square gives the compatible
isomorphism. A proved private helper reduces the dimension assertion to an affine
chart and the existing tensor-product field-extension dimension theorem; a second
proved private helper identifies the fibre point using the fibre inclusion.

Repaired return 5d2bdf5da: removed the duplicate private
`AlgebraicGeometry.localDim_openEmbedding`. Its existing declaration in
`Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension` was private;
made that existing lemma public in place, with identical binders, conclusion and
proof, and added its explanatory docstring. The item imports that module privately
and uses the existing lemma. The adapted module was unclaimed. No consumer edits,
new statements, new definitions, or target signature changes are needed.

Kept the removal of the unused public import
`Sheaf.AlgebraicGeometry.BaseChangeConventions`. Change records:
`coord/changes/N3-fibre-dimension-unused-conventions-import.md` and
`coord/changes/N3-shared-localDim-openEmbedding.md`.
Updated the item's node proof text and origin to record the actual Lean route;
its proof dependencies and the unit route remain unchanged.

Verification: both changed modules compile cleanly. The unchanged consumers
`Sheaf.AlgebraicGeometry.RationalPointLocalDimensionBaseChange`,
`Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension`, and
`Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound` compile against the changed
modules (2.2 s, 3.1 s, and 10.4 s). `#print axioms` for both the fibre theorem and
the shared open-embedding lemma reports exactly `propext`, `Classical.choice`, and
`Quot.sound`. Verification-only sources were removed from the delivered set.
Empty pullbacks are vacuous because an input point is required; the affine proof
imposes no closed-point or rational-point assumption.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.fibre_dimension_after_base_change`
(node `lem-sc-fibre-dimension-after-base-change`).

Holes added: 0. Holes remaining in the item: 0. Split-offs: 0.
The adapted existing module also has 0 holes. Both remaining private helpers are
proved. The shared lemma was already proved and is reused, not counted as a new
hole closed. This is a proof, not a decomposition.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.BaseChangeConventions`. Neither
`baseChange_fiber` nor `baseChange_iterated` is used: Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback` supplies the pasting directly.
The item's duplicate private `localDim_openEmbedding` is removed; its existing
proof in `Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension` is
now shared through a proof-only import.

No declared proof dependency is pruned: residue fields, scheme fibres, fibre
products, pullback pasting, locally-finite-type base change, local topological
dimension, and the affine field-extension dimension theorem are all used.
No DAG node or module is withdrawn. The conventions module still has other users;
its global unreachability is not claimed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated an existing private lemma word for word. The
repair exposes and imports the original instead of repeating its proof. Merely
adding the import would not have worked because of the original's private
visibility. The original mathematical proof plan and fibre theorem statement
need no correction. The retained report's consumer list was outdated; the change
record now records the current two transitive importers of the item and the
actual consumer compiles.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
