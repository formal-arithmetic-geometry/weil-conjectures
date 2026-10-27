## What changed

Filled `AlgebraicGeometry.proper_dim_zero_finite_over_field` in
`Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField` without changing its signature.
Install the given structure morphism as `Y.Over (Spec k)`, obtain locally finite type
and quasi-compactness from `proper_basic`, and apply the existing proved
`isAffine_and_isFinite_of_dim_le_zero`. Finally apply `Scheme.Hom.finite_appTop`,
transport finiteness across `Scheme.ΓSpecIso`, and use `RingHom.finite_algebraMap`
with exactly `f.ΓAlgebra`. This implements all three original DAG proof steps.
No imports, definitions, statements, attributes, or other modules change.
The compile server checked the proof in 6.9 seconds; the final delivery check
also verifies the standard-axiom bound for the completed declaration.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.proper_dim_zero_finite_over_field`
(node `lem-pc-dim-zero-finite-over-field`). Holes closed: 1. Holes added: 0.
No sorry remains in the delivered module; no result is split off.

## No longer needed

None. Both existing proof-only imports are used: `ProperBasic` supplies the
finite-type hypotheses and `DimZeroFiniteOverField` supplies affineness and
finiteness. All three recorded proof dependencies remain needed, including the
Mathlib leaf `lem-weil-pbc-finite-over-field-affine-finite-dim`. No node or module
is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The finite-type dimension-zero dependency is
already completely proved, so no intermediate theorem is necessary. Searches
with LeanFinder and Loogle, the server grep service, and local `rg` confirm the
Mathlib finite-affine criterion and `Scheme.Hom.finite_appTop`; they provide the
last step rather than a direct replacement for the full theorem. The Stacks
Tag 06LH proof includes the finite-type algebraic case used here. The proof
also includes the empty scheme, since no nonempty or nontrivial global-section
hypothesis is introduced. The algebra structure in the conclusion is unchanged.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
