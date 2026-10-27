## What changed

Proved `AlgebraicGeometry.fppfSchemeDataSheafGluing` with its original signature.
The proof uses the sheaf descent datum already stored in `SchemeCoverDescentDatum`.
`setSheafCoverDescent` and Mathlib's fully faithful essential-image lift provide the
global sheaf functor and its natural local comparison. An explicit bijection between
maps to the local scheme over the base and pairs of a map to the covering member
and a global section provides the product representation. Its inverse, naturality,
and projection formulas are proved. Fully faithful cancellation of
`schemeCoverDescentForget` gives the final natural isomorphism and its specified
component equation.

Validation: the complete module compiled cleanly through `lcompile.py` in 13.7 seconds,
with no warnings or errors and zero textual `sorry`.

Added only proved private helpers in the assigned module. Existing public imports,
the theorem signature, and definitions in other modules are unchanged. Updated the
node's proof route and removed the unused affine-refinement tool approval.

## Proved and sorry left

Closed: `AlgebraicGeometry.fppfSchemeDataSheafGluing`
(node `lem-trf-fppf-scheme-data-sheaf-gluing`), the item's one original hole.
Added: none. Remaining in the delivery: none. This is a proof, not a decomposition.
The proof uses the existing `CategoryTheory.setSheafCoverDescent` declaration.

## No longer needed

Removed the private imports `Sheaf.AlgebraicGeometry.FppfAffineRefinement` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`. The latter's module
is unnecessary for a proof using only set-valued slice sheaves. Added the private
Mathlib product-functor import `Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes`.

The proof no longer needs `lem-pc-fppf-affine-refinement` (and its module),
`def-weil-pbc-fpqc-covering`, or `lem-weil-pbc-fpqc-representable-descent`:
local objects are already sheaves in the datum. It also does not need the
fibre-product construction `def-pc-fibre-product` as a proof dependency, nor
`lem-pc-representable-unique`: the explicit slice bijection supplies product
representability and categorical full faithfulness supplies the comparison.
These are removals from this proof's dependencies, not requests to delete shared
nodes or modules. The statement dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The planned representable-sheaf and transition constructions were redundant with
`SchemeCoverDescentDatum.data` and `.representation`. The final comparison can be
constructed by cancelling the fully faithful induced functor, with no separate
scheme-Yoneda reconstruction. The unit `sk-i-curve-zero` has no realized entries
for this node, and its route is unchanged.

The explicit product bijection uses canonical maps with identity underlying scheme
arrows between objects with propositionally equal structure morphisms. Keeping
these maps explicit is necessary: the objects need not be definitionally equal.
The same formulas work for empty schemes, empty local section sets, repeated
indices, and an empty covering index set; no nonemptiness hypothesis is used.

Searches used LeanFinder for slice/product representability, Loogle for fully
faithful preimage isomorphisms, and grep for representability and categorical
lifting. Mathlib's existing explicit product functor and essential-image lift
supply the shorter route. No new public statements or nodes were needed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
