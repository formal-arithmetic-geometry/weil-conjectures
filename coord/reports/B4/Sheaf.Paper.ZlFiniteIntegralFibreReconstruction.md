## What changed

Proved `WeilConjectures.ZlFibreReconstruction.finite_integral_fibre_roos`
without changing its statement or any public definition. The proof uses private,
fully proved generic helpers for the product-of-a-tower functor, additivity of
the recorded strict Roos functor, and finite-biproduct comparison. The existing
proved cone-coordinate helper is imported privately from
`Sheaf.Paper.IntegralAmbientOperationModels`; Mathlib supplies preservation of
finite biproducts by additive functors. Step 5 of the existing node now records
this route. All other steps, including the unit route, are retained.

## Proved and sorry left

Closed one of the item's two holes:
`WeilConjectures.ZlFibreReconstruction.finite_integral_fibre_roos`.
This includes invertibility, the coordinate reindexing isomorphism, commutation
with the actual `1-s`, the level projection identity, and the empty-fibre zero
objects and uniqueness assertion. Every new private helper is proved. The complete file compiled successfully.

One existing hole remains, unchanged:
`WeilConjectures.ZlFibreReconstruction.finite_integral_fibre_reconstruction`
(node `lem-zl-finite-integral-fibre-reconstruction`). Its existing seven-step
source proof remains in its docstring. No holes were added or split off.

## No longer needed

The strict finite Roos comparison needs countable products, with no exactness
hypothesis and no passage to the derived category. Thus Step 5 does not need
`lem-weil-strict-roos-comparison`. The unfinished reconstruction still needs
that node for its derived-limit identifications, so the node dependency is
retained. Removed private plan imports `Sheaf.Paper.FiniteCounitRestrictionTowers`,
`Sheaf.CategoryTheory.StrictRoosComparison`, and the redundant direct import
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`. The last module's
countable-product instances remain available through the public statement
imports. The first two modules remain dependencies of the unfinished
reconstruction plan in the DAG. No modules are withdrawn. No public imports
are removed.

## Where the brief, the DAG or earlier work was wrong

The strict chain-level finite comparison can be obtained by additivity and
Mathlib's canonical finite-biproduct comparison; derived-limit comparison is
unnecessary for this particular theorem. No statement is disputed or changed.
The primary reconstruction theorem is left unchanged as permitted for a module
with several holes. No new nodes or consumer adaptations are required.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
