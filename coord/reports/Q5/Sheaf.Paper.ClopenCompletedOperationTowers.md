## What changed

Proved `restriction_exact`, `goodRestriction_property`, and `roos_restriction` in
`Sheaf.Paper.ClopenCompletedOperationTowers`. Exactness uses the clopen restriction
and scalar transport equivalence. The good-complex property transports flatness
and K-flatness through the normalized coefficient isomorphism. The Roos comparison
uses preservation of countable products and the additive strict-cone comparison,
with both required projection formulas proved.

Private proof imports add ring-isomorphism tensor transport, additive Roos
comparison, strict shifted-cone coordinates, and the homological-complex functor
API. Local reducibility settings keep the coefficient and derived constructions
behind their interfaces. Public declaration signatures, definition bodies, and public imports are unchanged.
The delivered file compiled cleanly in 39.8 seconds through `lcompile.py`.

## Proved and sorry left

Closed three of the four original holes, with no holes added:

- `WeilConjectures.ClopenCompletedOperations.restriction_exact`.
- `WeilConjectures.ClopenCompletedOperations.goodRestriction_property`.
- `WeilConjectures.ClopenCompletedOperations.roos_restriction`.

The remaining hole is
`WeilConjectures.ClopenCompletedOperations.clopen_completed_operation_towers`,
node `lem-pur-clopen-completed-operation-towers`.

## No longer needed

Removed unused private imports from the item: 
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`,
`WeilConjectures.CategoryTheory.NatTransFromResolvingClass`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`, and
`Mathlib.CategoryTheory.Localization.Predicate`.
The Roos proof no longer uses node `lem-pur-clopen-strict-tower-roos-equivalence`:
it uses the generic additive comparison and shifted-cone coordinates instead.
That proof dependency is removed from the item node. The module
`Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence` remains a public import
for the existing interface, so no module is withdrawn or claimed pruned.
The remaining theorem retains the other nodes of its original proof plan.

## Where the brief, the DAG or earlier work was wrong

The planned clopen strict-tower comparison can be replaced, for the Roos helper,
by the already proved generic additive Roos comparison. The completed coefficient
identification must also be transported through the commutative-ring forgetful
functor before using its flatness and K-flatness clauses. No mathematical
statement was changed.

The unfinished final theorem still requires the finite-level tensor and scalar
comparison formulas, their transition squares, and normalized derived descent.
Those constructions were investigated in the scratchpad, but are not submitted as
new dependencies or counted as closed holes. There are no new nodes, definition
repairs, or adaptations of other groups' modules in this delivery.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
