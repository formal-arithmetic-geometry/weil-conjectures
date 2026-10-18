## What changed

Filled `CategoryTheory.BigradedExactCouple.finiteCycle_formula` with the finite-cycle
induction. The proof identifies the recursive image-prefix maps with
`incomingAlphaIter`, proves the projection compatibility by induction, and then
proves the cycle-subobject formula using the derived-couple kernel identity,
pullback universal properties, and image factorization. The proof-only imports were
pruned to `all WeilConjectures.CategoryTheory.FinitePageImageLift`,
`WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities`, and the subobject
limits support.

## Proved and sorry left

The declaration `CategoryTheory.BigradedExactCouple.finiteCycle_formula` is proved.
No `sorry` remains in the delivered module and no new holes were added.

## No longer needed

The proof does not need the separate Sheaf re-export imports, the ordinary
`WeilConjectures.CategoryTheory.ExactCoupleConvergence`, `DerivedCoupleExact`, or
ordinary `FinitePageImageLift` imports, because the all-imported upstream finite
page module supplies the recursive image-prefix and iterate declarations. No DAG
nodes are pruned; all five declared proof dependencies are used through those
interfaces.

## Where the brief, the DAG or earlier work was wrong

The earlier source layout had a `derived_f` helper referenced by an intermediate
proof sketch; the current upstream source exposes the needed `DerivedMaps.f_comm`
equation instead. The proof uses that equation directly. The upstream private
iterate recurrence is accessed through the required `import all` form.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
