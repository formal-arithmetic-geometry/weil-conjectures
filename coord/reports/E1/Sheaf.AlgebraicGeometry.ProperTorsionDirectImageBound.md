## What changed

Filled the proof of `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le`.
The proof uses proper base change, geometric-point conservativity, the finite-type torsion
cohomological-dimension theorem, and exact geometric-point sections. Added proof-only imports
for `WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension` and
`WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived`.

## Proved and sorry left

The target theorem is proved. No `sorry` remains in the delivered module and no new holes were added.

## No longer needed

No proof dependency was removed. The empty-fibre case is subsumed by the finite-type
cohomological-dimension theorem, which accepts the bottom dimension bound directly.

## Where the brief, the DAG or earlier work was wrong

The proof plan's separate empty-fibre argument and exact-dimension case split are unnecessary:
the existing finite-type torsion cohomological-dimension theorem handles arbitrary schemes with
a dimension upper bound, including the empty scheme.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
