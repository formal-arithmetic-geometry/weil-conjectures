## What changed

The change record is `coord/changes/R1-point-sections-finite-reduction-bounded.md`.

Closed `WeilConjectures.point_sections_finite_reduction_bounded`. The proof resolves bounded-above module objects by bounded-above termwise flat complexes, computes the selected derived tensor on that resolution, and proves the mixed tensor remains bounded above. Its sheaf component uses `SheafOfModules.ringedTensorCohomologicalBounds`; the selected ringed scalar-extension witness is identified with `pointFiniteReductionSheafTensor`. Exact point sections transfer the upper bound to the module side. Added proof-only imports and a separate fully proved generic module-bound support theorem.

## Proved and sorry left

Proved: `WeilConjectures.point_sections_finite_reduction_bounded`.

Sorry left: `WeilConjectures.point_sections_finite_reduction_iso`, `WeilConjectures.point_sections_finite_reduction_complex`.

## No longer needed

None. No declared dependency or imported module was pruned.

## Where the brief, the DAG or earlier work was wrong

The boundedness route in the existing DAG omitted the already available generic ringed scalar-extension upper-bound theorem and the exact-functor upper-bound API. The delivered proof uses those declarations and records the ringed bound node as an additional proof dependency.

## New nodes

`lem-trf-point-sections-finite-reduction-module-bound` records the fully proved generic
module-side boundedness helper in `Sheaf.Paper.PointSectionsFiniteReductionModuleBound`.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
