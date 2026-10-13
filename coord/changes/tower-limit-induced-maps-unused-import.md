# CategoryTheory.tower_limit_induced_maps (unused public import)

## Reason

Remove an unused public import as required by stage-3 pruning. Neither the theorem's
signature nor either helper or proof uses exactness. All existing declaration signatures,
definitions, and target meanings remain identical. This change does not reopen any target
definition review.

## Old

```lean
public import Mathlib.Algebra.Exact.Basic
```

## New

The unused import is removed. `Mathlib.Algebra.Category.ModuleCat.Limits` remains public;
the two newly added proof dependencies are plain imports.

## Users

`tools/downstream.py Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps` lists the
following modules. Its sole direct importer, TowerLimitExactSurjectiveKernels, imports
this module privately and already publicly imports `Mathlib.Algebra.Exact.Basic` itself
(line 10). Thus it continues to obtain and export exactly the exactness API it used before;
no downstream signature, proof or definition depends on this removed import edge.
No module needs forced adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.Algebra.Homology.MittagLefflerLimitHomology | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.CategoryTheory.SurjectiveTowerLimitAcyclic | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.FlatModuleCompletion | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.LimitFlatModules | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlat | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlatOverBase | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.StrictHenselizationCompletionNoetherian | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.StrictHenselizationNoetherian | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |
| Sheaf.RingTheory.StrictHenselizationRegular | unclaimed | No adaptation or semantic change; direct importer retains its own public exactness import. |

## Status

landed 20261013T082421-L-1650733 2026-10-13 (merge of deliver/V4/Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps)
