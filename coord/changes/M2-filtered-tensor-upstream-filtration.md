# CochainComplex.filteredTensor_graded_comparison

## Reason

Restore the quarantined item on the current upstream API. Importing the duplicate Sheaf
finite-filtration declarations alongside the upstream declarations fails with an environment
collision on `CategoryTheory.FilteredObject.restrictionSteps` in the existing importer
`Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement`. Importing the upstream extension
instead supplies the same restriction and graded-map API from its canonical source. No
statement or definition body is changed, except that the decreasing-step theorem is proved.

## Old

```lean
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
```

## New

```lean
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
```

## Users

The source-only downstream tool reports zero current library consumers because the item and its
consumers are quarantined. Searching the quarantine archive finds the following direct consumers.
The first is restored unchanged in this delivery and compiles against the repaired item. The
others remain quarantined; their named API is supplied unchanged by the upstream import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FilteredTensorGradedComparison | M2 | Uses the upstream restriction/graded-map API; all declaration signatures preserved. |
| Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement | unclaimed | Restored verbatim; compiled with the item in import order. |
| Sheaf.Algebra.Homology.FilteredTensorLocalization | unclaimed | Quarantined; no source change needed for this API migration. |
| Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence | unclaimed | Quarantined; no source change needed for this API migration. |

The target statements and the mathematical meaning of their definitions do not change.

## Status

landed 20261020T230807-L-613194 2026-10-20 (merge of deliver/M2/Sheaf.Algebra.Homology.FilteredTensorGradedComparison)
