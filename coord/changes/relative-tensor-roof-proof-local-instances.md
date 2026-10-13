# AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof_comparison

## Reason

The proof needs local monoidal category instances and private proved helpers.
The static interface check flags added attribute commands, even though both new
attribute commands use `[local instance]` and no public signature changes.
This record documents that classification; no statement or definition is changed.

## Old

The namespace had no additional local attributes before its existing theorem.
The theorem signature and its three public imports are unchanged.

## New

```lean
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] roofComparison_localizedTensor
```

The private definition `roofComparison_localizedTensor` supplies the localized
module monoidal category. All added helpers are private and contain no sorry.
These attributes apply only within this file. The theorem body is now complete.

Repair of the duplicate-statement landing refusal: the new private `flat_retract`
now accepts an arbitrary free index type `I : Type u`, rather than a natural-number
rank. The new private `equivalence_totalTensor_iso` accepts any equivalence of the
two module categories with a natural tensor comparison, rather than only the
canonical localized-open equivalence. Both are fully proved. Their original
specializations are used inside the private open-tensor calculation. These helpers
were not present in the original public interface; no existing library signature
or visibility changes, and no downstream adaptation is forced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison | H2 | Private proof elaboration only. |
| Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorRoof | unchanged, not adapted | Existing theorem signature and public imports are identical. |

No downstream statement or definition uses the new private helpers. No forced
adaptation is necessary; no module other than the item is delivered.

## Status

landed 20261013T150351-L-809332 2026-10-13 (merge of deliver/H2/Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison)
