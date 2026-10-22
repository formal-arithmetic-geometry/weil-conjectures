# SheafOfModules.ringIsoCochainMonoidal

## Reason

Avoid an expensive monoidal-instance search when elaborating the assigned complete proof.
The cached structure is the existing Mathlib total tensor. A private diagnostic compiled
both the original cache and the equality to the explicit constructor with proof `rfl`.
Thus the replacement is definitionally equal, including the tensor, associator and unitors. The companion structure cache now directly
names Mathlib's `monoidalCategoryStruct`; a private diagnostic `rfl` theorem checked its equality to
the original projection of the monoidal cache in a clean 22.0-second prefix compile.
The diagnostic theorem is omitted from the final source.
No source-library file changes, and no target statement or mathematical meaning changes.

## Old

```lean
noncomputable instance (priority := 2000) ringIsoCochainMonoidal
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategory (CochainComplex (scalarModules J A) ℤ) := inferInstance

noncomputable instance (priority := 2000) ringIsoCochainMonoidalStruct
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategoryStruct (CochainComplex (scalarModules J A) ℤ) :=
  (ringIsoCochainMonoidal A).toMonoidalCategoryStruct
```

## New

```lean
noncomputable instance (priority := 2000) ringIsoCochainMonoidal
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategory (CochainComplex (scalarModules J A) ℤ) :=
  HomologicalComplex.monoidalCategory (C := scalarModules J A) (c := .up ℤ)

noncomputable instance (priority := 2000) ringIsoCochainMonoidalStruct
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategoryStruct (CochainComplex (scalarModules J A) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (C := scalarModules J A) (c := .up ℤ)
```

## Users

The read-only downstream inventory lists twelve consumers. None refers to the cache by name;
they receive its instance through the same public import. The instance has the same name,
signature, priority and definitionally identical data, so no consumer adaptation is forced.
The companion `ringIsoCochainMonoidalStruct` was checked equal to the original projection
by a private `rfl` diagnostic theorem; its data are definitionally unchanged.
The public statement and all other existing data definitions remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingIsomorphismTensorTransport | P3 | Explicit equal cache constructors. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.CoefficientPointFlatKFlatComparison | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.ExternalRHomConePairing | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.ExternalRHomSignedCones | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.GlobalHomEvaluationFlatLift | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.PerAdicCommonStageTruncations | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Definitionally unchanged instances. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | K4 | Definitionally unchanged instances. |

## Status

landed 20261022T011908-L-3230116 2026-10-22 (merge of deliver/P3/Sheaf.Algebra.Homology.RingIsomorphismTensorTransport)
