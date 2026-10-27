# scalarExtension_preservesKFlat

## Reason

Factor the existing proof through a private helper taking only the ordinary extension
functor and its prescribed object and map equations. The adjunct-factorization proof
has exactly these data; constructing a full homotopy-derived package is unnecessary.
The public statement and its visibility remain unchanged. This is a proof refactor,
with no changed public definition and no new hole.

## Old

```lean
theorem scalarExtension_preservesKFlat (s : ScalarDerivedPair a)
    (P : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
      ((scalarComplex s.extension s.extension_additive).obj P)
```

## New

```lean
theorem scalarExtension_preservesKFlat (s : ScalarDerivedPair a)
    (P : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
      ((scalarComplex s.extension s.extension_additive).obj P) := by
  have := s.extension_additive
  exact kflatOfScalarExtensionIdentification a s.extension
    s.extension_obj s.extension_map P hP
```
The private helper is the original balanced-cancellation proof with the ordinary fields
passed directly. It has no derived-category parameters.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ScalarHomExtensionKFlat | unclaimed | Public theorem signature and meaning unchanged; no adaptation. |
| Sheaf.Algebra.Homology.ScalarHomTensorComparison | unclaimed | Public theorem signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | unclaimed | Public theorem signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | Public theorem signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PrescribedScalarTensorComparison | unclaimed | Public theorem signature and meaning unchanged; no adaptation. |

## Status

landed 20261025T002454-L-3110664 2026-10-25 (merge of deliver/C5/Sheaf.Paper.QuotientOperationAdjointFactorizations)
