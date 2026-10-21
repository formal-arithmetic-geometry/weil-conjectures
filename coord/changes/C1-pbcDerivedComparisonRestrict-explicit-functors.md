# AlgebraicGeometry.ProEtale.pbcDerivedComparisonRestrict

## Reason

Make the existing functor type or functor arguments explicit to prevent costly inference through derived functor compositions. These elaboration annotations preserve the construction and its inferred signature judgmentally. No target meaning changes.

## Old

```lean
noncomputable def pbcDerivedComparisonRestrict (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pbcComparisonRestrict T φ) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
```

## New

```lean
noncomputable def pbcDerivedComparisonRestrict (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} S) T)
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := comparisonUpperStar (ModuleCat.{u + 1} S) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      (G := Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} R) T)
      (pbcComparisonRestrict T φ) ≪≫
      Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (comparisonUpperStar (ModuleCat.{u + 1} R) T)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.LevelwiseAdicTruncations | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.NormalizedOriginComparisonCoherence | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.WitnessCompatibility | C1 | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | No adaptation: same functor and canonical comparison. |

## Status

landed 20261021T003502-L-1642808 2026-10-21 (merge of deliver/C1/Sheaf.Paper.WitnessCompatibility)
