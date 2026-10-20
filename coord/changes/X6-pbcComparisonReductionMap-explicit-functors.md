# AlgebraicGeometry.ProEtale.pbcComparisonReductionMap

## Reason

Make the existing functor type or functor arguments explicit to prevent costly inference through derived functor compositions. These elaboration annotations preserve the construction and its inferred signature judgmentally. No target meaning changes.

## Old

```lean
noncomputable def pbcComparisonReductionMap (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ⟶
      pbcFixedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv)).natTrans
```

## New

```lean
noncomputable def pbcComparisonReductionMap (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ⟶
      pbcFixedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  ((mateEquiv
    (G := (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory)
    (H := (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv)).natTrans
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.NormalizedOriginComparisonCoherence | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.WitnessCompatibility | X6 | No adaptation: same functor and canonical comparison. |

## Status

landed 20261020T221402-L-4181465 2026-10-20 (merge of deliver/X6/Sheaf.Paper.WitnessCompatibility)
