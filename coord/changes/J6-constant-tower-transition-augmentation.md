# AlgebraicGeometry.ProEtale.constantTowerTransitionAugmentation

## Reason

The original inverse-of-composite construction was a compiler hot spot. The complete
proof compiled, but the combined delivery compile and axiom probe exceeded 60 seconds.
Construct the inverse of the zeroth classical comparison first and then the inverse
of the unbounded/classical comparison. Mathlib's `CategoryTheory.Iso.trans_symm`
is proved by `rfl`, so this is the same isomorphism, with the same hom and inverse.
The complete revised file with the delivery probe compiled in 44.0 seconds after
sharing repeated functor terms and using a proved private augmentation equation
to keep the construction locally irreducible during the final proof.

## Old

```lean
noncomputable def constantTowerTransitionAugmentation
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) f).obj F ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj F)) :=
  ((lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedZeroIsoSelf.app F).symm
```

## New

```lean
noncomputable def constantTowerTransitionAugmentation
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) f).obj F ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj F)) :=
  let L := lowerStar (ModuleCat.{u + 1} A) f
  (L.rightDerivedZeroIsoSelf.app F).symm ≪≫
    (L.homologyRightDerivedFunctorObjSingleFunctorIso F 0).symm
```

## Users

`tools/downstream.py Sheaf.Paper.ConstantTowerTransition --uses
AlgebraicGeometry.ProEtale.constantTowerTransitionAugmentation` found 40 downstream
modules and only one module mentioning the declaration: the item itself. No consumer
requires adaptation. The unchanged meaning follows uniformly from `Iso.trans_symm`
(definitional equality), including occurrences under the unchanged target statement.
Current claim holders are recorded below; no other module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ConstantTowerTransition` | J6 | Own theorem proves the same square; both augmentation maps are definitionally unchanged. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | No direct use of the augmentation; all statements retain identical meaning by definitional equality. |

## Status

landed 20261020T211745-L-3497378 2026-10-20 (merge of deliver/J6/Sheaf.Paper.ConstantTowerTransition)
