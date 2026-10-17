# AlgebraicGeometry.ProEtale.CondensedRing.scalar_mate_counit

## Reason

Repair the duplicate-statement return of 07d5a89eac. The normalized item cannot
import ScalarCounitModel, which already reaches it through TensorPresentation and
PullSquare. Relocate the complete existing scalar mate calculation into the item,
remove its former copies from ScalarCounitModel, and make ScalarCounitModel import
and reuse the two shared entry points. This is an atomic move with no duplicated
statements, no new holes, and no change to a data definition or an existing public
signature. All moved generic helpers and cache instances remain private.

ScalarCounitModel is unclaimed. Its public theorem, its tensor-specific private
helpers and their proofs stay unchanged. Only the moved proofs and their redundant
imports are removed. This is an unclaimed-module repair, not a forced adaptation.

## Old

In `Sheaf.Paper.IntegralResidueScalarCounitModel`:

```lean
private theorem restrict_pull_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y))
      (.up ℤ)) :
    (residueExchangeRestrictPullIso ℓ E f).hom.app (DerivedCategory.Qh.obj N) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeUpperStarCounit
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app N) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategoryFactorsh.hom.app
        ((((f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧).mapHomotopyCategory
          (.up ℤ)).obj N) =
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((Mod.comap
          (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategoryFactorsh.hom.app N) ≫
        (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app
          (((Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app N)

private theorem scalar_mate_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
      (residueExchangeReductionCounit ℓ E X).app
          ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj P) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app P) ≫
      ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj P))
```

Their complete private prerequisites occur in the same module's ProofCalculations
section. The normalized item's existing public theorem has one sorry.

## New

In `Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized`:

```lean
theorem restrict_pull_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y))
      (.up ℤ)) :
    (residueExchangeRestrictPullIso ℓ E f).hom.app (DerivedCategory.Qh.obj N) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeUpperStarCounit
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app N) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategoryFactorsh.hom.app
        ((((f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧).mapHomotopyCategory
          (.up ℤ)).obj N) =
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((Mod.comap
          (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategoryFactorsh.hom.app N) ≫
        (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app
          (((Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app N)

theorem scalar_mate_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
      (residueExchangeReductionCounit ℓ E X).app
          ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj P) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app P) ≫
      ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj P))
```

The proofs and complete private prerequisites are moved unchanged, with the old
copies removed in the same delivery. ScalarCounitModel has a proof-only import of
the item. The normalized theorem is proved by postcomposition and cancellation.
No new mathematical lemma is assumed and no target meaning changes.

## Users

The complete downstream set was checked with tools/downstream.py for both modules.
The only external textual user of the normalized theorem is PullFlatModelComparison;
the only external textual user of integralResidue_scalarCounit_model is
ScalarGeometryBridge. Neither needs adaptation. The helper users are now the item
and ScalarCounitModel, with identical elaborated propositions. All downstream
statements keep their meaning because no definition or existing public signature changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResiduePullFlatModel | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResiduePullFlatModelComparison | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized | A2 | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResiduePullSquare | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | unchanged statements and definitions; imports shared helpers |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | B4 | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorRouteModel | A4 | unchanged public theorem statements and definitions |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | unchanged public theorem statements and definitions |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | unchanged public theorem statements and definitions |
| TargetsCheck | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Basic | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | unchanged public theorem statements and definitions |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | unchanged public theorem statements and definitions |

## Status

landed 20261017T121123-L-399885 2026-10-17 (merge of deliver/A2/Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized)
