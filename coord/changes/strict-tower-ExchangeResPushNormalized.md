# AlgebraicGeometry.Scheme.ExchangeResPushNormalized

## Reason

The previous expressions repeatedly unfold concrete coefficient transports while checking the mate cube. Share the ordinary isomorphism and the generic derived-unit normalization to keep single-file compilation within the existing limit. The comparison components, normalization equation and all existing signatures stay the same. New generic helpers construct the same canonical unit and equation; no arbitrary data is selected. The target statements and every downstream statement retain their mathematical meaning. Definitions used by targets should receive the normal independent statement review.

The additional public MapDerivedCategoryMate import supports the exact-descent definition. Supporting constructions are exchangeOrdinaryResPull, exchangeDerivedUnit and ExchangeDerivedPushNormalized in the same module.

## Old

```lean
def ExchangeResPushNormalized {U V : Scheme.{t}} (f : U ⟶ V)
    (e : d.towerPush f ⋙ exchangeTowerRes d V ≅
      exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f) : Prop :=
  ∀ C : CochainComplex (exchangeTowers U (d.completedRing U)) ℤ,
    (exchangeTowerRes d V).map
        (exchangeTowerDerivedUnit f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) C) ≫
      e.hom.app (DerivedCategory.Q.obj C) ≫
      (exchangeConstantPush (A := A) f).map
        ((exchangeTowerModuleRes d U).mapDerivedCategoryFactors.hom.app C) =
    (exchangeTowerModuleRes d V).mapDerivedCategoryFactors.hom.app
        (((d.towerModulePush f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (exchangeModuleResPush d f) (.up ℤ)).hom.app C) ≫
      exchangeTowerDerivedUnit f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)
        (((exchangeTowerModuleRes d U).mapHomologicalComplex (.up ℤ)).obj C)
```

## New

```lean
def ExchangeResPushNormalized {U V : Scheme.{t}} (f : U ⟶ V)
    (e : d.towerPush f ⋙ exchangeTowerRes d V ≅
      exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f) : Prop :=
  ExchangeDerivedPushNormalized (d.towerModulePush f)
    (exchangeTowerModulePush f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModuleRes d V) (exchangeTowerModuleRes d U) (exchangeModuleResPush d f) e
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | N2 | Uses the shared definitions in its proofs; same components and normalization. No statement change. |
| Sheaf.Paper.CompletedProjectionCoherence | D2 | Imports the module transitively; no direct use of these names. No adaptation required. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | Imports the module transitively; no direct use of these names. No adaptation required. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | Imports the module transitively; no direct use of these names. No adaptation required. |
| Sheaf.Paper.ProEtaleConstantReductionTower | T4 | Imports the module transitively; no direct use of these names. No adaptation required. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Imports the module transitively; no direct use of these names. No adaptation required. |

`tools/downstream.py --uses exchangeModuleResPull exchangeResPull ExchangeResPushNormalized` lists only the item as a direct user of each changed name. No adopted source-library file is changed.


## Status

landed 20261021T012414-L-2186301 2026-10-21 (merge of deliver/N2/Sheaf.Paper.StrictTowerExchangeMateNormalization)
