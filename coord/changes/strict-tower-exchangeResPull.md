# AlgebraicGeometry.Scheme.exchangeResPull

## Reason

The previous expressions repeatedly unfold concrete coefficient transports while checking the mate cube. Share the ordinary isomorphism and the generic derived-unit normalization to keep single-file compilation within the existing limit. The comparison components, normalization equation and all existing signatures stay the same. New generic helpers construct the same canonical unit and equation; no arbitrary data is selected. The target statements and every downstream statement retain their mathematical meaning. Definitions used by targets should receive the normal independent statement review.

The additional public MapDerivedCategoryMate import supports the exact-descent definition. Supporting constructions are exchangeOrdinaryResPull, exchangeDerivedUnit and ExchangeDerivedPushNormalized in the same module.

## Old

```lean
def exchangeResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerPull f ⋙ exchangeTowerRes d U ≅
      exchangeTowerRes d V ⋙ exchangeConstantPull (A := A) f :=
  (Functor.mapDerivedCategoryCompIso (d.towerModulePull f)
    (exchangeTowerModuleRes d U)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (exchangeModuleResPull d f) ≪≫
  Functor.mapDerivedCategoryCompIso (exchangeTowerModuleRes d V)
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
```

## New

```lean
def exchangeResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerPull f ⋙ exchangeTowerRes d U ≅
      exchangeTowerRes d V ⋙ exchangeConstantPull (A := A) f :=
  Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d f)
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
