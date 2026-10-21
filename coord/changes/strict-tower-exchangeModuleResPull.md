# AlgebraicGeometry.Scheme.exchangeModuleResPull

## Reason

The previous expressions repeatedly unfold concrete coefficient transports while checking the mate cube. Share the ordinary isomorphism and the generic derived-unit normalization to keep single-file compilation within the existing limit. The comparison components, normalization equation and all existing signatures stay the same. New generic helpers construct the same canonical unit and equation; no arbitrary data is selected. The target statements and every downstream statement retain their mathematical meaning. Definitions used by targets should receive the normal independent statement review.

The additional public MapDerivedCategoryMate import supports the exact-descent definition. Supporting constructions are exchangeOrdinaryResPull, exchangeDerivedUnit and ExchangeDerivedPushNormalized in the same module.

## Old

```lean
def exchangeModuleResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePull f ⋙ exchangeTowerModuleRes d U ≅
      exchangeTowerModuleRes d V ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))
      (proEtaleRingRestrictionPullbackInv_isIso f
        (exchangeConstantRing V A) (d.completedRing V)
        (exchangeConstantRing U A) (d.completedRing U)
        (exchangeScalar d V) (exchangeScalar d U)
        (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f)))).symm
```

## New

```lean
def exchangeModuleResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePull f ⋙ exchangeTowerModuleRes d U ≅
      exchangeTowerModuleRes d V ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  NatIso.ofComponents
    (fun M ↦ Functor.isoWhiskerLeft M (exchangeOrdinaryResPull d f)) (by
      intro M N a
      apply NatTrans.ext
      funext n
      exact (exchangeOrdinaryResPull d f).hom.naturality (a.app n))
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
