# AlgebraicGeometry.Scheme.exchangeModuleResPull and exchangeModuleResPush

## Reason

The kernel checks the old whiskering square by unfolding associativity after the
completed coefficient sheaves have been inserted. Profiling measured about 19 seconds
in that definition alone. The delivery adds `exchangeWhiskerSquareIso`, whose return
type fixes the same parenthesization for abstract categories first. Its body is exactly
`Functor.whiskeringRight.mapIso`; the old and new comparison have the same maps and
are definitionally equal after unfolding the wrapper. No scalar map, functor,
adjunction, statement, universe or visibility of an existing declaration changes.

The proved K-injective helper uses an explicitly typed ordinary adjunction and
an abstract termwise adjunction lemma before registering the tower-specific
exactness instances. This prevents expensive instance search through the concrete
coefficient constructions. The full item then compiled in 34 seconds.

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

def exchangeModuleResPush {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePush f ⋙ exchangeTowerModuleRes d V ≅
      exchangeTowerModuleRes d U ⋙ exchangeTowerModulePush f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (proEtaleRingRestrictionDirectImage f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))
```

## New

```lean
def exchangeWhiskerSquareIso {C D E F : Type (t + 2)}
    [Category.{t + 1} C] [Category.{t + 1} D]
    [Category.{t + 1} E] [Category.{t + 1} F]
    {P : C ⥤ D} {Q : D ⥤ F} {R : C ⥤ E} {S : E ⥤ F}
    (e : P ⋙ Q ≅ R ⋙ S) :
    (Functor.whiskeringRight ℕᵒᵖ C D).obj P ⋙
        (Functor.whiskeringRight ℕᵒᵖ D F).obj Q ≅
      (Functor.whiskeringRight ℕᵒᵖ C E).obj R ⋙
        (Functor.whiskeringRight ℕᵒᵖ E F).obj S :=
  (Functor.whiskeringRight ℕᵒᵖ C F).mapIso e

def exchangeModuleResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePull f ⋙ exchangeTowerModuleRes d U ≅
      exchangeTowerModuleRes d V ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  (exchangeWhiskerSquareIso
    (P := proEtaleRingRestrictScalars (exchangeScalar d V))
    (Q := proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A))
    (R := proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
    (S := proEtaleRingRestrictScalars (exchangeScalar d U))
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

def exchangeModuleResPush {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePush f ⋙ exchangeTowerModuleRes d V ≅
      exchangeTowerModuleRes d U ⋙ exchangeTowerModulePush f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  exchangeWhiskerSquareIso
    (P := proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
    (Q := proEtaleRingRestrictScalars (exchangeScalar d V))
    (R := proEtaleRingRestrictScalars (exchangeScalar d U))
    (S := proEtaleRingModuleDirectImage f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A))
    (proEtaleRingRestrictionDirectImage f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))
```

The new public wrapper is documented and attached to the same existing blueprint node.
It constructs the ordinary whiskered isomorphism directly and contains no choice or hole.

## Users

`tools/downstream.py Sheaf.Paper.StrictTowerExchangeMateNormalization --uses
exchangeModuleResPull exchangeModuleResPush` finds only the item itself as a declaration user. It lists the
five transitive importers below; none mentions either definition. They keep all existing
interfaces and require no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | J3 | Same comparison; faster type checking. |
| Sheaf.Paper.CompletedProjectionCoherence | V1 | No direct use; unchanged interface. |
| Sheaf.Paper.CompletedPullbackUnitTower | D8 | No direct use; unchanged interface. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | No direct use; unchanged interface. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | No direct use; unchanged interface. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | No direct use; unchanged interface. |

All five unchanged importers compiled against the delivery's compiled item in one
`lcompile.py --all` batch; the item compiled in 36.7 seconds in that batch. Their
statements retain the same meaning because the two comparison definitions are
definitionally equal to the previous constructions. No forced adaptation is needed.

## Status

landed 20261020T211742-L-3496725 2026-10-20 (merge of deliver/J3/Sheaf.Paper.StrictTowerExchangeMateNormalization)
