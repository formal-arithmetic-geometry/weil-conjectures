# Mapping-limit maps: statement interface extraction

## Reason

The target-shift comparison must use exactly the existing map definitions.
Expanding duplicate formulas caused derived-category instance conversion to unfold
large localization constructions and exceed the 60-second compile limit. Move the
three unchanged definitions to the separate shift module and publicly import it
from the original module. Names, universes, signatures and bodies stay verbatim.
No target statement or mathematical definition changes meaning.

## Old

In `Sheaf.Paper.IntegralMappingLimitProjections`:

```lean
def integralMappingLimitMap (S : CoefficientDerivedSystemCalculus l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) :=
  (coefficientIntegralGlobalHom l E W).map
      (Prod.mkHom (𝟙 (op P)) (S.adjunction.unit.app Q)) ≫
    (S.gamma l E W P (S.reduction.obj Q) (S.reduction_normalized Q)).hom

def integralMappingLimitSourceShift
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :=
  letI : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1,t,u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  letI : (coefficientIntegralSections l E W).CommShift ℤ :=
    inferInstanceAs ((coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).rightDerivedFunctor.CommShift ℤ)
  ((RingedHomUniverses.hom.{t+1, t, u, (max u (t+1))+1}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P ⋙
      coefficientIntegralSections l E W).commShiftIso r).hom.app Q

def integralMappingLimitTargetShift (S : CoefficientDerivedSystemCalculus l E W)
    (sh : PurReductionLimitShiftData l E W S)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :=
  coefficientMappingLimit.{max u (t+1)}.map
      ((coefficientSequenceGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op (S.reduction.obj P)))
          ((sh.reduction_shift.commShiftIso r).hom.app Q))) ≫
    ((RingedHomUniverses.hom.{t+1, t, u, (max u (t+1))+1}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (S.reduction.obj P) ⋙
      coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
      coefficientMappingLimit.{max u (t+1)}).commShiftIso r).hom.app (S.reduction.obj Q)
```

## New

The identical declarations now belong to
`Sheaf.Paper.CoefficientEnrichedGlobalShift`. The original module contains
`public import Sheaf.Paper.CoefficientEnrichedGlobalShift`, preserving the API.

```lean
def integralMappingLimitMap (S : CoefficientDerivedSystemCalculus l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) :=
  (coefficientIntegralGlobalHom l E W).map
      (Prod.mkHom (𝟙 (op P)) (S.adjunction.unit.app Q)) ≫
    (S.gamma l E W P (S.reduction.obj Q) (S.reduction_normalized Q)).hom

def integralMappingLimitSourceShift
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :=
  letI : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1,t,u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  letI : (coefficientIntegralSections l E W).CommShift ℤ :=
    inferInstanceAs ((coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).rightDerivedFunctor.CommShift ℤ)
  ((RingedHomUniverses.hom.{t+1, t, u, (max u (t+1))+1}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P ⋙
      coefficientIntegralSections l E W).commShiftIso r).hom.app Q

def integralMappingLimitTargetShift (S : CoefficientDerivedSystemCalculus l E W)
    (sh : PurReductionLimitShiftData l E W S)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :=
  coefficientMappingLimit.{max u (t+1)}.map
      ((coefficientSequenceGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op (S.reduction.obj P)))
          ((sh.reduction_shift.commShiftIso r).hom.app Q))) ≫
    ((RingedHomUniverses.hom.{t+1, t, u, (max u (t+1))+1}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (S.reduction.obj P) ⋙
      coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
      coefficientMappingLimit.{max u (t+1)}).commShiftIso r).hom.app (S.reduction.obj Q)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralMappingLimitProjections | J3 | Publicly imports the extracted definitions and proves the shift clause by the separate lemma. |
| Sheaf.Paper.CoefficientEnrichedGlobalShift | new, J3 | Owns the unchanged definitions and their shift square. |

The `tools/downstream.py --uses` checks for each of the three moved names
report no downstream modules and only the item module as a direct user. A search
for all three names in both Lean roots gives only the item source. Thus there are
no forced adaptations of modules held by other groups.

## Status

landed 20261024T214907-L-728139 2026-10-24 (merge of deliver/J3/Sheaf.Paper.IntegralMappingLimitProjections)
