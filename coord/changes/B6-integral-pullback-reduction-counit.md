# WeilConjectures.integralPullbackKFlatReductionCounit

## Reason

Expose the independent K-flat reduction-unit calculation needed before the
resolution transport and quotient-counit naturality steps of the existing item.
This adds one public theorem in a new module; it changes no existing interface,
definition or target meaning. The remaining source proof is explicitly a named
hole, rather than an unfinished tactic block inside the item proof.

## Old

No declaration with this name or statement existed.

## New

```lean
theorem integralPullbackKFlatReductionCounit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E Z)
    (F : IntegralComparisonPullbackModel l E h S ρ)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralComparisonConstantTower l E Z).map
        ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
          (integralDerivedPullbackComparison l E h).inv.app P ≫
          F.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj
              (S.reduction.obj (DerivedCategory.Q.obj P.obj)))) =
      (integralTowerInverseImageDiagonal l E h).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map
              (S.adjunction.unit.app (DerivedCategory.Q.obj P.obj)) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj
                (S.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          (S.reduction.obj (DerivedCategory.Q.obj P.obj))
```

The proof is `by sorry`, with source and a full proof in words in its docstring,
and node `lem-trf-integral-pullback-reduction-counit`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralPullbackResolutionMatching | B6 | Imports and applies the K-flat source computation; transports it to the arbitrary chosen representative and then to the first pullback tower by categorical naturality. Existing signatures stay identical. |

The theorem is new, so no existing consumer can refer to it. The item is its only
consumer in the delivered overlay. No held module of another group is adapted.

## Status

landed 20261020T051029-L-1535578 2026-10-20 (merge of deliver/B6/Sheaf.Paper.IntegralPullbackResolutionMatching)
