# spCompletedStrictTower and the completed-tower interface

## Reason

The three independent remaining comparison steps must be modules that the item imports.
Their statements use the completed scalar-forgetting, reduction and total-limit constructions.
Move those five existing definitions verbatim to the lower module
Sheaf.Paper.SmoothPurityCompletedTowerRoos, and publicly re-export that module from the item.
This breaks the would-be helper/import cycle. Add proved componentwise exactness instances,
the standard derived-limit shift structure, and its triangulatedness theorem there.
The new Roos theorem has a proof hole with its own node; it chooses no data in a definition.

Every existing declaration keeps its name, signature, universe, visibility and construction.
Every original public import of the item is retained. New proof imports are private.
No target or mathematical definition is changed, and no source-library module is edited.

## Old

The following constructions were declared in SmoothPurityNormalizedEquivalence:

```lean
/-- Forget the finite-level actions to completed coefficients, retaining all strict
transitions. Source: blueprint, definition of L_T (blueprint: det-sp-normalized-equivalence). -/
def spCompletedStrictTower (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ⥤
      (ℕᵒᵖ ⥤ WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  (Functor.ofOpSequence (spCompletedTransition l E T D)).flip

/-- The coefficient-ring identification transports the existing reduction functor
from section modules to modules over the completed ring. Source: blueprint, r_T
(blueprint: det-sp-normalized-equivalence). -/
def spCompletedReduction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      spDerivedCoefficientTowers l E T D :=
  (restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      R.coefficient.hom)).mapDerivedCategory ⋙ R.red

/-- Total derived inverse limit after the exact scalar-forgetting functor. The
fixed-ring limit is the existing K-injective total derived inverse limit, including its
resolution-normalized projections. Source: blueprint, L_T; Stacks 0941
(blueprint: det-sp-normalized-equivalence). -/
def spCompletedTotalLimit (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] :
    spDerivedCoefficientTowers l E T D ⥤
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  letI := D.hasDerived
  (spCompletedStrictTower l E T D).mapDerivedCategory ⋙
    WeilConjectures.coefficientConstantTowerLimit l E T

/-- Exact evaluation commutes with forgetting the finite-level coefficient actions.
The comparison is the canonical localization comparison for the two exact composites.
Source: blueprint, definition of L_T (blueprint: det-sp-normalized-equivalence). -/
def spCompletedForgettingEvaluationIso (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    @Functor.mapDerivedCategory _ _ _ D.hasDerived _ _ _
        (HasDerivedCategory.standard _) (spCompletedStrictTower l E T D) _ _ _ ⋙
      WeilConjectures.coefficientConstantTowerEvaluation l E T n ≅
        spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Functor.mapDerivedCategoryCompIso (spCompletedStrictTower l E T D)
    ((evaluation ℕᵒᵖ (WeilConjectures.scalarReductionSource l E T)).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryCompIso (spCoefficientEvaluation l E T D.equivalence n)
      (spCompletedEllRestriction l E T n)

/-- The actual total-limit projection to each completed-coefficient level. Its
normalization comes from the existing projection on simultaneous K-injective towers.
Source: blueprint, total limit and its counit (blueprint: det-sp-normalized-equivalence). -/
def spCompletedTotalProjection (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    spCompletedTotalLimit l E T D ⟶ spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  Functor.whiskerLeft (spCompletedStrictTower l E T D).mapDerivedCategory
    (WeilConjectures.coefficientConstantTowerProjection l E T n) ≫
      (spCompletedForgettingEvaluationIso l E T D n).hom
```

## New

The preceding five declarations are verbatim in SmoothPurityCompletedTowerRoos and the item adds:

```lean
public import Sheaf.Paper.SmoothPurityCompletedTowerRoos
```

The new lower module also proves spCompletedStrictTowerLimits,
spCompletedStrictTowerColimits, spCompletedStrictTowerAdditive,
spCompletedTotalLimitShift and spCompletedTotalLimit_triangulated from existing exact evaluation
and total right-derived functor instances. Their types are exactly the existing structure fields.
The three named comparison statements in the new modules are described in the report and nodes.

## Users

The source-only downstream scan lists the following complete transitive consumer set.
There are no consumer adaptations: public re-export preserves each name and definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompleteCompactificationLimitRealization | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.CompleteProjectionMateDescent | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.IntegralDirectImageTower | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.ProjectionReductionPresentation | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.TwistedPullbackReductionData | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.TwistedPullbackReductionTower | not adapted | Same signatures and constructions through public re-export. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | S4 | Re-exports the moved interface and proves restriction assembly. |

## Status

landed 20261025T095827-L-3486300 2026-10-25 (merge of deliver/S4/Sheaf.Paper.SmoothPurityNormalizedEquivalence)
