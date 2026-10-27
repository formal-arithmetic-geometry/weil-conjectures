# WeilConjectures.IntegralExceptionalMapping.integralExceptionalMappingSystem

## Reason

The former calculus hypotheses supplied only an objectwise globalEvaluation family.
The intended outer-counit naturality argument requires its existing resolution
normalization. Require the resolution-coherence structures already provided by
finiteAdjunctionDiagramRealization. This adds no condition on integral inputs or
geometry; every functor, comparison and conclusion is unchanged. A proved private
helper derives the required naturality from globalEvaluation_model, naturality of
systemSectionsEvaluation and fiber_naturality. Both formulas are then proved.

## Old

```lean
theorem integralExceptionalMappingSystem (n : ℕ)
    (K : sfIntegralConstructibleCategory l E X) (L : sfIntegralConstructibleCategory l E Y) :
    finitePsi r a n K L =
      (coefficientFiniteGlobalHom l E Y n).map
        (Prod.mkHom ((finiteSupport r n K).inv.op) (𝟙 _)) ≫
      (a.finiteIso n).hom.app
        (op ((evaluation l E X n).obj ((R l E D hl X SX).obj K)),
          (evaluation l E Y n).obj ((R l E D hl Y SY).obj L)) ≫
      (coefficientFiniteGlobalHom l E X n).map
        (Prod.mkHom (𝟙 _) ((finiteExceptional r n L).inv)) ∧
    ∀ x : (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).obj
        ((coefficientFiniteGlobalHom l E Y n).obj
          (op ((coefficientSequenceDerivedEvaluation l E Y n).obj
            (SY.reduction.obj ((F r).obj K))),
            (coefficientSequenceDerivedEvaluation l E Y n).obj (SY.reduction.obj L.obj))),
      coefficientFiniteHomEquiv l E X n _ _
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
          (finitePsi r a n K L)) x) =
      (((FiniteExceptional.adjunction l E D hl f c n).homEquiv
        ((evaluation l E X n).obj ((R l E D hl X SX).obj K))
        ((evaluation l E Y n).obj ((R l E D hl Y SY).obj L))
        (ObjectProperty.homMk ((finiteSupport r n K).inv ≫
          coefficientFiniteHomEquiv l E Y n _
            ((coefficientSequenceDerivedEvaluation l E Y n).obj
              (SY.reduction.obj L.obj)) x))).hom) ≫
        (finiteExceptional r n L).inv
```

## New

```lean
theorem integralExceptionalMappingSystem
    (CX : CoefficientDerivedSystemResolutionCoherence l E X SX)
    (CY : CoefficientDerivedSystemResolutionCoherence l E Y SY) (n : ℕ)
    (K : sfIntegralConstructibleCategory l E X) (L : sfIntegralConstructibleCategory l E Y) :
    finitePsi r a n K L =
      (coefficientFiniteGlobalHom l E Y n).map
        (Prod.mkHom ((finiteSupport r n K).inv.op) (𝟙 _)) ≫
      (a.finiteIso n).hom.app
        (op ((evaluation l E X n).obj ((R l E D hl X SX).obj K)),
          (evaluation l E Y n).obj ((R l E D hl Y SY).obj L)) ≫
      (coefficientFiniteGlobalHom l E X n).map
        (Prod.mkHom (𝟙 _) ((finiteExceptional r n L).inv)) ∧
    ∀ x : (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).obj
        ((coefficientFiniteGlobalHom l E Y n).obj
          (op ((coefficientSequenceDerivedEvaluation l E Y n).obj
            (SY.reduction.obj ((F r).obj K))),
            (coefficientSequenceDerivedEvaluation l E Y n).obj (SY.reduction.obj L.obj))),
      coefficientFiniteHomEquiv l E X n _ _
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
          (finitePsi r a n K L)) x) =
      (((FiniteExceptional.adjunction l E D hl f c n).homEquiv
        ((evaluation l E X n).obj ((R l E D hl X SX).obj K))
        ((evaluation l E Y n).obj ((R l E D hl Y SY).obj L))
        (ObjectProperty.homMk ((finiteSupport r n K).inv ≫
          coefficientFiniteHomEquiv l E Y n _
            ((coefficientSequenceDerivedEvaluation l E Y n).obj
              (SY.reduction.obj L.obj)) x))).hom) ≫
        (finiteExceptional r n L).inv
```

## Users

The downstream.py --uses scan reports zero downstream modules and only this
module as a textual user; a full Lean-source name search agrees. No forced
adaptation is needed. The two DAG parents remain valid: the exceptional-adjoint
proposition uses the coherent specified realization, and the descended-counit
lemma already assumes full coherence for both calculi. No target changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Q9 | Require resolution coherence and prove both conclusions. |

## Status

landed 20261025T143811-L-1086968 2026-10-25 (merge of deliver/Q9/Sheaf.SixFunctors.IntegralExceptionalMappingSystem)
