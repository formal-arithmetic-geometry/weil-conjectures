/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunneth

/-!

# Identity (a) of the trace-class source exchange

`κ_Y ∘ ρ_f = Φ ∘ Rq_* κ_X` (`ProEtale.CondensedRing.kernelPushforward_comp_kunnethVerdierMap`,
blueprint `lem-trf-trace-source-exchange`, Step 3), assembled from the evaluation part and the
exceptional Künneth part proved in `WeilConjectures.TraceFormula.SourceExchangeKunneth`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

set_option profiler true in
-- the compactly supported direct images are unfolded in the defeq checks
/-- **The kernel pushforward and the Künneth–Verdier isomorphisms** (blueprint
`lem-trf-trace-source-exchange`, identity (a)): `κ_Y ∘ ρ_f = Φ ∘ Rq_* κ_X`. -/
theorem kernelPushforward_comp_kunnethVerdierMap :
    kernelPushforward ℓ f K ≫
        kunnethVerdierMap ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
          ((boundedConstructibleLowerStar ℓ f).obj K) =
      (boundedConstructibleLowerStar ℓ (prod.map f f)).map (kunnethVerdierMap ℓ K K) ≫
        classTransportMap ℓ f K := by
  simp only [kernelPushforward, Category.assoc, IsIso.inv_comp_eq]
  apply classTest_injective ℓ (M := (boundedConstructibleLowerStar ℓ f).obj K)
  simp only [classTest_comp ℓ _ (kunnethVerdierMap ℓ
      ((boundedConstructibleLowerStar ℓ f).obj K) ((boundedConstructibleLowerStar ℓ f).obj K)),
    classTest_comp ℓ _ ((boundedConstructibleLowerStar ℓ (prod.map f f)).map
      (kunnethVerdierMap ℓ K K) ≫ classTransportMap ℓ f K),
    classTest_map_comp_classTransportMap, classTest_kunnethVerdierMap]
  simp only [← Functor.map_comp_assoc]
  refine (congrArg (fun t ↦ (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map t ≫
    exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar ℓ f).obj K))
    (MonoidalCategory.whiskerLeft_whiskerLeft_map_comp_evaluation
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar ℓ f).obj K))
    ((boundedConstructibleLowerStar ℓ f).obj K) (lowerStarVerdierDualMap ℓ f K)
    ((ihom.ev ((boundedConstructibleLowerStar ℓ f).obj K)).app (dualizingComplex' ℓ Y))
    _ (MonoidalClosed.whiskerLeft_curry_ihom_ev_app (A :=
        (boundedConstructibleLowerStar ℓ f).obj K) _ _))).trans ?_
  refine (Functor.map_whiskerLeft_map_comp_eq
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar ℓ f).obj K)) _ _ _ _
    (lowerStarTensorMap ℓ f K (verdierDual ℓ K))
    ((boundedConstructibleLowerStar ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)))
    (lowerStarDualizingComplexTrace ℓ f)
    (exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar ℓ f).obj K))
    (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
      (externalProduct ℓ K (dualizingComplex' ℓ X))) _ _
    (lowerShriek_map_trace_comp_exceptionalKunnethAdjoint ℓ f K)
    (evaluation_comp_prodLowerStarExternalProduct ℓ f K)).trans ?_
  simp only [classTransport, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map, Category.id_comp,
    Category.comp_id, Category.assoc, leftProjectionNatTrans, curriedTensor_map_app,
    curriedTensor_obj_obj, Functor.map_comp, MonoidalCategory.whiskerLeft_comp]
  refine whisker_eq _ (whisker_eq _ (whisker_eq _ ?_))
  dsimp only [verdierDual, dualizingComplex, Functor.comp_obj, curriedTensor_obj_obj]
  exact NatIso.map_map₆_comp_hom_app_comp_map_comp_hom_app
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleLowerShriek ℓ (prod.map f f))
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X))
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f) _ _ _ _ _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing
