/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeTransport

/-!

# The kernel pushforward and the Künneth–Verdier isomorphisms

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

lemma _root_.CategoryTheory.MonoidalCategory.whiskerLeft_whiskerLeft_map_comp_evaluation
    {C E : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [Category E]
    [MonoidalCategory E] (U : E ⥤ C) [U.LaxMonoidal] (P : C) (N : E) {D D' W : E}
    (x : D' ⟶ D) (e : N ⊗ D ⟶ W) (g : N ⊗ D' ⟶ W) (hg : N ◁ x ≫ e = g) :
    U.obj N ◁ (P ◁ U.map x) ≫ (α_ _ _ _).inv ≫ ((β_ (U.obj N) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ U N D) ≫ (P ◁ U.map e) =
      (α_ _ _ _).inv ≫ ((β_ (U.obj N) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ U N D') ≫ (P ◁ U.map g) := by
  subst hg
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right,
    MonoidalCategory.whiskerLeft_comp_assoc]

lemma _root_.CategoryTheory.Functor.map_whiskerLeft_map_comp_eq {𝒞 𝒟 𝒠 : Type*} [Category 𝒞]
    [MonoidalCategory 𝒞] [Category 𝒟] [Category 𝒠] (L : 𝒞 ⥤ 𝒟) (U : 𝒠 ⥤ 𝒞) (P : 𝒞)
    {A A₁ A₂ A₃ Q Q' : 𝒞} {E₁ E₂ E₃ E₄ : 𝒠} {Z : 𝒟} (a₁ : A ⟶ A₁) (a₂ : A₁ ⟶ A₂)
    (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ P ⊗ U.obj E₁) (m₁ : E₁ ⟶ E₂)
    (m₂ : E₂ ⟶ E₃) (τ : E₃ ⟶ E₄) (ex : L.obj (P ⊗ U.obj E₄) ⟶ Z) (pr : P ⊗ U.obj E₃ ⟶ Q)
    (σ : Q ⟶ Q') (T : L.obj Q' ⟶ Z) (W : A ⟶ Q')
    (h₂ : L.map (P ◁ U.map τ) ≫ ex = L.map pr ≫ L.map σ ≫ T)
    (h₁ : a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ P ◁ U.map (m₁ ≫ m₂) ≫ pr ≫ σ = W) :
    L.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ P ◁ U.map (m₁ ≫ m₂ ≫ τ)) ≫ ex = L.map W ≫ T := by
  rw [← h₁]
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc, h₂]

lemma _root_.CategoryTheory.NatIso.map_map₆_comp_hom_app_comp_map_comp_hom_app {𝒱 𝒲 𝒳 𝒴 : Type*}
    [Category 𝒱] [Category 𝒲] [Category 𝒳] [Category 𝒴] (F₁ : 𝒲 ⥤ 𝒴) (G : 𝒱 ⥤ 𝒲) (H : 𝒱 ⥤ 𝒳)
    {Lf Sf : 𝒳 ⥤ 𝒴} (s : G ⋙ F₁ ≅ H ⋙ Lf) (σ : Lf ≅ Sf) {V₀ V₁ V₂ V₃ V₄ V₅ V₆ : 𝒱} {Z : 𝒳}
    (y₁ : V₀ ⟶ V₁) (y₂ : V₁ ⟶ V₂) (y₃ : V₂ ⟶ V₃) (y₄ : V₃ ⟶ V₄) (y₅ : V₄ ⟶ V₅)
    (y₆ : V₅ ⟶ V₆) (e : H.obj V₆ ⟶ Z) :
    F₁.map (G.map y₁) ≫ F₁.map (G.map y₂) ≫ F₁.map (G.map y₃) ≫ F₁.map (G.map y₄) ≫
        F₁.map (G.map y₅) ≫ F₁.map (G.map y₆) ≫ s.hom.app V₆ ≫ Lf.map e ≫ σ.hom.app Z =
      s.hom.app V₀ ≫ Lf.map (H.map y₁) ≫ σ.hom.app _ ≫ Sf.map (H.map y₂) ≫ Sf.map (H.map y₃) ≫
        Sf.map (H.map y₄) ≫ Sf.map (H.map y₅) ≫ Sf.map (H.map y₆) ≫ Sf.map e := by
  have h := s.hom.naturality (y₁ ≫ y₂ ≫ y₃ ≫ y₄ ≫ y₅ ≫ y₆)
  have h' := σ.hom.naturality (H.map y₂ ≫ H.map y₃ ≫ H.map y₄ ≫ H.map y₅ ≫ H.map y₆ ≫ e)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at h h'
  rw [reassoc_of% h, h']

lemma _root_.CategoryTheory.Adjunction.homEquiv_symm_comp_homEquiv {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A B : C} {Z : D} (p : A ⟶ B)
    (e : F.obj B ⟶ Z) : (adj.homEquiv A Z).symm (p ≫ adj.homEquiv B Z e) = F.map p ≫ e := by
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

section Test

variable {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (M : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The test map of the Künneth–Verdier map: the evaluation of `D_S M` against `Lp₂^* M`
followed by the adjoint of the exceptional Künneth map. -/
lemma classTest_kunnethVerdierMap :
    classTest ℓ M (kunnethVerdierMap ℓ M M) =
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : S ⨯ S ⟶ S)).map
          ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
            (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
              (prod.snd : S ⨯ S ⟶ S)) _ _) ≫
            (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).map
              ((ihom.ev M).app (dualizingComplex' ℓ S)))) ≫
        exceptionalKunnethAdjoint ℓ M := by
  have h : kunnethVerdierPairing ℓ M M =
      ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
          (prod.snd : S ⨯ S ⟶ S)) _ _) ≫
        (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).map
          ((ihom.ev M).app (dualizingComplex' ℓ S)))) ≫
      ((boundedConstructibleUpperShriekAdjunction _ ℓ (prod.fst : S ⨯ S ⟶ S)).homEquiv
        (externalProduct ℓ M (dualizingComplex' ℓ S)) M) (exceptionalKunnethAdjoint ℓ M) := by
    simp only [kunnethVerdierPairing, exceptionalKunnethMap, Category.assoc]
    rfl
  simp only [classTest, kunnethVerdierMap, uncurry_curry]
  refine (congrArg ((boundedConstructibleUpperShriekAdjunction _ ℓ
    (prod.fst : S ⨯ S ⟶ S)).homEquiv _ _).symm h).trans ?_
  exact Adjunction.homEquiv_symm_comp_homEquiv _ _ _

end Test

section KernelPushforward

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- **The exceptional Künneth adjoint commutes with a proper pushforward** (blueprint
`lem-trf-trace-source-exchange`, Step 3): through `Π_f`, `Rq_* ≅ Rq_!`, the composition law of
the square `q ≫ p₁' = p₁ ≫ f` and `Rf_! ≅ Rf_*`, the adjoint of the exceptional Künneth map of
`Rf_* K` precomposed with the trace `τ_f` is `Rf_*` of that of `K`. -/
theorem lowerShriek_map_trace_comp_exceptionalKunnethAdjoint :
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj K) ◁
          (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
            (lowerStarDualizingComplexTrace ℓ f)) ≫
      exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K) =
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (dualizingComplex' ℓ X))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map (exceptionalKunnethAdjoint ℓ K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K :=
  sorry

/-- The evaluation part of identity (a) (blueprint `lem-trf-trace-source-exchange`, Step 3):
`Π_f` and `μ_f` are adjoint to the counits of `f`. -/
theorem evaluation_comp_prodLowerStarExternalProduct :
    (α_ _ _ _).inv ≫ ((β_ ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K))
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K))).hom ▷ _) ≫ (α_ _ _ _).hom ≫
      (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
        ((boundedConstructibleLowerStar _ ℓ f).obj K)
        ((boundedConstructibleLowerStar _ ℓ f).obj (verdierDual ℓ (toPoint X) K))) ≫
      (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
        (lowerStarTensorMap ℓ f K (verdierDual ℓ (toPoint X) K) ≫
          (boundedConstructibleLowerStar _ ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)))) ≫
      prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) =
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
        ((boundedConstructibleLowerStar _ ℓ f).obj K) ◁
      (prodLowerStarExternalProduct ℓ f f K (verdierDual ℓ (toPoint X) K) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (verdierDual ℓ (toPoint X) K))) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ (prod.map f f))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K))
        (externalProduct ℓ K (verdierDual ℓ (toPoint X) K)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.map f f)).map
        ((prodUpperStarCounit ℓ (prod.map_snd f f) K ▷ _) ≫
          (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
          (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
            (prod.snd : X ⨯ X ⟶ X)) _ _) ≫
          (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map
            ((ihom.ev K).app (dualizingComplex' ℓ X)))) :=
  sorry

set_option maxHeartbeats 6000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- **The kernel pushforward and the Künneth–Verdier isomorphisms** (blueprint
`lem-trf-trace-source-exchange`, identity (a)): `κ_Y ∘ ρ_f = Φ ∘ Rq_* κ_X`. -/
theorem kernelPushforward_comp_kunnethVerdierMap :
    kernelPushforward ℓ f K ≫
        kunnethVerdierMap ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K)
          ((boundedConstructibleLowerStar _ ℓ f).obj K) =
      (boundedConstructibleLowerStar _ ℓ (prod.map f f)).map (kunnethVerdierMap ℓ K K) ≫
        classTransportMap ℓ f K := by
  rw [kernelPushforward, Category.assoc, IsIso.inv_comp_eq]
  apply classTest_injective
  rw [classTest_comp, classTest_comp, classTest_map_comp_classTransportMap,
    classTest_kunnethVerdierMap, classTest_kunnethVerdierMap]

  rewrite [← Functor.map_comp_assoc]
  refine (congrArg (fun t ↦ (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map t ≫
    exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K))
    (MonoidalCategory.whiskerLeft_whiskerLeft_map_comp_evaluation
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar _ ℓ f).obj K))
    ((boundedConstructibleLowerStar _ ℓ f).obj K) (lowerStarVerdierDualMap ℓ f K)
    ((ihom.ev ((boundedConstructibleLowerStar _ ℓ f).obj K)).app (dualizingComplex' ℓ Y))
    _ (MonoidalClosed.whiskerLeft_curry_ihom_ev_app (A := (boundedConstructibleLowerStar _ ℓ f).obj K) _ _))).trans ?_
  refine (Functor.map_whiskerLeft_map_comp_eq
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar _ ℓ f).obj K)) _ _ _ _
    (lowerStarTensorMap ℓ f K (verdierDual ℓ (toPoint X) K))
    ((boundedConstructibleLowerStar _ ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)))
    (lowerStarDualizingComplexTrace ℓ f)
    (exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K))
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
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleLowerShriek _ ℓ (prod.map f f))
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)) _ _ _ _ _ _ _ _ _

end KernelPushforward

end AlgebraicGeometry.ProEtale.CondensedRing
