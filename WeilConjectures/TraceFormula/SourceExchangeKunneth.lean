/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeProjection

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

lemma _root_.CategoryTheory.Functor.OplaxMonoidal.map_evaluation_comp_δ {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] [MonoidalCategory 𝒞] [MonoidalCategory 𝒟] [BraidedCategory 𝒞]
    [BraidedCategory 𝒟] (G : 𝒟 ⥤ 𝒞) [G.OplaxMonoidal]
    (hbraid : ∀ A B : 𝒟, G.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ G B A =
      Functor.OplaxMonoidal.δ G A B ≫ (β_ (G.obj A) (G.obj B)).hom)
    {a b d v w : 𝒟} {Ka Wb Vd Vw E : 𝒞} (x₁ : a ⊗ d ⟶ v) (x₂ : v ⟶ w) (cb : G.obj b ⟶ Wb)
    (ca : G.obj a ⟶ Ka) (cd : G.obj d ⟶ Vd) (cw : G.obj w ⟶ Vw) (m : Ka ⊗ Vd ⟶ E)
    (e : E ⟶ Vw)
    (h : G.map (x₁ ≫ x₂) ≫ cw = Functor.OplaxMonoidal.δ G a d ≫ (ca ⊗ₘ cd) ≫ m ≫ e) :
    G.map ((α_ a b d).inv ≫ (β_ a b).hom ▷ d ≫ (α_ b a d).hom ≫ b ◁ x₁ ≫ b ◁ x₂) ≫
        Functor.OplaxMonoidal.δ G b w ≫ (cb ⊗ₘ cw) =
      Functor.OplaxMonoidal.δ G a (b ⊗ d) ≫
        G.obj a ◁ (Functor.OplaxMonoidal.δ G b d ≫ (cb ⊗ₘ cd)) ≫ ca ▷ (Wb ⊗ Vd) ≫
        (α_ _ _ _).inv ≫ (β_ Ka Wb).hom ▷ Vd ≫ (α_ _ _ _).hom ≫ Wb ◁ m ≫ Wb ◁ e := by
  have h' : G.map (b ◁ x₁) ≫ G.map (b ◁ x₂) ≫ Functor.OplaxMonoidal.δ G b w ≫ (cb ⊗ₘ cw) =
      Functor.OplaxMonoidal.δ G b (a ⊗ d) ≫ (cb ⊗ₘ (Functor.OplaxMonoidal.δ G a d ≫
        (ca ⊗ₘ cd) ≫ m ≫ e)) := by
    rw [← h, ← G.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← Functor.OplaxMonoidal.δ_natural_right_assoc, MonoidalCategory.tensorHom_def',
      MonoidalCategory.tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc,
      Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc, h']
  have h₃ := Functor.OplaxMonoidal.associativity G b a d
  have h₂ := Functor.OplaxMonoidal.δ_natural_left G (β_ a b).hom d
  have h₁ := Functor.OplaxMonoidal.associativity_inv G a b d
  have hnat : (α_ (G.obj a) (G.obj b) (G.obj d)).inv ≫ (β_ (G.obj a) (G.obj b)).hom ▷ G.obj d ≫
      (α_ (G.obj b) (G.obj a) (G.obj d)).hom ≫ (cb ⊗ₘ ((ca ⊗ₘ cd) ≫ m ≫ e)) =
      G.obj a ◁ (cb ⊗ₘ cd) ≫ ca ▷ (Wb ⊗ Vd) ≫ (α_ _ _ _).inv ≫ (β_ Ka Wb).hom ▷ Vd ≫
        (α_ _ _ _).hom ≫ Wb ◁ m ≫ Wb ◁ e := by
    have k1 : cb ⊗ₘ ((ca ⊗ₘ cd) ≫ m ≫ e) = (cb ⊗ₘ (ca ⊗ₘ cd)) ≫ Wb ◁ m ≫ Wb ◁ e := by
      rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.id_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    have k2 : G.obj a ◁ (cb ⊗ₘ cd) ≫ ca ▷ (Wb ⊗ Vd) = ca ⊗ₘ (cb ⊗ₘ cd) :=
      (MonoidalCategory.tensorHom_def' _ _).symm
    have k3 : ((ca ⊗ₘ cb) ⊗ₘ cd) ≫ (β_ Ka Wb).hom ▷ Vd =
        (β_ (G.obj a) (G.obj b)).hom ▷ G.obj d ≫ ((cb ⊗ₘ ca) ⊗ₘ cd) := by
      rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
        BraidedCategory.braiding_naturality, Category.comp_id, Category.id_comp]
    rw [k1, reassoc_of% k2, MonoidalCategory.associator_inv_naturality_assoc, reassoc_of% k3,
      MonoidalCategory.associator_naturality_assoc]
  have k4 : cb ⊗ₘ (Functor.OplaxMonoidal.δ G a d ≫ (ca ⊗ₘ cd) ≫ m ≫ e) =
      G.obj b ◁ Functor.OplaxMonoidal.δ G a d ≫ (cb ⊗ₘ ((ca ⊗ₘ cd) ≫ m ≫ e)) := by
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  rw [k4, ← reassoc_of% h₃, ← reassoc_of% h₂, ← MonoidalCategory.comp_whiskerRight_assoc, hbraid,
    MonoidalCategory.comp_whiskerRight_assoc, ← reassoc_of% h₁, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, hnat]

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

set_option maxHeartbeats 2000000 in
-- the adjunctions of bounded constructible complexes are unfolded in the defeq checks
/-- The left projection morphism of a proper morphism after a unit. -/
lemma leftProjection_lowerShriek_unit_app {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom]
    [QuasiCompact A.hom] [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] (g : A ⟶ B) [IsProper g.left]
    (M W : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app W ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj W)) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ g) M
        ((boundedConstructibleUpperStar _ ℓ g).obj W) =
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app (M ⊗ W) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj (M ⊗ W)) ≫
      (boundedConstructibleLowerShriek _ ℓ g).map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ g) M W) :=
  Verdier.leftProjection_unit_app _ _ _ _
    (fun T M ↦ upperStar_map_exceptionalProjection_comp_counit ℓ g T M)
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ _ ℓ g A B)
    (fun _ _ ↦ boundedConstructible_braiding_hom_braiding_hom _ _ _) M W

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

/-- The transported counits of `q = f × f` are compatible with the multiplication `μ_f`. -/
theorem upperStar_map_tensorMap_comp_prodUpperStarCounit
    (B₁ B₂ B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (e : B₁ ⊗ B₂ ⟶ B) :
    (boundedConstructibleUpperStar _ ℓ (prod.map f f)).map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
            ((boundedConstructibleLowerStar _ ℓ f).obj B₁)
            ((boundedConstructibleLowerStar _ ℓ f).obj B₂) ≫
          (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
            (lowerStarTensorMap ℓ f B₁ B₂ ≫ (boundedConstructibleLowerStar _ ℓ f).map e)) ≫
      prodUpperStarCounit ℓ (prod.map_snd f f) B =
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (prod.map f f)) _ _ ≫
      (prodUpperStarCounit ℓ (prod.map_snd f f) B₁ ⊗ₘ prodUpperStarCounit ℓ (prod.map_snd f f) B₂) ≫
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)) B₁ B₂ ≫
      (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map e :=
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
  by
  unfold prodLowerStarExternalProduct
  refine Verdier.comp_homEquiv_comp_eq_whiskerLeft_homEquiv_comp_leftProjection _ _ _ _
    (fun M W ↦ leftProjection_lowerShriek_unit_app ℓ (prod.map f f) M W) _ _ _ _ _ _ _ _ ?_
  simp only [Functor.Monoidal.μIso_inv]
  exact Functor.OplaxMonoidal.map_evaluation_comp_δ _
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ _ ℓ (prod.map f f) A B)
    _ _ _ _ _ _ _ _ (upperStar_map_tensorMap_comp_prodUpperStarCounit ℓ f _ _ _ _)
  done

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
