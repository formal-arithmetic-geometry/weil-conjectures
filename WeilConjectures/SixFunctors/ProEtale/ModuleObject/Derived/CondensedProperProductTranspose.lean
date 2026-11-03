/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
public import WeilConjectures.CategoryTheory.TensorExchangeProductMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-! # Proper product transpose for condensed derived module objects

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/
sk-thm-sf-kunneth-relative.proof.md, Coherence (i), final sentence
(blueprint: lem-sf-condensed-proper-product-transpose).

The ordinary unbounded projection, exchange and compositor maps define the product map.
Its transpose is the canonical tensor comparison followed by the two counits.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Moving a conjugate right-adjoint comparison across the Hom equivalence (step 1).
private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {N : D} (u : M ⟶ R₁.obj N) :
    (a₂.homEquiv M N).symm (u ≫ (conjugateEquiv a₁ a₂ α).app N) =
      α.app M ≫ (a₁.homEquiv M N).symm u := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, α.naturality_assoc]

-- The two symmetries cancel after the first projection is transposed (steps 2 and 3).
private theorem symmetric_projection_transpose
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (δ : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (hc : ∀ A B, F.map (β_ A B).hom ≫ δ B A =
      δ A B ≫ (β_ (F.obj A) (F.obj B)).hom)
    (hs : ∀ A B : D, (β_ A B).hom ≫ (β_ B A).hom = 𝟙 _)
    (A : C) (M : D)
    (π : G.obj M ⊗ A ⟶ G.obj (M ⊗ F.obj A))
    (hπ : (a.homEquiv _ _).symm π =
      δ (G.obj M) A ≫ (a.counit.app M ⊗ₘ 𝟙 (F.obj A))) :
    (a.homEquiv _ _).symm
      ((β_ A (G.obj M)).hom ≫ π ≫ G.map (β_ M (F.obj A)).hom) =
      δ A (G.obj M) ≫ (𝟙 (F.obj A) ⊗ₘ a.counit.app M) := by
  rw [a.homEquiv_naturality_left_symm, a.homEquiv_naturality_right_symm, hπ]
  simp only [Category.assoc]
  rw [reassoc_of% (hc A (G.obj M))]
  slice_lhs 3 4 =>
    exact BraidedCategory.braiding_naturality (a.counit.app M) (𝟙 (F.obj A))
  simp only [Functor.comp_obj]
  rw [reassoc_of% (hs (F.obj A) (F.obj (G.obj M)))]

-- Transposing the second projection after a tensor of two morphisms (step 4).
private theorem tensor_projection_transpose
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (δ : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (hn : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      F.map (f ⊗ₘ g) ≫ δ A' B' = δ A B ≫ (F.map f ⊗ₘ F.map g))
    {A B W : C} {M : D} (f : A ⟶ G.obj M) (g : B ⟶ W)
    (π : G.obj M ⊗ W ⟶ G.obj (M ⊗ F.obj W))
    (hπ : (a.homEquiv _ _).symm π =
      δ (G.obj M) W ≫ (a.counit.app M ⊗ₘ 𝟙 (F.obj W))) :
    (a.homEquiv _ _).symm ((f ⊗ₘ g) ≫ π) =
      δ A B ≫ ((F.map f ≫ a.counit.app M) ⊗ₘ F.map g) := by
  rw [a.homEquiv_naturality_left_symm, hπ, ← Category.assoc, hn]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

private theorem successive_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}
    (a : F ⊣ G) (b : F' ⊣ G') {M : C} {Q : D} {N : E}
    (w : M ⟶ G.obj Q) (v : Q ⟶ G'.obj N) :
    ((a.comp b).homEquiv M N).symm (w ≫ G.map v) =
      F'.map ((a.homEquiv _ _).symm w) ≫ (b.homEquiv _ _).symm v := by
  rw [Adjunction.comp_homEquiv]
  change (b.homEquiv _ _).symm ((a.homEquiv _ _).symm (w ≫ G.map v)) = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]

private theorem pair_normalization
    {D E : Type*} [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E] (P : D ⥤ E)
    (m : ∀ A B, P.obj (A ⊗ B) ⟶ P.obj A ⊗ P.obj B)
    (hn : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      m A B ≫ (P.map f ⊗ₘ P.map g) = P.map (f ⊗ₘ g) ≫ m A' B')
    {H U V W : D} {T X Y Z : E}
    (c : T ⟶ P.obj H) (δ : H ⟶ U ⊗ V)
    (cA : X ⟶ P.obj U) (cB : Y ⟶ P.obj V) (δt : T ⟶ X ⊗ Y)
    (hc : δt ≫ (cA ⊗ₘ cB) = c ≫ P.map δ ≫ m U V)
    (e : V ⟶ W) (h : P.obj U ⟶ Z) :
    c ≫ P.map (δ ≫ (𝟙 U ⊗ₘ e)) ≫ m U W ≫ (h ⊗ₘ 𝟙 (P.obj W)) =
      δt ≫ ((cA ≫ h) ⊗ₘ (cB ≫ P.map e)) := by
  simp only [P.map_comp, Category.assoc]
  rw [← reassoc_of% (hn (𝟙 U) e)]
  simp only [P.map_id, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [← reassoc_of% hc, tensorHom_comp_tensorHom]

-- The six-step calculation, with the canonical data supplied as parameters.
private theorem product_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [BraidedCategory C] [BraidedCategory D]
    {Fg : C ⥤ D} {Rg : D ⥤ C} {Fq : D ⥤ E} {Rq : E ⥤ D}
    {Ft : C ⥤ E} {Rt : E ⥤ C}
    (ag : Fg ⊣ Rg) (aq : Fq ⊣ Rq) (aTot : Ft ⊣ Rt)
    (δg : ∀ A B, Fg.obj (A ⊗ B) ⟶ Fg.obj A ⊗ Fg.obj B)
    (δq : ∀ A B, Fq.obj (A ⊗ B) ⟶ Fq.obj A ⊗ Fq.obj B)
    (δt : ∀ A B, Ft.obj (A ⊗ B) ⟶ Ft.obj A ⊗ Ft.obj B)
    (c : Ft ≅ Fg ⋙ Fq)
    (hc : ∀ A B, Fg.map (β_ A B).hom ≫ δg B A =
      δg A B ≫ (β_ (Fg.obj A) (Fg.obj B)).hom)
    (hs : ∀ A B : D, (β_ A B).hom ≫ (β_ B A).hom = 𝟙 _)
    (hn : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      δq A B ≫ (Fq.map f ⊗ₘ Fq.map g) = Fq.map (f ⊗ₘ g) ≫ δq A' B')
    (A : C) (L : D) (K : E)
    (s₀ : A ⊗ Rg.obj L ⟶ Rg.obj L ⊗ A)
    (h₀ : s₀ = (β_ A (Rg.obj L)).hom)
    (s₁ : L ⊗ Fg.obj A ⟶ Fg.obj A ⊗ L)
    (h₁ : s₁ = (β_ L (Fg.obj A)).hom)
    (πg : Rg.obj L ⊗ A ⟶ Rg.obj (L ⊗ Fg.obj A))
    (hπg : (ag.homEquiv _ _).symm πg =
      δg (Rg.obj L) A ≫ (ag.counit.app L ⊗ₘ 𝟙 (Fg.obj A)))
    (πq : Rq.obj K ⊗ L ⟶ Rq.obj (K ⊗ Fq.obj L))
    (hπq : (aq.homEquiv _ _).symm πq =
      δq (Rq.obj K) L ≫ (aq.counit.app K ⊗ₘ 𝟙 (Fq.obj L)))
    (ex : Fg.obj A ⟶ Rq.obj K) (h : Fq.obj (Fg.obj A) ⟶ K)
    (he : Fq.map ex ≫ aq.counit.app K = h)
    (ht : δt A (Rg.obj L) ≫ (c.hom.app A ⊗ₘ c.hom.app (Rg.obj L)) =
      c.hom.app (A ⊗ Rg.obj L) ≫ Fq.map (δg A (Rg.obj L)) ≫
        δq (Fg.obj A) (Fg.obj (Rg.obj L))) :
    (aTot.homEquiv _ _).symm
      (s₀ ≫ πg ≫ Rg.map s₁ ≫
        Rg.map (ex ⊗ₘ 𝟙 L) ≫ Rg.map πq ≫
          (conjugateIsoEquiv (ag.comp aq) aTot c).hom.app _) =
      δt A (Rg.obj L) ≫
        ((c.hom.app A ≫ h) ⊗ₘ (c.hom.app (Rg.obj L) ≫ Fq.map (ag.counit.app L))) := by
  rw [conjugateIsoEquiv_apply_hom]
  let w := s₀ ≫ πg ≫ Rg.map s₁
  let v := (ex ⊗ₘ 𝟙 L) ≫ πq
  have hw : (ag.homEquiv _ _).symm w =
      δg A (Rg.obj L) ≫ (𝟙 (Fg.obj A) ⊗ₘ ag.counit.app L) := by
    dsimp only [w]
    rw [h₀, h₁]
    exact symmetric_projection_transpose ag δg hc hs A L πg hπg
  have hv : (aq.homEquiv _ _).symm v =
      δq (Fg.obj A) L ≫ ((Fq.map ex ≫ aq.counit.app K) ⊗ₘ 𝟙 (Fq.obj L)) := by
    have hv' := tensor_projection_transpose aq δq
      (fun {_ _ _ _} f g ↦ (hn f g).symm) ex (𝟙 L) πq hπq
    rw [Fq.map_id L] at hv'
    exact hv'
  have hm : s₀ ≫ πg ≫ Rg.map s₁ ≫
      Rg.map (ex ⊗ₘ 𝟙 L) ≫ Rg.map πq ≫
        (conjugateEquiv (ag.comp aq) aTot c.hom).app (K ⊗ Fq.obj L) =
      (w ≫ Rg.map v) ≫ (conjugateEquiv (ag.comp aq) aTot c.hom).app _ := by
    simp only [w, v, Functor.map_comp, Category.assoc]
  rw [hm]
  rw [conjugate_transpose (ag.comp aq) aTot c.hom (w ≫ Rg.map v)]
  rw [successive_transpose ag aq w v, hw, hv, he]
  exact pair_normalization Fq δq hn
    (c.hom.app _) (δg A _) (c.hom.app A) (c.hom.app _) (δt A _) ht (ag.counit.app L) h

private theorem product_transpose_of_mate
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [BraidedCategory C] [BraidedCategory D]
    {Fg : C ⥤ D} {Rg : D ⥤ C} {Fq : D ⥤ E} {Rq : E ⥤ D}
    {Ft : C ⥤ E} {Rt : E ⥤ C} {Ff : C ⥤ H} {Rf : H ⥤ C} {Fp : H ⥤ E}
    (af : Ff ⊣ Rf) (ag : Fg ⊣ Rg) (aq : Fq ⊣ Rq) (aTot : Ft ⊣ Rt)
    (δg : ∀ A B, Fg.obj (A ⊗ B) ⟶ Fg.obj A ⊗ Fg.obj B)
    (δq : ∀ A B, Fq.obj (A ⊗ B) ⟶ Fq.obj A ⊗ Fq.obj B)
    (δt : ∀ A B, Ft.obj (A ⊗ B) ⟶ Ft.obj A ⊗ Ft.obj B)
    (c : Ft ≅ Fg ⋙ Fq) (θ : Fg ⋙ Fq ≅ Ff ⋙ Fp)
    (τ : Rf ⋙ Fg ⟶ Fp ⋙ Rq)
    (hτ : τ = (mateEquiv af aq (TwoSquare.mk _ _ _ _ θ.hom)).natTrans)
    (d : Rq ⋙ Rg ≅ Rt) (hd : d = conjugateIsoEquiv (ag.comp aq) aTot c)
    (hc : ∀ A B, Fg.map (β_ A B).hom ≫ δg B A =
      δg A B ≫ (β_ (Fg.obj A) (Fg.obj B)).hom)
    (hs : ∀ A B : D, (β_ A B).hom ≫ (β_ B A).hom = 𝟙 _)
    (hn : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      δq A B ≫ (Fq.map f ⊗ₘ Fq.map g) = Fq.map (f ⊗ₘ g) ≫ δq A' B')
    (M : H) (L : D)
    (s₀ : Rf.obj M ⊗ Rg.obj L ⟶ Rg.obj L ⊗ Rf.obj M)
    (h₀ : s₀ = (β_ (Rf.obj M) (Rg.obj L)).hom)
    (s₁ : L ⊗ Fg.obj (Rf.obj M) ⟶ Fg.obj (Rf.obj M) ⊗ L)
    (h₁ : s₁ = (β_ L (Fg.obj (Rf.obj M))).hom)
    (πg : Rg.obj L ⊗ Rf.obj M ⟶ Rg.obj (L ⊗ Fg.obj (Rf.obj M)))
    (hπg : (ag.homEquiv _ _).symm πg =
      δg (Rg.obj L) (Rf.obj M) ≫ (ag.counit.app L ⊗ₘ 𝟙 (Fg.obj (Rf.obj M))))
    (πq : Rq.obj (Fp.obj M) ⊗ L ⟶ Rq.obj (Fp.obj M ⊗ Fq.obj L))
    (hπq : (aq.homEquiv _ _).symm πq =
      δq (Rq.obj (Fp.obj M)) L ≫ (aq.counit.app (Fp.obj M) ⊗ₘ 𝟙 (Fq.obj L)))
    (ht : ∀ A B, δt A B ≫ (c.hom.app A ⊗ₘ c.hom.app B) =
      c.hom.app (A ⊗ B) ≫ Fq.map (δg A B) ≫ δq (Fg.obj A) (Fg.obj B)) :
    (aTot.homEquiv _ _).symm
      (tensorExchangeProductMap τ d.hom M L s₀ πg s₁ πq) =
      δt (Rf.obj M) (Rg.obj L) ≫
        ((c.hom.app (Rf.obj M) ≫ θ.hom.app (Rf.obj M) ≫ Fp.map (af.counit.app M)) ⊗ₘ
          (c.hom.app (Rg.obj L) ≫ Fq.map (ag.counit.app L))) := by
  unfold tensorExchangeProductMap
  rw [hτ, hd]
  exact product_transpose ag aq aTot δg δq δt c hc hs hn (Rf.obj M) L (Fp.obj M)
    s₀ h₀ s₁ h₁ πg hπg πq hπq
    ((mateEquiv af aq (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app M)
    (θ.hom.app (Rf.obj M) ≫ Fp.map (af.counit.app M))
    (mateEquiv_counit af aq (TwoSquare.mk _ _ _ _ θ.hom) M)
    (ht (Rf.obj M) (Rg.obj L))

private theorem projection_transpose_core
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (M : D) (A : C) :
    (a.homEquiv _ _).symm (((a.rightAdjointProjectionMap φ).app M).app A) =
      (φ.app (G.obj M)).app A ≫ (a.counit.app M ⊗ₘ 𝟙 (F.obj A)) := by
  simpa only [Functor.comp_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.id_obj, curriedTensor_obj_obj, curriedTensor_map_app, tensorHom_id] using
    a.homEquiv_symm_rightAdjointProjectionMap_app_app φ M A

private theorem koszul_symmetry_hom
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (K L : DerivedCategory C) :
    letI := DerivedCategory.braidedCategory' C
    (derivedTensorKoszulSymmetry C K L).hom = (β_ K L).hom := by
  rfl

section

attribute [local irreducible] upperStar lowerStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp

-- Rewrite the complete natural transformation before evaluating its component.
-- Explicit functor arguments keep the native interfaces in the mate's type.
private theorem native_exchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    moduleObjectDerivedExchange Λ sq =
      (mateEquiv
        (L₁ := moduleObjectDerivedPullback Λ p)
        (R₁ := moduleObjectDerivedPushforward Λ p)
        (L₂ := moduleObjectDerivedPullback Λ p')
        (R₂ := moduleObjectDerivedPushforward Λ p')
        (G := moduleObjectDerivedPullback Λ g)
        (H := moduleObjectDerivedPullback Λ g')
        (derivedUpperStarLowerStarAdjunction Λ p)
        (derivedUpperStarLowerStarAdjunction Λ p')
        (TwoSquare.mk _ _ _ _
          (moduleObjectDerivedPullbackSquareComparison Λ sq).hom)).natTrans := by
  rfl


end

section

attribute [local irreducible] upperStar lowerStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp

private theorem native_pushforward_compositor_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedLowerStarComp Λ f g =
      conjugateIsoEquiv
        (L₁ := moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f)
        (R₁ := moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPushforward Λ g)
        (L₂ := moduleObjectDerivedPullback Λ (f ≫ g))
        (R₂ := moduleObjectDerivedPushforward Λ (f ≫ g))
        ((show moduleObjectDerivedPullback Λ g ⊣ moduleObjectDerivedPushforward Λ g from
          derivedUpperStarLowerStarAdjunction Λ g).comp
          (show moduleObjectDerivedPullback Λ f ⊣ moduleObjectDerivedPushforward Λ f from
            derivedUpperStarLowerStarAdjunction Λ f))
        (derivedUpperStarLowerStarAdjunction Λ (f ≫ g)) (leftDerivedUpperStarComp Λ f g) := by
  rfl

end

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y B : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
  (L : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))

/-- The product map: signed symmetry, the `g` projection, signed symmetry, the
unit--square--counit exchange tensor identity, the `q` projection, and the direct-image
compositor, in that order. Here `p` and `q` are the canonical pullback projections and
`t = q ≫ g = p ≫ f`. Every factor is an existing canonical construction. The generic
six-factor constructor retains the functors and exchange before evaluating their components.
Source: the cited blueprint proof, Coherence (i), final sentence
(blueprint: lem-sf-condensed-proper-product-transpose). -/
def condensedProperProductMap :
    (moduleObjectDerivedPushforward Λ f).obj K ⊗
        (moduleObjectDerivedPushforward Λ g).obj L ⟶
      (moduleObjectDerivedPushforward Λ (pullback.snd f g ≫ g)).obj
        ((moduleObjectDerivedPullback Λ (pullback.fst f g)).obj K ⊗
          (moduleObjectDerivedPullback Λ (pullback.snd f g)).obj L) :=
  tensorExchangeProductMap
    (mC := Mod.derivedMonoidalCategory
      (C := Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (R := condensedRingObj Λ B))
    (mD := Mod.derivedMonoidalCategory
      (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (R := condensedRingObj Λ Y))
    (mE := Mod.derivedMonoidalCategory
      (C := Sheaf (Scheme.ProEt.topology (pullback f g)) Ab.{u + 1})
      (R := condensedRingObj Λ (pullback f g)))
    (Rf := moduleObjectDerivedPushforward Λ f)
    (Fg := moduleObjectDerivedPullback Λ g)
    (Fp := moduleObjectDerivedPullback Λ (pullback.fst f g))
    (Rq := moduleObjectDerivedPushforward Λ (pullback.snd f g))
    (Rg := moduleObjectDerivedPushforward Λ g)
    (Fq := moduleObjectDerivedPullback Λ (pullback.snd f g))
    (Rt := moduleObjectDerivedPushforward Λ (pullback.snd f g ≫ g))
    (moduleObjectDerivedExchange Λ
      (CommSq.mk (pullback.condition (f := f) (g := g))))
    (rightDerivedLowerStarComp Λ (pullback.snd f g) g).hom K L
    (derivedTensorKoszulSymmetry _ _ _).hom
    (moduleObjectProjectionMap Λ g L ((moduleObjectDerivedPushforward Λ f).obj K))
    (derivedTensorKoszulSymmetry _ _ _).hom
    (moduleObjectProjectionMap Λ (pullback.snd f g)
      ((moduleObjectDerivedPullback Λ (pullback.fst f g)).obj K) L)

attribute [local instance] DerivedCategory.braidedCategory'

attribute [local irreducible] upperStar lowerStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp
  moduleObjectDerivedExchange mateEquiv moduleObjectDerivedPullbackSquareComparison

set_option maxHeartbeats 200000 in
-- Instantiating the native tensor comparisons involves large coefficient categories.
/-- The product map is adjoint to the tensor of the two pulled-back counits.
Source: the cited blueprint proof, Coherence (i), final sentence
(blueprint: lem-sf-condensed-proper-product-transpose).

Proof, following the six DAG steps:
1. `lem-fix-condensed-pullback-coherence` identifies the specified adjunction for `t`
   with the composite adjunction for `q` then `g`, including its counit and tensorator.
2. `def-sfb-module-object-projection-map` identifies the transpose of each projection
   map with its tensorator followed by counit tensor identity; no projection is inverted.
3. Transpose along `g`. Naturality of its counit and the pullback braiding identity
   `lem-sf-condensed-derived-pullback-braiding` move the counit through the two symmetries,
   which cancel, leaving the exchange tensor the `g` counit after the tensorator.
4. Transpose along `q`. The defining projection equation and tensorator naturality give
   the tensor of the `q`-transpose of the exchange and the pulled-back `g` counit.
5. Expand the exchange using `def-weil-pbc-adjunction-mate`: counit naturality and the
   left triangle identity cancel its `q` unit and counit, leaving the square comparison
   followed by the pulled-back `f` counit.
6. Coherence identifies the composite tensorator with that for `t` and the square
   comparison with the `fp` compositor. This gives exactly the two-counit map below.
All objects are unbounded native derived modules and no exchange map is inverted. -/
theorem condensedProperProductTranspose [IsProper f] [IsProper g] :
    ((derivedUpperStarLowerStarAdjunction Λ (pullback.snd f g ≫ g)).homEquiv _ _).symm
        (condensedProperProductMap Λ f g K L) =
      ((leftDerivedUpperStarTensor Λ (pullback.snd f g ≫ g)).app
        ((moduleObjectDerivedPushforward Λ f).obj K)).app
          ((moduleObjectDerivedPushforward Λ g).obj L) ≫
        (((leftDerivedUpperStarComp Λ (pullback.snd f g) g).hom.app
            ((moduleObjectDerivedPushforward Λ f).obj K) ≫
          (moduleObjectDerivedPullbackSquareComparison Λ
            (CommSq.mk (pullback.condition (f := f) (g := g)))).hom.app
              ((moduleObjectDerivedPushforward Λ f).obj K) ≫
          (moduleObjectDerivedPullback Λ (pullback.fst f g)).map
            ((derivedUpperStarLowerStarAdjunction Λ f).counit.app K)) ⊗ₘ
          ((leftDerivedUpperStarComp Λ (pullback.snd f g) g).hom.app
              ((moduleObjectDerivedPushforward Λ g).obj L) ≫
            (moduleObjectDerivedPullback Λ (pullback.snd f g)).map
              ((derivedUpperStarLowerStarAdjunction Λ g).counit.app L))) := by
  let q := pullback.snd f g
  let p := pullback.fst f g
  let A := (moduleObjectDerivedPushforward Λ f).obj K
  let E := (moduleObjectDerivedPullback Λ p).obj K
  let ag : moduleObjectDerivedPullback Λ g ⊣ moduleObjectDerivedPushforward Λ g :=
    derivedUpperStarLowerStarAdjunction Λ g
  let aq : moduleObjectDerivedPullback Λ q ⊣ moduleObjectDerivedPushforward Λ q :=
    derivedUpperStarLowerStarAdjunction Λ q
  let aTot : moduleObjectDerivedPullback Λ (q ≫ g) ⊣
      moduleObjectDerivedPushforward Λ (q ≫ g) :=
    derivedUpperStarLowerStarAdjunction Λ (q ≫ g)
  let c : moduleObjectDerivedPullback Λ (q ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ q :=
    leftDerivedUpperStarComp Λ q g
  refine product_transpose_of_mate
    (Ff := moduleObjectDerivedPullback Λ f)
    (Rf := moduleObjectDerivedPushforward Λ f)
    (Fp := moduleObjectDerivedPullback Λ p)
    (derivedUpperStarLowerStarAdjunction Λ f) ag aq aTot
    (fun A B ↦ ((leftDerivedUpperStarTensor Λ g).app A).app B)
    (fun A B ↦ ((leftDerivedUpperStarTensor Λ q).app A).app B)
    (fun A B ↦ ((leftDerivedUpperStarTensor Λ (q ≫ g)).app A).app B)
    c (moduleObjectDerivedPullbackSquareComparison Λ
      (CommSq.mk (pullback.condition (f := f) (g := g))))
    (moduleObjectDerivedExchange Λ
      (CommSq.mk (pullback.condition (f := f) (g := g))))
    (native_exchange_eq Λ (CommSq.mk (pullback.condition (f := f) (g := g))))
    (rightDerivedLowerStarComp Λ q g) (native_pushforward_compositor_eq Λ q g)
    (leftDerivedUpperStarTensor_braiding Λ g)
    (fun A B ↦ DerivedCategory.braiding_hom_braiding_hom _
      (fun U V ↦ SymmetricCategory.symmetry U V) A B)
    (fun {_ _ _ _} a b ↦ leftDerivedUpperStarTensor_naturality Λ q a b)
    K L (derivedTensorKoszulSymmetry _ _ _).hom (koszul_symmetry_hom _ _ _)
    (derivedTensorKoszulSymmetry _ _ _).hom (koszul_symmetry_hom _ _ _)
    (moduleObjectProjectionMap Λ g L A) ?_
    (moduleObjectProjectionMap Λ q E L) ?_ ?_
  · exact projection_transpose_core ag (leftDerivedUpperStarTensor Λ g) L A
  · exact projection_transpose_core aq (leftDerivedUpperStarTensor Λ q) E L
  · exact leftDerivedUpperStarTensor_comp Λ q g

end AlgebraicGeometry.ProEtale.CondensedRing
