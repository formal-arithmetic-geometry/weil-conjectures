/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
public import WeilConjectures.TraceFormula.FieldDualizable
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen

/-!

# Nearby duality and global sections: the concrete inputs

For a trait model `M` over the base with proper `X`, `X'` and proper total space, the global
sections `RΓ(X', δ_{M,K})` of the duality map are compared with the duality map of the trait by
the abstract identity `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` (blueprint
`det-tf-nearby-duality-proper` (1), (3)), applied to `G = Ra_*`, `G' = Ra'_*` and the proper
exchange `χ_a`. This file proves its concrete inputs:

* the lax monoidal structure of `Rf_*` on bounded constructible complexes, the right adjoint of
  the monoidal functor `Lf^*` (`ProEtale.CondensedRing.boundedConstructibleLowerStarLaxMonoidal`);
* the compatibility of the pushforward exchange `χ_f` with the lax tensor maps
  (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`), from the monoidality
  of the pullback exchange through the abstract computation
  `ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux` of the Künneth map, specialised
  to the diagonal;
* **global Verdier duality**: for a proper `k`-scheme `Z`, the duality map of `(Ra_*, μ, tr_Z)`
  is the Verdier exchange morphism `Ra_* RHom(K, ω_Z) ≅ RHom(Ra_! K, ℚ̄_ℓ)` read through
  `Ra_! ≅ Ra_*` (`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`), hence is an
  isomorphism (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`). The
  identification uses that the exceptional projection morphism of a proper morphism is the
  projection morphism of `Lf^* ⊣ Rf_!`
  (`ProEtale.CondensedRing.upperStar_map_exceptionalProjection_comp_counit`, blueprint
  `prop-sf-pf-coherence`).

With these, `RΓ(X', δ_{M,K})` is an isomorphism as soon as the proper exchange `χ_a` is invertible
and the duality map of the trait is invertible at `Ra_* K`
(`NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemmas -/

namespace CategoryTheory

namespace Verdier

section Abstract

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]

/-- The lax tensor map of the right adjoint `G` of an oplax monoidal functor `F` is adjoint to the
tensor product of the counits. -/
lemma map_rightAdjointLaxMonoidal_μ_comp_counit {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    [F.OplaxMonoidal] (A B : C) :
    F.map (letI := adj.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ G A B) ≫
        adj.counit.app (A ⊗ B) =
      Functor.OplaxMonoidal.δ F _ _ ≫ (adj.counit.app A ⊗ₘ adj.counit.app B) := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ]
  exact (adj.homEquiv_counit (g := _)).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)

/-- The compatibility of a pushforward exchange `χ : Rg ⋙ Ψ₁ ⟶ Ψ ⋙ Rg'` with the lax tensor maps
of `Ψ`, `Ψ₁` and of the right adjoints `Rg`, `Rg'`, in abstract categories: the Künneth
computation `ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux` for the diagonal,
from the monoidality of the pullback exchange `α : Ψ₁ ⋙ g' ⟶ g ⋙ Ψ` whose mate is `χ`. -/
lemma pushforwardExchange_tensor_aux {DX DX1 SX SX1 : Type*} [Category* DX] [Category* DX1]
    [Category* SX] [Category* SX1] [MonoidalCategory DX] [MonoidalCategory DX1]
    [MonoidalCategory SX] [MonoidalCategory SX1] {Ψ : DX ⥤ SX} {Ψ₁ : DX1 ⥤ SX1}
    {g : DX1 ⥤ DX} {g' : SX1 ⥤ SX} {Rg : DX ⥤ DX1} {Rg' : SX ⥤ SX1}
    [g.OplaxMonoidal] [g'.OplaxMonoidal] (ag : g ⊣ Rg) (ag' : g' ⊣ Rg')
    (μ : ∀ U V, Ψ.obj U ⊗ Ψ.obj V ⟶ Ψ.obj (U ⊗ V))
    (μ₁ : ∀ U V, Ψ₁.obj U ⊗ Ψ₁.obj V ⟶ Ψ₁.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : DX} (x : U ⟶ U') (y : V ⟶ V'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ U' V' = μ U V ≫ Ψ.map (x ⊗ₘ y))
    (α : Ψ₁ ⋙ g' ⟶ g ⋙ Ψ) (χ : Rg ⋙ Ψ₁ ⟶ Ψ ⋙ Rg')
    (hχ : ∀ A, g'.map (χ.app A) ≫ ag'.counit.app (Ψ.obj A) =
      α.app (Rg.obj A) ≫ Ψ.map (ag.counit.app A))
    (hα : ∀ U V, g'.map (μ₁ U V) ≫ α.app (U ⊗ V) ≫ Ψ.map (Functor.OplaxMonoidal.δ g U V) =
      Functor.OplaxMonoidal.δ g' _ _ ≫ (α.app U ⊗ₘ α.app V) ≫ μ (g.obj U) (g.obj V))
    (A B : DX) :
    (χ.app A ⊗ₘ χ.app B) ≫
        (letI := ag'.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg' _ _) ≫
          Rg'.map (μ A B) =
      μ₁ _ _ ≫ Ψ₁.map (letI := ag.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg A B) ≫
        χ.app (A ⊗ B) := by
  have h := AlgebraicGeometry.ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux
    (f₁ := 𝟭 DX) (f₂ := 𝟭 DX) (e₁ := 𝟭 DX1) (e₂ := 𝟭 DX1) (f₁' := 𝟭 SX) (f₂' := 𝟭 SX)
    (e₁' := 𝟭 SX1) (e₂' := 𝟭 SX1) ag ag ag ag' ag' ag' μ μ₁ hμ (𝟙 Ψ) (𝟙 Ψ) (𝟙 Ψ₁) (𝟙 Ψ₁)
    α α α χ χ χ hχ hχ hχ (𝟙 g) (𝟙 g) (𝟙 g') (𝟙 g') (𝟙 Rg) (𝟙 Rg) (𝟙 Rg') (𝟙 Rg')
    (fun _ ↦ by simp) (fun _ ↦ by simp) (fun _ ↦ by simp) (fun _ ↦ by simp)
    (letI := ag.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg)
    (letI := ag'.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg')
    (map_rightAdjointLaxMonoidal_μ_comp_counit ag) (map_rightAdjointLaxMonoidal_μ_comp_counit ag')
    (fun _ ↦ by simp) (fun _ ↦ by simp) hα A B
  simpa using h

variable [MonoidalClosed C] [MonoidalClosed D]

/-- **Global Verdier duality as a duality map**, in abstract categories: let `F ⊣ G` (for
`Lf^* ⊣ Rf_*`, `F` oplax monoidal) and `P ⊣ S` (for `Rf_! ⊣ Rf^!`), with an isomorphism
`e : P ≅ G` and a projection morphism `pf` which is the projection morphism of the adjunction
`F ⊣ P` transported along `e`. Then the duality map of `(G, μ_G, tr)`, `μ_G` the lax structure of
the right adjoint and `tr = ε' ∘ e⁻¹ : G S L ⟶ L`, read through `e`, is the Verdier exchange
morphism `G RHom(K, S L) ⟶ RHom(P K, L)`. -/
lemma nearbyDualityMap_comp_pre_eq_exchange {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    [F.OplaxMonoidal] {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S) (e : P ≅ G)
    (pf : curriedTensorInsertFunctor₁ P ⟶
      curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)
    (hpf : ∀ (T : C) (B : D), F.map ((pf.app T).app B) ≫
        (adj.ofNatIsoRight e.symm).counit.app (T ⊗ F.obj B) =
      Functor.OplaxMonoidal.δ F (P.obj T) B ≫
        (adj.ofNatIsoRight e.symm).counit.app T ▷ F.obj B)
    (K : C) (L : D) :
    nearbyDualityMap (letI := adj.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ G)
        (e.inv.app (S.obj L) ≫ adj'.counit.app L) K ≫ (pre (e.hom.app K)).app L =
      exchange adj adj' pf K L := by
  let := adj.rightAdjointLaxMonoidal
  have hc (Z : C) : (adj.ofNatIsoRight e.symm).counit.app Z =
      F.map (e.hom.app Z) ≫ adj.counit.app Z := by
    rw [← Adjunction.homEquiv_symm_id, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
      Adjunction.homEquiv_counit]
    simp
  -- the key identity: `pf` followed by the counit is `e_K ⊗ 1` followed by `μ_G`, through `e`
  have key (B : C) : e.hom.app K ▷ G.obj B ≫ Functor.LaxMonoidal.μ G K B =
      (pf.app K).app (G.obj B) ≫ P.map (K ◁ adj.counit.app B) ≫ e.hom.app (K ⊗ B) := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, F.map_comp, Category.assoc,
      map_rightAdjointLaxMonoidal_μ_comp_counit, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
      F.map_comp, F.map_comp, Category.assoc, Category.assoc, ← hc,
      Adjunction.counit_naturality]
    erw [reassoc_of% (hpf K (G.obj B))]
    rw [hc K, comp_whiskerRight, Category.assoc]
    simp [MonoidalCategory.tensorHom_def]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_nearbyDualityMap, uncurry_exchange, exchangePairing,
    reassoc_of% (key _), ← e.hom.naturality_assoc]
  simp

end Abstract

section Proper

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']
  {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]
  {D' : Type*} [Category* D'] [MonoidalCategory D'] [MonoidalClosed D']
  {ΨX : C ⥤ C'} {ΨY : D ⥤ D'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μY : ∀ A B : D, ΨY.obj A ⊗ ΨY.obj B ⟶ ΨY.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωY : D} {ωY' : D'} (θX : ΨX.obj ωX ⟶ ωX') (θY : ΨY.obj ωY ⟶ ωY')
  {G : C ⥤ D} {G' : C' ⥤ D'} (μG : ∀ A B : C, G.obj A ⊗ G.obj B ⟶ G.obj (A ⊗ B))
  (μG' : ∀ A B : C', G'.obj A ⊗ G'.obj B ⟶ G'.obj (A ⊗ B))
  (tr : G.obj ωX ⟶ ωY) (tr' : G'.obj ωX' ⟶ ωY')
  (χ : ∀ A : C, ΨY.obj (G.obj A) ⟶ G'.obj (ΨX.obj A))

/-- `CategoryTheory.Verdier.nearbyDualityMap_proper` for lax tensor maps `μ_G`, `μ_{G'}` given
explicitly (not through `Functor.LaxMonoidal` instances), `μ_{G'}` natural in its second
variable. -/
theorem nearbyDualityMap_proper'
    (hμG' : ∀ (A : C') {B B' : C'} (y : B ⟶ B'),
      G'.obj A ◁ G'.map y ≫ μG' A B' = μG' A B ≫ G'.map (A ◁ y))
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y))
    (hχ : ∀ {A B : C} (g : A ⟶ B), ΨY.map (G.map g) ≫ χ B = χ A ≫ G'.map (ΨX.map g))
    (hμ : ∀ A B : C, (χ A ⊗ₘ χ B) ≫ μG' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (μG A B) ≫ χ (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ ωX ≫ G'.map θX ≫ tr') (M : C) :
    ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M) =
      χ _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
        nearbyDualityMap μG' tr' (ΨX.obj M) ≫ (pre (χ M)).app ωY' := by
  apply uncurry_injective
  have hL : uncurry (ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M)) =
      μY _ _ ≫ ΨY.map (μG _ _) ≫ ΨY.map (G.map ((ihom.ev M).app ωX)) ≫ ΨY.map tr ≫ θY := by
    have hl : ΨY.obj (G.obj M) ◁ ΨY.map (nearbyDualityMap μG tr M) ≫ μY _ _ =
        μY _ _ ≫ ΨY.map (G.obj M ◁ nearbyDualityMap μG tr M) := by
      have := hμY (𝟙 (G.obj M)) (nearbyDualityMap μG tr M)
      rwa [ΨY.map_id, id_tensorHom, id_tensorHom] at this
    rw [uncurry_natural_left, uncurry_nearbyDualityMap, reassoc_of% hl, ← ΨY.map_comp_assoc,
      ← uncurry_eq, uncurry_nearbyDualityMap]
    simp only [Functor.map_comp, Category.assoc]
  have hR : uncurry (χ _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
      nearbyDualityMap μG' tr' (ΨX.obj M) ≫ (pre (χ M)).app ωY') =
      (χ M ⊗ₘ χ _) ≫ μG' _ _ ≫ G'.map (μX _ _) ≫
        G'.map (ΨX.map ((ihom.ev M).app ωX)) ≫ G'.map θX ≫ tr' := by
    rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_left,
      uncurry_nearbyDualityMap, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% (hμG' _ (nearbyDualityMap μX θX M)), ← G'.map_comp_assoc, ← uncurry_eq,
      uncurry_nearbyDualityMap, MonoidalCategory.tensorHom_def]
    simp only [Functor.map_comp, Category.assoc]
  rw [hL, hR, reassoc_of% (hμ M _),
    ← reassoc_of% (hχ (A := M ⊗ (ihom M).obj ωX) (B := ωX) ((ihom.ev M).app ωX)), ← hθ]

/-- `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` for lax tensor maps `μ_G`,
`μ_{G'}` given explicitly, with the invertibility hypotheses as explicit arguments. -/
theorem isIso_map_nearbyDualityMap_of_proper'
    (hμG' : ∀ (A : C') {B B' : C'} (y : B ⟶ B'),
      G'.obj A ◁ G'.map y ≫ μG' A B' = μG' A B ≫ G'.map (A ◁ y))
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y))
    (hχ : ∀ {A B : C} (g : A ⟶ B), ΨY.map (G.map g) ≫ χ B = χ A ≫ G'.map (ΨX.map g))
    (hμ : ∀ A B : C, (χ A ⊗ₘ χ B) ≫ μG' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (μG A B) ≫ χ (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ ωX ≫ G'.map θX ≫ tr') (M : C)
    (h₁ : IsIso (χ M)) (h₂ : IsIso (χ ((ihom M).obj ωX)))
    (h₃ : IsIso (nearbyDualityMap μG tr M)) (h₄ : IsIso (nearbyDualityMap μG' tr' (ΨX.obj M)))
    (h₅ : IsIso (nearbyDualityMap μY θY (G.obj M))) :
    IsIso (G'.map (nearbyDualityMap μX θX M)) := by
  have e := nearbyDualityMap_proper' μX μY θX θY μG μG' tr tr' χ hμG' hμY hχ hμ hθ M
  have : IsIso ((pre (χ M)).app ωY') :=
    ⟨(pre (inv (χ M))).app ωY', by rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id,
      pre_id, NatTrans.id_app], by rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id,
      NatTrans.id_app]⟩
  have h : G'.map (nearbyDualityMap μX θX M) =
      inv (χ _) ≫ (ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M)) ≫
        inv ((pre (χ M)).app ωY') ≫ inv (nearbyDualityMap μG' tr' (ΨX.obj M)) := by
    rw [e]
    simp
  rw [h]
  infer_instance

end Proper

section Rigid

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']

omit [MonoidalClosed C] [MonoidalClosed C'] in
/-- A monoidal functor carries the counit `X ⊗ (Y ⊗ K) ⟶ K` of the adjunction
`tensorLeft X ⊣ tensorLeft Y` of an exact pairing to the counit of the image exact pairing
(`CategoryTheory.ExactPairing.map`), up to the tensor maps. -/
lemma μ_comp_map_tensorLeftAdjunction_counit_app (F : C ⥤ C') [F.Monoidal] (Y X K : C)
    [ExactPairing Y X] :
    Functor.LaxMonoidal.μ F X (Y ⊗ K) ≫ F.map ((tensorLeftAdjunction Y X).counit.app K) =
      F.obj X ◁ Functor.OplaxMonoidal.δ F Y K ≫
        (@tensorLeftAdjunction C' _ _ (F.obj Y) (F.obj X)
          (ExactPairing.map F Y X)).counit.app (F.obj K) := by
  let := ExactPairing.map F Y X
  rw [tensorLeftAdjunction_counit_app, tensorLeftAdjunction_counit_app]
  change _ = _ ≫ (α_ _ _ _).inv ≫ (Functor.LaxMonoidal.μ F X Y ≫ F.map (ε_ Y X) ≫
    Functor.OplaxMonoidal.η F) ▷ F.obj K ≫ (λ_ _).hom
  simp only [Functor.map_comp, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, comp_whiskerRight, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [Functor.Monoidal.map_leftUnitor F K, Functor.Monoidal.μ_δ_assoc]

/-- **Monoidal functors commute with duals**: for a monoidal functor `F` (lax tensor maps `μ`,
dualizing map the inverse `η` of the unit map) and an object `X` with a left dual `Y`, the duality
map `F RHom(X, 𝟙) ⟶ RHom(F X, 𝟙)` is an isomorphism. Both internal homs are identified with
tensoring with the duals `Y` and `F Y` (`CategoryTheory.ExactPairing.map`), and under these
identifications the duality map is `F (Y ⊗ 𝟙) ≅ F Y ⊗ F 𝟙 ≅ F Y ⊗ 𝟙`. -/
theorem isIso_nearbyDualityMap_of_monoidal (F : C ⥤ C') [F.Monoidal] (Y X : C)
    [ExactPairing Y X] :
    IsIso (nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B)
      (Functor.OplaxMonoidal.η F) X) := by
  let := ExactPairing.map F Y X
  let s := (tensorLeftAdjunction Y X).rightAdjointUniq (ihom.adjunction X)
  let s' := (tensorLeftAdjunction (F.obj Y) (F.obj X)).rightAdjointUniq
    (ihom.adjunction (F.obj X))
  have e1 : X ◁ s.hom.app (𝟙_ C) ≫ (ihom.ev X).app (𝟙_ C) =
      (tensorLeftAdjunction Y X).counit.app (𝟙_ C) :=
    (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) (𝟙_ C)
  have e2 : F.obj X ◁ s'.hom.app (𝟙_ C') ≫ (ihom.ev (F.obj X)).app (𝟙_ C') =
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (𝟙_ C') :=
    (tensorLeftAdjunction (F.obj Y) (F.obj X)).rightAdjointUniq_hom_app_counit
      (ihom.adjunction (F.obj X)) (𝟙_ C')
  have e3 : F.obj X ◁ F.obj Y ◁ Functor.OplaxMonoidal.η F ≫
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (𝟙_ C') =
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (F.obj (𝟙_ C)) ≫
        Functor.OplaxMonoidal.η F :=
    (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.naturality (Functor.OplaxMonoidal.η F)
  have h : F.map (s.hom.app (𝟙_ C)) ≫ nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B)
      (Functor.OplaxMonoidal.η F) X =
      Functor.OplaxMonoidal.δ F Y (𝟙_ C) ≫ F.obj Y ◁ Functor.OplaxMonoidal.η F ≫
        s'.hom.app (𝟙_ C') := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_nearbyDualityMap, Functor.LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp_assoc, e1]
    erw [reassoc_of% (μ_comp_map_tensorLeftAdjunction_counit_app F Y X (𝟙_ C))]
    rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Category.assoc, e2, e3]
  have : IsIso (F.map (s.hom.app (𝟙_ C)) ≫ nearbyDualityMap
      (fun A B ↦ Functor.LaxMonoidal.μ F A B) (Functor.OplaxMonoidal.η F) X) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (s.hom.app (𝟙_ C))) _

end Rigid

end Verdier

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-! ### The lax monoidal structure of the direct image -/

section LaxMonoidal

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

variable (Λ ℓ) in
/-- The lax monoidal structure of the derived direct image `Rf_*` on bounded constructible
complexes: the right adjoint of the monoidal functor `Lf^*`. Its tensor maps are adjoint to the
tensor products of the counits (`CategoryTheory.Verdier.map_rightAdjointLaxMonoidal_μ_comp_counit`).
It is not an instance. -/
noncomputable abbrev boundedConstructibleLowerStarLaxMonoidal :
    (boundedConstructibleLowerStar Λ ℓ f).LaxMonoidal :=
  (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).rightAdjointLaxMonoidal

/-- The comparison `δ` of the restricted pullback is that of the ambient derived pullback. -/
lemma δ_boundedConstructibleUpperStar_hom' (A B : Dᵇc(Y.left)⟦Λ⟧) :
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) A B).hom =
      Functor.OplaxMonoidal.δ L((f.left)^*⟦Λ⟧) A.obj B.obj :=
  rfl

end LaxMonoidal

/-! ### The pushforward exchange and the lax tensor maps -/

namespace NearbyCyclesModel

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible Λ) (hN : N.PreservesBoundedConstructible Λ)

/-- The restricted pushforward exchange is the mate of the restricted pullback exchange:
compatibility with the counits of `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma Hom.map_boundedConstructiblePushforwardExchange_app_comp_counit_app
    (A : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ f').map
        ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').counit.app
          ((boundedConstructibleNearbyCycles hM).obj A) =
      (φ.boundedConstructiblePullbackExchange ℓ hM hN).app
          ((boundedConstructibleLowerStar Λ ℓ f).obj A) ≫
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit.app A) := by
  rw [Hom.boundedConstructiblePushforwardExchange_eq_mateEquiv]
  exact mateEquiv_counit _ _ _ A

/-- The oplax monoidality of `NearbyCyclesModel.liftExchange` of an arbitrary transformation
`α : Ψ_N ⋙ Lf'^* ⟶ Lf^* ⋙ Ψ_M`, deduced from that of `α`; the transformation is kept abstract so
that the kernel never unfolds the pullback exchange. -/
private lemma liftExchange_tensor_oplax_aux
    (α : N.nearbyCycles Λ ⋙ L((f'.left)^*⟦Λ⟧) ⟶ L((f.left)^*⟦Λ⟧) ⋙ M.nearbyCycles Λ)
    (hα : ∀ A B, L((f'.left)^*⟦Λ⟧).map (N.tensorMap Λ A B) ≫ α.app (A ⊗ B) ≫
          (M.nearbyCycles Λ).map (Functor.OplaxMonoidal.δ L((f.left)^*⟦Λ⟧) A B) =
      Functor.OplaxMonoidal.δ L((f'.left)^*⟦Λ⟧) _ _ ≫
        (α.app A ⊗ₘ α.app B) ≫ M.tensorMap Λ _ _)
    (β : boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleUpperStar Λ ℓ f' ⟶
        boundedConstructibleUpperStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hM)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K.obj K.property))
    (A B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ f').map (boundedConstructibleTensorMap hN A B) ≫
        β.app (A ⊗ B) ≫ (boundedConstructibleNearbyCycles hM).map
          (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) A B) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f') _ _ ≫
        (β.app A ⊗ₘ β.app B) ≫ boundedConstructibleTensorMap hM _ _ := by
  subst hβ
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    δ_boundedConstructibleUpperStar_hom', ObjectProperty.tensorHom_hom', liftExchange_app_hom]
  exact hα A.obj B.obj

/-- **The restricted pullback exchange is monoidal**, in the oplax form: the restriction of
`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`. -/
lemma Hom.boundedConstructiblePullbackExchange_tensor_oplax (A B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ f').map (boundedConstructibleTensorMap hN A B) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hM hN).app (A ⊗ B) ≫
        (boundedConstructibleNearbyCycles hM).map
          (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) A B) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f') _ _ ≫
        ((φ.boundedConstructiblePullbackExchange ℓ hM hN).app A ⊗ₘ
          (φ.boundedConstructiblePullbackExchange ℓ hM hN).app B) ≫
        boundedConstructibleTensorMap hM _ _ :=
  liftExchange_tensor_oplax_aux hM hN (φ.pullbackExchange _)
    (φ.map_tensorMap_comp_pullbackExchange_app _) _
    (φ.boundedConstructiblePullbackExchange_eq_liftExchange' hM hN) A B

/-- **The pushforward exchange is compatible with the lax tensor maps** (blueprint
`det-tf-nearby-duality-proper` (1), "the lax products commute through proper exchange"): with the
lax monoidal structures of `Rf_*` and `Rf'_*` (`boundedConstructibleLowerStarLaxMonoidal`),
`Rf'_*(μ_M) ∘ μ_{Rf'_*} ∘ (χ ⊗ χ) = χ ∘ Ψ_N(μ_{Rf_*}) ∘ μ_N`. Both sides have the same adjoint,
the tensor product of the generic-open counits, by the monoidality of the pullback exchange
(`CategoryTheory.Verdier.pushforwardExchange_tensor_aux`). -/
lemma Hom.boundedConstructiblePushforwardExchange_tensor (A B : Dᵇc(X.left)⟦Λ⟧) :
    ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app A ⊗ₘ
        (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app B) ≫
        (letI := boundedConstructibleLowerStarLaxMonoidal Λ ℓ f';
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar Λ ℓ f') _ _) ≫
        (boundedConstructibleLowerStar Λ ℓ f').map (boundedConstructibleTensorMap hM A B) =
      boundedConstructibleTensorMap hN _ _ ≫ (boundedConstructibleNearbyCycles hN).map
          (letI := boundedConstructibleLowerStarLaxMonoidal Λ ℓ f;
            Functor.LaxMonoidal.μ (boundedConstructibleLowerStar Λ ℓ f) A B) ≫
        (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app (A ⊗ B) :=
  Verdier.pushforwardExchange_tensor_aux (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
    (boundedConstructibleTensorMap hM) (boundedConstructibleTensorMap hN)
    (fun x y ↦ boundedConstructibleTensorMap_natural hM x y)
    (φ.boundedConstructiblePullbackExchange ℓ hM hN)
    (φ.boundedConstructiblePushforwardExchange ℓ hM hN)
    (φ.map_boundedConstructiblePushforwardExchange_app_comp_counit_app hM hN)
    (φ.boundedConstructiblePullbackExchange_tensor_oplax hM hN) A B

end NearbyCyclesModel

/-! ### Global Verdier duality -/

section Global

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left]

/-- **Global Verdier duality** (blueprint `det-tf-nearby-duality-proper` (3), "global Verdier
duality"): for a proper `k`-scheme `Z` with structure morphism `a`, the duality map
`Ra_* D_Z K ⟶ RHom(Ra_* K, ℚ̄_ℓ)` of `(Ra_*, μ, tr_Z)` (`μ` the lax structure
`boundedConstructibleLowerStarLaxMonoidal`, `tr_Z` the trace `NearbyCyclesModel.trace`) is an
isomorphism: read through `Ra_! ≅ Ra_*` it is the Verdier exchange morphism
(`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`), an isomorphism by
`ProEtale.CondensedRing.isIso_verdierExchange`. -/
theorem isIso_nearbyDualityMap_lowerStar_trace (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (letI := boundedConstructibleLowerStarLaxMonoidal (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint Z);
        Functor.LaxMonoidal.μ (boundedConstructibleLowerStar _ ℓ (toPoint Z)))
      (NearbyCyclesModel.trace ℓ Z) K) := by
  have e := Verdier.nearbyDualityMap_comp_pre_eq_exchange
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (toPoint Z))
    (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint Z))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z))
    (boundedConstructibleExceptionalProjection _ ℓ (toPoint Z))
    (fun T B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ (toPoint Z) T B) K (𝟙_ _)
  have h₁ : IsIso (Verdier.exchange
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (toPoint Z))
      (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint Z))
      (boundedConstructibleExceptionalProjection _ ℓ (toPoint Z)) K (𝟙_ _)) :=
    isIso_verdierExchange ℓ (toPoint Z) K (𝟙_ _)
  have h₂ := isIso_pre_app
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).hom.app K) (𝟙_ _)
  rw [← e] at h₁
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ h₁

end Global

/-! ### Global sections of the duality map -/

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- **The nearby cycles of the trait are monoidal on the base point**: the nearby cycles
`Ψ_S : Dᵇc(Spec k) ⥤ Dᵇc(Spec k')` of the trait `S` as a model of `Spec k` are a monoidal functor
with tensor maps the lax tensor maps of nearby cycles (`boundedConstructibleTensorMap`) and unit
map the specialization unit `σ_s` (`traitSpecializationUnit`).

Unfinished. Two inputs are missing. (a) The lax tensor maps and the specialization unit of
nearby cycles satisfy the associativity and unit axioms of a lax monoidal functor: with
`Ψ = Li^* ∘ Rj_* ∘ Lε^*`, they are those of the composite of the monoidal functors `Li^*`, `Lε^*`
and of the lax monoidal right adjoint `Rj_*` (`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`).
(b) The tensor maps are invertible: `Lε^* A` is a finite direct sum of shifts of the unit on the
geometric generic point `Spec Ω` (`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), where
the Künneth map of the trait is invertible
(`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_of_shiftDecomposition`); the unit map
`σ_s` is invertible by `ProEtale.CondensedRing.isIso_traitSpecializationUnit`. -/
theorem exists_monoidal_traitSpecialization :
    ∃ L : (boundedConstructibleNearbyCycles
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)).Monoidal,
      (∀ A B, (letI := L; Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles
          (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) A B) =
        boundedConstructibleTensorMap (preservesBoundedConstructible_traitModel ℓ) A B) ∧
      (letI := L; Functor.LaxMonoidal.ε (boundedConstructibleNearbyCycles
          (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))) =
        traitSpecializationUnit k k' (ℓ := ℓ) :=
  sorry

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- **The duality map of the trait itself** (blueprint `det-tf-nearby-duality-proper` (3), "with
`θ_S` the identity of `A` the normalized pairing on `S` is ordinary evaluation"): for the trait `S`
as a model of the base point `Spec k`, with the lax tensor map of its nearby cycles and the inverse
of the specialization unit as dualizing map, the duality map
`δ_{S,N} : Ψ_S RHom(N, ℚ̄_ℓ) ⟶ RHom(Ψ_S N, ℚ̄_ℓ)` is an isomorphism for every bounded
constructible `N` on `Spec k`: `Ψ_S` is monoidal (`exists_monoidal_traitSpecialization`), `N` is
dualizable (`ProEtale.CondensedRing.nonempty_hasLeftDual_point`), and monoidal functors commute
with duals (`CategoryTheory.Verdier.isIso_nearbyDualityMap_of_monoidal`). -/
theorem isIso_nearbyDualityMap_traitModel
    (N : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
      (inv (traitSpecializationUnit k k' (ℓ := ℓ))) N) := by
  obtain ⟨L, hμ, hε⟩ := exists_monoidal_traitSpecialization ℓ (k := k) (k' := k')
  obtain ⟨hN⟩ := nonempty_hasLeftDual_point ℓ (k := k) N
  let := L
  have h := Verdier.isIso_nearbyDualityMap_of_monoidal (boundedConstructibleNearbyCycles
    (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) (ᘁN) N
  have e₁ : (fun A B ↦ Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles
      (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) A B) =
      boundedConstructibleTensorMap (preservesBoundedConstructible_traitModel ℓ) :=
    funext₂ hμ
  have e₂ : Functor.OplaxMonoidal.η (boundedConstructibleNearbyCycles
      (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) =
      inv (traitSpecializationUnit k k' (ℓ := ℓ)) :=
    IsIso.eq_inv_of_hom_inv_id (by rw [← hε]; exact Functor.Monoidal.ε_η _)
  rw [e₁, e₂] at h
  exact h

/-- **Global sections of the duality map of a proper model, reduced to the trait** (blueprint
`det-tf-nearby-duality-proper` (1) and (3)): if `X`, `X'` and the total space of the trait model
`M` over the base are proper, then `RΓ(X', δ_{M,K})` is an isomorphism as soon as the proper
exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure morphism is invertible (it is used at `K`
and `D_X K`), and the duality map of the trait `S` itself (lax tensor map of its nearby cycles,
dualizing map the inverse of the specialization unit `σ_s`) is invertible at `Ra_* K`. This is
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper'`, with the compatibility of `χ_a`
with the lax tensor maps (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`),
the proper axiom of the dualizing maps
(`NearbyCyclesModel.NearbyDualizingData.pushforwardExchange_comp_map_θ_comp_trace`) and global
Verdier duality on both fibres (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`).

The invertibility of `χ_a` needs the geometric generic fibre of `M` to be all of `X ×_k Spec Ω`
(not only an open of it, as `NearbyCyclesModel.IsTraitModelOfBase` allows): for
`X = Spec k ⊔ Spec k` and the trait `S` itself as total space, mapping to the first copy, `χ_a`
kills `Ψ_S Ra_*` of the unit of the second copy.
-/
theorem isIso_lowerStar_nearbyDualityMap_of_isIso (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hχ : ∀ A, IsIso ((h.pushforwardExchange ℓ).app A))
    [IsIso (Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
      (inv (traitSpecializationUnit k k' (ℓ := ℓ)))
      ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K))] :
    IsIso ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint X')).map (nearbyDualityMap ℓ D h K)) := by
  let _ := boundedConstructibleLowerStarLaxMonoidal (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)
  let _ := boundedConstructibleLowerStarLaxMonoidal (Profinite.padicAlgClRingObj ℓ) ℓ
    (toPoint X')
  have hθ := (D.pushforwardExchange_comp_map_θ_comp_trace h hgen).symm
  have t₁ : h.pushforwardExchange ℓ = h.toTrait.boundedConstructiblePushforwardExchange ℓ
      (h.preservesBoundedConstructible ℓ) (preservesBoundedConstructible_traitModel ℓ) := rfl
  rw [t₁] at hθ hχ
  exact Verdier.isIso_map_nearbyDualityMap_of_proper'
    (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ))
    (boundedConstructibleTensorMap (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
    (D.θ h) (inv (traitSpecializationUnit k k' (ℓ := ℓ)))
    (Functor.LaxMonoidal.μ (boundedConstructibleLowerStar _ ℓ (toPoint X)))
    (Functor.LaxMonoidal.μ (boundedConstructibleLowerStar _ ℓ (toPoint X')))
    (trace ℓ X) (trace ℓ X') (fun A ↦ (h.toTrait.boundedConstructiblePushforwardExchange ℓ
      (h.preservesBoundedConstructible ℓ) (preservesBoundedConstructible_traitModel ℓ)).app A)
    (fun A _ _ y ↦ Functor.LaxMonoidal.μ_natural_right _ A y)
    (fun x y ↦ boundedConstructibleTensorMap_natural _ x y)
    (fun u ↦ (h.toTrait.boundedConstructiblePushforwardExchange ℓ
      (h.preservesBoundedConstructible ℓ)
      (preservesBoundedConstructible_traitModel ℓ)).naturality u)
    (fun A B ↦ h.toTrait.boundedConstructiblePushforwardExchange_tensor
      (h.preservesBoundedConstructible ℓ) (preservesBoundedConstructible_traitModel ℓ) A B)
    hθ K (hχ K) (hχ _) (isIso_nearbyDualityMap_lowerStar_trace ℓ X K)
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X' _) ‹_›

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
