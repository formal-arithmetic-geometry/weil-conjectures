/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarTensor

/-!
# Pullback of `ℓ`-adic sheaves commutes with tensor products, compatibly with exchanges

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ : Scheme.{u}}

/-- The quotient map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M` is compatible with the comparison
`g^*(P ⊗_{ℚ̄_ℓ} M) ≅ g^*P ⊗_{ℚ̄_ℓ} g^*M`. -/
@[reassoc]
lemma adicUpperStar_map_tensorπ_comp_tensorLeftIso_hom {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (P M : AdicSheaf l Y) :
    (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
        ((adicUpperStarTensorLeftIso l g M).hom.app P).hom =
      inv (μ (g)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        Mod.tensorπ ((g)^*ᵃ[l].obj P) ((g)^*ᵃ[l].obj M) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  exact Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _) P M

/-- The quotient map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M` is compatible with the comparison
`g_*(P ⊗_{ℚ̄_ℓ} M) ≅ g_*P ⊗_{ℚ̄_ℓ} g_*M` along an automorphism `g`. -/
@[reassoc]
lemma adicLowerStar_map_tensorπ_comp_tensorLeftIso_hom {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    (P M : AdicSheaf l X) :
    (g)_*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
        ((adicLowerStarTensorLeftIso l g M).hom.app P).hom =
      inv (μ (g)_*[WeilCoefficients.{u} l] P.X M.X) ≫
        Mod.tensorπ ((g)_*ᵃ[l].obj P) ((g)_*ᵃ[l].obj M) := by
  have : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  exact Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) P M

/-- The quotient map `j^* P ⊗ j^* M ⟶ j^*(P ⊗_{ℚ̄_ℓ} M)` followed by `g_*` and the comparisons
`g_* j^*(P ⊗_{ℚ̄_ℓ} M) ≅ g_* j^* P ⊗_{ℚ̄_ℓ} g_* j^* M`, for an automorphism `g`, is the quotient
map. -/
lemma adicLowerStar_upperStar_map_tensorπ_comp (j : T₁ ⟶ T₂) (g : T₁ ⟶ T₁) [IsIso g]
    (P M : AdicSheaf l T₂) :
    μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫
        (g)_*[WeilCoefficients.{u} l].map ((adicUpperStarTensorLeftIso l j M).hom.app P).hom ≫
        ((adicLowerStarTensorLeftIso l g ((j)^*ᵃ[l].obj M)).hom.app ((j)^*ᵃ[l].obj P)).hom =
      Mod.tensorπ ((g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj P)) ((g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj M)) := by
  have h₁ : μ (j)^*[WeilCoefficients.{u} l] P.X M.X ≫
      (j)^*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
        ((adicUpperStarTensorLeftIso l j M).hom.app P).hom =
      Mod.tensorπ ((j)^*ᵃ[l].obj P) ((j)^*ᵃ[l].obj M) := by
    rw [adicUpperStar_map_tensorπ_comp_tensorLeftIso_hom, IsIso.hom_inv_id_assoc]
  have h₂ := adicLowerStar_map_tensorπ_comp_tensorLeftIso_hom (l := l) g ((j)^*ᵃ[l].obj P)
    ((j)^*ᵃ[l].obj M)
  rw [← Functor.map_comp_assoc (g)_*[WeilCoefficients.{u} l] _
    ((adicUpperStarTensorLeftIso l j M).hom.app P).hom,
    ← Functor.map_comp_assoc (g)_*[WeilCoefficients.{u} l] (μ _ _ _), h₁]
  exact (congrArg (_ ≫ ·) h₂).trans (IsIso.hom_inv_id_assoc _ _)

/-- Two morphisms out of `g_* j^*(P ⊗_{ℚ̄_ℓ} M)`, for an automorphism `g`, agreeing on
`g_* j^* P ⊗ g_* j^* M` are equal. -/
lemma adicLowerStar_upperStar_tensor_hom_ext (j : T₁ ⟶ T₂) (g : T₁ ⟶ T₁) [IsIso g]
    {P M : AdicSheaf l T₂} {N : AdicSheaf l T₁}
    {f₁ f₂ : (g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj ((Mod.tensorLeft M).obj P)) ⟶ N}
    (h : μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫ f₁.hom =
      μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫ f₂.hom) :
    f₁ = f₂ := by
  let Φ := (g)_*ᵃ[l].mapIso ((adicUpperStarTensorLeftIso l j M).app P) ≪≫
    (adicLowerStarTensorLeftIso l g ((j)^*ᵃ[l].obj M)).app ((j)^*ᵃ[l].obj P)
  have hΦ : μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫ Φ.hom.hom =
        Mod.tensorπ ((g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj P)) ((g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj M)) :=
    adicLowerStar_upperStar_map_tensorπ_comp j g P M
  rw [← Φ.hom_inv_id_assoc f₁, ← Φ.hom_inv_id_assoc f₂]
  congr 1
  refine Mod.tensorLeft_obj_hom_ext' ?_
  rw [← hΦ, Mod.comp_hom', Mod.comp_hom']
  simp only [Category.assoc]
  have hh : Φ.hom.hom ≫ Φ.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Φ.hom_inv_id]
    rfl
  rw [reassoc_of% hh, reassoc_of% hh]
  exact h

/-- The exchange isomorphism of `ℓ`-adic sheaves is natural with respect to morphisms of the
underlying sheaves. -/
lemma adicUpperStarExchange_hom_app_hom_naturality (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (X : AdicSheaf l T₂)
    {Z : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)} (f : Z ⟶ X.X) :
    (a.inv)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map f) ≫
      ((adicUpperStarExchange l j a b c).hom.app X).hom =
    (upperStarExchange l j a b c).hom.app Z ≫
      (j)^*[WeilCoefficients.{u} l].map ((b.inv)_*[WeilCoefficients.{u} l].map f) :=
  (congrArg (fun x ↦ _ ≫ x) (adicUpperStarExchange_hom_app_hom j a b c X)).trans
    ((upperStarExchange l j a b c).hom.naturality f)

@[reassoc]
lemma upperStarExchange_μ (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (X Y : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)) :
    μ (a.inv)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj X)
        ((j)^*[WeilCoefficients.{u} l].obj Y) ≫
      (a.inv)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] X Y) ≫
      (upperStarExchange l j a b c).hom.app (X ⊗ Y) =
    ((upperStarExchange l j a b c).hom.app X ⊗ₘ (upperStarExchange l j a b c).hom.app Y) ≫
      μ (j)^*[WeilCoefficients.{u} l] ((b.inv)_*[WeilCoefficients.{u} l].obj X)
        ((b.inv)_*[WeilCoefficients.{u} l].obj Y) ≫
      (j)^*[WeilCoefficients.{u} l].map (μ (b.inv)_*[WeilCoefficients.{u} l] X Y) := by
  simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc] using
    NatTrans.IsMonoidal.tensor (τ := (upperStarExchange l j a b c).hom) X Y

lemma adicUpperStar_lowerStar_map_tensorπ_comp (j : T₁ ⟶ T₂) (b : T₂ ≅ T₂)
    (P M : AdicSheaf l T₂) :
    μ (j)^*[WeilCoefficients.{u} l] ((b.inv)_*[WeilCoefficients.{u} l].obj P.X)
          ((b.inv)_*[WeilCoefficients.{u} l].obj M.X) ≫
        (j)^*[WeilCoefficients.{u} l].map (μ (b.inv)_*[WeilCoefficients.{u} l] P.X M.X) ≫
        (j)^*[WeilCoefficients.{u} l].map ((b.inv)_*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫
        (j)^*[WeilCoefficients.{u} l].map ((adicLowerStarTensorLeftIso l b.inv M).hom.app P).hom ≫
        ((adicUpperStarTensorLeftIso l j ((b.inv)_*ᵃ[l].obj M)).hom.app
          ((b.inv)_*ᵃ[l].obj P)).hom =
      Mod.tensorπ ((j)^*ᵃ[l].obj ((b.inv)_*ᵃ[l].obj P)) ((j)^*ᵃ[l].obj ((b.inv)_*ᵃ[l].obj M)) := by
  have h₁ : μ (b.inv)_*[WeilCoefficients.{u} l] P.X M.X ≫
      (b.inv)_*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
        ((adicLowerStarTensorLeftIso l b.inv M).hom.app P).hom =
      Mod.tensorπ ((b.inv)_*ᵃ[l].obj P) ((b.inv)_*ᵃ[l].obj M) := by
    rw [adicLowerStar_map_tensorπ_comp_tensorLeftIso_hom, IsIso.hom_inv_id_assoc]
  have h₂ := adicUpperStar_map_tensorπ_comp_tensorLeftIso_hom (l := l) j ((b.inv)_*ᵃ[l].obj P)
    ((b.inv)_*ᵃ[l].obj M)
  rw [← Functor.map_comp_assoc (j)^*[WeilCoefficients.{u} l] _
    ((adicLowerStarTensorLeftIso l b.inv M).hom.app P).hom,
    ← Functor.map_comp_assoc (j)^*[WeilCoefficients.{u} l] (μ _ _ _), h₁]
  exact (congrArg (_ ≫ ·) h₂).trans (IsIso.hom_inv_id_assoc _ _)

/-- The exchange isomorphism of `ℓ`-adic sheaves on a morphism out of a tensor product of the
underlying sheaves, through the monoidal structures. -/
lemma adicUpperStarExchange_μ_naturality (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (X : AdicSheaf l T₂)
    {Y Z : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)} (f : Y ⊗ Z ⟶ X.X) :
    μ (a.inv)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj Y)
        ((j)^*[WeilCoefficients.{u} l].obj Z) ≫
      (a.inv)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] Y Z) ≫
      (a.inv)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map f) ≫
      ((adicUpperStarExchange l j a b c).hom.app X).hom =
    ((upperStarExchange l j a b c).hom.app Y ⊗ₘ (upperStarExchange l j a b c).hom.app Z) ≫
      μ (j)^*[WeilCoefficients.{u} l] ((b.inv)_*[WeilCoefficients.{u} l].obj Y)
        ((b.inv)_*[WeilCoefficients.{u} l].obj Z) ≫
      (j)^*[WeilCoefficients.{u} l].map (μ (b.inv)_*[WeilCoefficients.{u} l] Y Z) ≫
      (j)^*[WeilCoefficients.{u} l].map ((b.inv)_*[WeilCoefficients.{u} l].map f) := by
  rw [adicUpperStarExchange_hom_app_hom_naturality, upperStarExchange_μ_assoc]

/-- **The comparison `j^*(P ⊗ M) ≅ j^* P ⊗ j^* M` is compatible with the exchange
isomorphisms** `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` of `ℓ`-adic sheaves. -/
@[reassoc]
lemma adicUpperStarTensorLeftIso_exchange (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (P M : AdicSheaf l T₂) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l j M).hom.app P) ≫
        (adicLowerStarTensorLeftIso l a.inv ((j)^*ᵃ[l].obj M)).hom.app ((j)^*ᵃ[l].obj P) ≫
        (Mod.tensorLeftMap ((adicUpperStarExchange l j a b c).hom.app M)).app _ ≫
        (Mod.tensorLeft _).map ((adicUpperStarExchange l j a b c).hom.app P) =
      (adicUpperStarExchange l j a b c).hom.app ((Mod.tensorLeft M).obj P : AdicSheaf l T₂) ≫
        (j)^*ᵃ[l].map ((adicLowerStarTensorLeftIso l b.inv M).hom.app P) ≫
        (adicUpperStarTensorLeftIso l j ((b.inv)_*ᵃ[l].obj M)).hom.app
          ((b.inv)_*ᵃ[l].obj P) := by
  refine adicLowerStar_upperStar_tensor_hom_ext j a.inv ?_
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicUpperStar_map_hom]
  rw [reassoc_of% (adicLowerStar_upperStar_map_tensorπ_comp j a.inv P M),
    Mod.tensorπ_tensorLeftMap_assoc, Mod.tensorπ_map, ← tensorHom_def'_assoc]
  rw [reassoc_of% (adicUpperStarExchange_μ_naturality j a b c
    ((Mod.tensorLeft M).obj P : AdicSheaf l T₂) (Mod.tensorπ P M))]
  rw [adicUpperStar_lowerStar_map_tensorπ_comp, adicUpperStarExchange_hom_app_hom j a b c
    (P : AdicSheaf l T₂), adicUpperStarExchange_hom_app_hom j a b c (M : AdicSheaf l T₂)]
  rfl

/-- The comparison `g^*(P ⊗_{ℚ̄_ℓ} M) ≅ g^*P ⊗_{ℚ̄_ℓ} g^*M` is natural in `M`. -/
@[reassoc]
lemma adicUpperStar_map_tensorLeftMap_app_tensorLeftIso_hom {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {M M' : AdicSheaf l Y} (f : M ⟶ M') (P : AdicSheaf l Y) :
    (g)^*ᵃ[l].map ((Mod.tensorLeftMap f).app P) ≫ (adicUpperStarTensorLeftIso l g M').hom.app P =
      (adicUpperStarTensorLeftIso l g M).hom.app P ≫
        (Mod.tensorLeftMap ((g)^*ᵃ[l].map f)).app ((g)^*ᵃ[l].obj P) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  exact Mod.map_tensorLeftMap_app_tensorLeftCompMapModComapIso_hom_app (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _) f P

/-- **The comparison `j^*(P ⊗ M) ≅ j^* P ⊗ j^* M` is compatible with the structure morphisms of
tensor products**: given structure morphisms `sM : (b⁻¹)_* M ⟶ M` and `sP : (b⁻¹)_* P ⟶ P`, it
intertwines the structure morphism of `P ⊗ M` transported along the exchange isomorphism with the
structure morphism of the tensor product of the transported structure morphisms. -/
lemma adicUpperStarTensorLeftIso_tensorStr_comm (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (P M : AdicSheaf l T₂) (sM : (b.inv)_*ᵃ[l].obj M ⟶ M)
    (sP : (b.inv)_*ᵃ[l].obj P ⟶ P) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l j M).hom.app P) ≫
        (adicLowerStarTensorLeftIso l a.inv ((j)^*ᵃ[l].obj M)).hom.app ((j)^*ᵃ[l].obj P) ≫
        (Mod.tensorLeftMap ((adicUpperStarExchange l j a b c).hom.app M ≫
          (j)^*ᵃ[l].map sM)).app _ ≫
        (Mod.tensorLeft _).map ((adicUpperStarExchange l j a b c).hom.app P ≫
          (j)^*ᵃ[l].map sP) =
      (adicUpperStarExchange l j a b c).hom.app ((Mod.tensorLeft M).obj P : AdicSheaf l T₂) ≫
        (j)^*ᵃ[l].map ((adicLowerStarTensorLeftIso l b.inv M).hom.app P ≫
          (Mod.tensorLeftMap sM).app _ ≫ (Mod.tensorLeft M).map sP) ≫
        (adicUpperStarTensorLeftIso l j M).hom.app P := by
  have n₁ := ((Mod.tensorLeftMap ((j)^*ᵃ[l].map sM)).naturality
    ((adicUpperStarExchange l j a b c).hom.app P)).symm
  have n₂ := (adicUpperStarTensorLeftIso l j M).hom.naturality sP
  rw [Mod.tensorLeftMap_comp, NatTrans.comp_app, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% n₁, adicUpperStarTensorLeftIso_exchange_assoc j a b c P M]
  simp only [Functor.comp_map] at n₂
  rw [← adicUpperStar_map_tensorLeftMap_app_tensorLeftIso_hom_assoc j sM, ← n₂]

end AlgebraicGeometry.ProEtale
