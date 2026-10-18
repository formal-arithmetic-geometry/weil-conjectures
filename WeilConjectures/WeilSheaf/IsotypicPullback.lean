/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Isotypic
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# Pullbacks of isotypic components along morphisms of torsors

Let `π₁ : W₁ ⟶ Z₁` and `π : W ⟶ X` be torsors (under `G₁` and `G`) and `(h, s)` a morphism of
torsors: `s ≫ π₁ = π ≫ h`, with `τ_g ≫ s = s ≫ τ₁_{c(g)}` for a map `c : G → G₁`. A morphism
of pro-étale Weil sheaves `ι : N ⟶ π₁_* ℚ̄_ℓ` on which `G₁` acts through a character `χ`, whose
adjoint `π₁^* N ⟶ ℚ̄_ℓ` is an isomorphism, induces a morphism `h^* N ⟶ π_* ℚ̄_ℓ` on which `G` acts
through `χ ∘ c` and whose adjoint `π^* h^* N ⟶ ℚ̄_ℓ` is an isomorphism
(`AlgebraicGeometry.ProEtaleWeilSheaf.isotypicPullback`): the adjoint of
`N ⟶ π₁_* ℚ̄_ℓ ⟶ π₁_* s_* ℚ̄_ℓ ≅ h_* π_* ℚ̄_ℓ`.

Applied to the Artin–Schreier covering of the affine line and the Artin–Schreier coverings of
the plane, this describes the Artin–Schreier sheaves `ℒ_{ψ,f}` of functions as isotypic
components (blueprint `lem-fd-as-characters`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X W Z₁ W₁ : Scheme.{u}} (π : W ⟶ X) (π₁ : W₁ ⟶ Z₁)
  (h : X ⟶ Z₁) (s : W ⟶ W₁) (hs : s ≫ π₁ = π ≫ h) {G G₁ : Type u}
  (τ : G → (W ≅ W)) (hτ : ∀ g, (τ g).hom ≫ π = π)
  (τ₁ : G₁ → (W₁ ≅ W₁)) (hτ₁ : ∀ g, (τ₁ g).hom ≫ π₁ = π₁)

/-- Pulling back functions along a morphism of torsors intertwines the translations. -/
lemma lowerStar_map_adicConstantSheafToLowerStar_comp_torsorTranslation (g : G) (g₁ : G₁)
    (hτs : (τ g).hom ≫ s = s ≫ (τ₁ g₁).hom) :
    (π₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s π₁).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hs).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) π h).inv.app _ ≫
      (h)_*[WeilCoefficients.{u} l].map (torsorTranslation l π τ hτ g).hom =
    (torsorTranslation l π₁ τ₁ hτ₁ g₁).hom ≫
      (π₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s π₁).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hs).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) π h).inv.app _ := by
  ext ⟨U⟩ : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, torsorTranslation_hom_app, adicConstantSheafToLowerStar_hom_app,
    adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  · simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj, Quiver.Hom.unop_op,
      MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
      Category.assoc, MorphismProperty.Over.pullbackComp_hom_app_left, Category.id_comp,
      limit.lift_π, PullbackCone.mk_π_app, MorphismProperty.Over.pullbackCongr,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
    rw [hτs]


/-- Pulling back functions along `s` commutes with pulling back along automorphisms `e_W`,
`e_{W₁}` with `s ≫ e_{W₁} = e_W ≫ s`. -/
lemma adicConstantSheafToLowerStar_lowerStarExchange (eW : W ⟶ W) (eW₁ : W₁ ⟶ W₁)
    (hc : s ≫ eW₁ = eW ≫ s) :
    adicConstantSheafToLowerStar l eW₁ ≫
      (eW₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s eW₁).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) eW s).inv.app _ =
    adicConstantSheafToLowerStar l s ≫
      (s)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l eW) := by
  ext ⟨U⟩ : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, adicConstantSheafToLowerStar_hom_app,
    adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]


variable (l) in
/-- The morphism `ℚ̄_ℓ ⟶ s_* ℚ̄_ℓ` of sheaves of `ℚ̄_ℓ`-modules pulling back functions along
`s`. -/
noncomputable def adicUnitToLowerStar :
    AdicSheaf.unit l W₁ ⟶ (s)_*ᵃ[l].obj (AdicSheaf.unit l W) :=
  Mod.homMk (adicConstantSheafToLowerStar l s) (by
    change MonObj.mul ≫ adicConstantSheafToLowerStar l s = _ ◁ adicConstantSheafToLowerStar l s ≫
      adicConstantSheafToLowerStar l s ▷ _ ≫ MonObj.mul
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

@[simp]
lemma adicUnitToLowerStar_hom :
    (adicUnitToLowerStar l s).hom = adicConstantSheafToLowerStar l s :=
  rfl

instance : IsIso ((adicUpperStarLowerStarAdjunction l s).homEquiv _ _ |>.symm
    (adicUnitToLowerStar l s)) := by
  have : IsIso ((adicUpperStarLowerStarAdjunction l s).homEquiv _ _ |>.symm
      (adicUnitToLowerStar l s)).hom := by
    rw [Adjunction.homEquiv_counit, Mod.comp_hom', adicUpperStar_map_hom,
      adicUpperStarLowerStarAdjunction_counit_app_hom_eq]
    have : IsIso (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) s).homEquiv
        (adicConstantSheaf l W₁) (adicConstantSheaf l W)).symm
          (adicConstantSheafToLowerStar l s)) := inferInstance
    rwa [Adjunction.homEquiv_counit] at this
  have : IsIso ((Mod.forget _).map ((adicUpperStarLowerStarAdjunction l s).homEquiv _ _ |>.symm
      (adicUnitToLowerStar l s))) := this
  exact isIso_of_reflects_iso _ (Mod.forget _)

end AlgebraicGeometry.ProEtale
