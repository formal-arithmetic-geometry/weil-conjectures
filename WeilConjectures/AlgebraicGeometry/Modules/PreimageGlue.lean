/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Gluing data for modules along preimages of an open cover

Let `U a` be a family of opens of a scheme `S` and `g : Z ⟶ S` a morphism. We consider gluing
data for sheaves of modules on `Z` relative to the opens `g⁻¹ U a`, with the intersections
`g⁻¹ (U a ⊓ U b)` and `g⁻¹ (U a ⊓ U b ⊓ U c)` as chosen (wide) pullbacks
(`AlgebraicGeometry.Scheme.Modules.PreGlueData`), *without* the cocycle conditions. Such data can
be pulled back along any `h : Z' ⟶ Z` (`AlgebraicGeometry.Scheme.Modules.PreGlueData.pull`), and
the cocycle conditions for the pulled back data are the pullbacks along the restrictions of `h`
of the cocycle conditions for the original data.

This is used to glue modules descended to a finite stage of a cofiltered limit of schemes: the
cocycle conditions only hold after passing to a later stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by the comparison isomorphisms `mapComp'`. -/
lemma pullHom_mapComp'_conj ⦃X₁ X₂ X₁' X₂' : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ (r₁ : X₁' ⟶ X₁) (r₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (p₁ : Y ⟶ X₁')
    (p₂ : Y ⟶ X₂') (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : p₁ ≫ r₁ = x₁) (hx₂ : p₂ ≫ r₂ = x₂)
    (ψ : (F.map x₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map x₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (l : Y' ⟶ Y) (f₁ : Y' ⟶ X₁') (f₂ : Y' ⟶ X₂') (hl₁ : l ≫ p₁ = f₁)
    (hl₂ : l ≫ p₂ = f₂) :
    pullHom ((F.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc (by subst hx₁; rfl)).inv.toNatTrans.app
        M₁ ≫ ψ ≫
        (F.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc (by subst hx₂; rfl)).hom.toNatTrans.app
          M₂) l f₁ f₂ hl₁ hl₂ =
      (F.mapComp' r₁.op.toLoc f₁.op.toLoc (f₁ ≫ r₁).op.toLoc rfl).inv.toNatTrans.app M₁ ≫
        pullHom ψ l (f₁ ≫ r₁) (f₂ ≫ r₂) (by rw [← hx₁, ← hl₁, Category.assoc])
          (by rw [← hx₂, ← hl₂, Category.assoc]) ≫
        (F.mapComp' r₂.op.toLoc f₂.op.toLoc (f₂ ≫ r₂).op.toLoc rfl).hom.toNatTrans.app M₂ := by
  subst hx₁ hx₂ hl₁ hl₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl rfl (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ rfl rfl (by cat_disch)]
  simp

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {Z : Scheme.{u}} (g : Z ⟶ S)

/-- The intersection `g⁻¹ (U a ⊓ U b)` as a chosen pullback of the open immersions of `g⁻¹ U a`
and `g⁻¹ U b`. -/
@[simps]
noncomputable def preimageChosenPullback (a b : ι) :
    ChosenPullback (g ⁻¹ᵁ U a).ι (g ⁻¹ᵁ U b).ι where
  pullback := g ⁻¹ᵁ (U a ⊓ U b)
  p₁ := Z.homOfLE (g.preimage_mono inf_le_left)
  p₂ := Z.homOfLE (g.preimage_mono inf_le_right)
  condition := by simp
  isLimit := (IsOpenImmersion.isPullback (Z.homOfLE (g.preimage_mono inf_le_left))
    (Z.homOfLE (g.preimage_mono inf_le_right)) (g ⁻¹ᵁ U a).ι (g ⁻¹ᵁ U b).ι (by simp)
    (by ext x; simp)).isLimit
  p := (g ⁻¹ᵁ (U a ⊓ U b)).ι
  hp₁ := by simp

/-- The triple intersection `g⁻¹ (U a ⊓ U b ⊓ U c)` as a chosen wide pullback. -/
@[simps]
noncomputable def preimageChosenPullback₃ (a b c : ι) :
    ChosenPullback₃ (preimageChosenPullback U g a b) (preimageChosenPullback U g b c)
      (preimageChosenPullback U g a c) where
  chosenPullback :=
    { pullback := g ⁻¹ᵁ (U a ⊓ U b ⊓ U c)
      p₁ := Z.homOfLE (g.preimage_mono inf_le_left)
      p₂ := Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      condition := by simp
      isLimit := by
        refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).isLimit
        · simp
        · ext x
          simp
          sorry
      p := Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_right))
      hp₁ := by simp }
  p := (g ⁻¹ᵁ (U a ⊓ U b ⊓ U c)).ι
  p₁ := Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_left))
  p₃ := Z.homOfLE (g.preimage_mono inf_le_right)
  l :=
    { f := Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) }
  hp₁ := by simp
  hp₃ := by simp

end AlgebraicGeometry.Scheme.Modules
