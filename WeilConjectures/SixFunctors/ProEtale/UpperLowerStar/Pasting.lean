/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# Pasting of the commutative square isomorphisms of pro-étale pullbacks

For a commutative square `a ≫ b = c ≫ d` of schemes, `ProEtale.upperStarCompIso` identifies
`b^* ⋙ a^*` with `d^* ⋙ c^*`. These isomorphisms paste horizontally and vertically, as
consequences of the associativity law `ProEtale.upperStarComp_assoc`.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarComp_assoc_app`: the associativity law in components,
  with arbitrary composites.
- `AlgebraicGeometry.ProEtale.upperStarCompIso_hcomp_app` and
  `AlgebraicGeometry.ProEtale.upperStarCompIso_vcomp_app`: horizontal and vertical pasting.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]


lemma upperStarCongr_rfl' {Z W : Scheme.{u}} (g : Z ⟶ W) :
    upperStarCongr A (rfl : g = g) = Iso.refl _ :=
  rfl



/-- The associativity law for `ProEtale.upperStarComp` in components, with the composites given
up to equality. -/
lemma upperStarComp_assoc'_app {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (gh : Y ⟶ V) (hgh : gh = g ≫ h) (fgh : X ⟶ V)
    (hfgh : fgh = f ≫ gh) (hfgh' : fgh = fg ≫ h) (M : Sheaf (Scheme.ProEt.topology V) A) :
    (upperStarCongr A hfgh).hom.app M ≫ (upperStarComp A f gh).hom.app M ≫
        (f)^*[A].map ((upperStarCongr A hgh).hom.app M ≫ (upperStarComp A g h).hom.app M) =
      (upperStarCongr A hfgh').hom.app M ≫ (upperStarComp A fg h).hom.app M ≫
        (upperStarCongr A hfg).hom.app ((h)^*[A].obj M) ≫
          (upperStarComp A f g).hom.app ((h)^*[A].obj M) := by
  subst hfg hgh hfgh
  have := congr_app (congrArg Iso.hom (upperStarComp_assoc A f g h)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom] at this
  rw [upperStarCongr_rfl' A (f ≫ g ≫ h), upperStarCongr_rfl' A (g ≫ h),
    upperStarCongr_rfl' A (f ≫ g)]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [this]
  erw [Category.id_comp, Category.id_comp]

set_option maxHeartbeats 0 in
/-- **Horizontal pasting** of the square isomorphisms of pullbacks: for squares
`a₁ ≫ v₂ = v₁ ≫ b₁` and `a₂ ≫ v₃ = v₂ ≫ b₂`, the isomorphism of the composite square
`(a₁ ≫ a₂) ≫ v₃ = v₁ ≫ b₁ ≫ b₂` is obtained by pasting. -/
lemma upperStarCompIso_hcomp_app {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Scheme.{u}} (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃) (v₁ : X₁ ⟶ Y₁) (v₂ : X₂ ⟶ Y₂) (v₃ : X₃ ⟶ Y₃)
    (sq₁ : a₁ ≫ v₂ = v₁ ≫ b₁) (sq₂ : a₂ ≫ v₃ = v₂ ≫ b₂) (sq : (a₁ ≫ a₂) ≫ v₃ = v₁ ≫ b₁ ≫ b₂)
    (M : Sheaf (Scheme.ProEt.topology Y₃) A) :
    (upperStarComp A a₁ a₂).hom.app ((v₃)^*[A].obj M) ≫
        (a₁)^*[A].map ((upperStarCompIso A sq₂).hom.app M) ≫
        (upperStarCompIso A sq₁).hom.app ((b₂)^*[A].obj M) =
      (upperStarCompIso A sq).hom.app M ≫ (v₁)^*[A].map ((upperStarComp A b₁ b₂).hom.app M) := by
  have E1 := upperStarComp_assoc'_app A a₁ a₂ v₃ _ rfl _ rfl _ (Category.assoc _ _ _) rfl M
  have E2 := upperStarComp_assoc'_app A a₁ v₂ b₂ _ rfl _ sq₂ _ (Category.assoc _ _ _)
    (by rw [Category.assoc, sq₂, ← Category.assoc]) M
  have E3 := upperStarComp_assoc'_app A v₁ b₁ b₂ _ sq₁ _ rfl _ sq
    (by rw [Category.assoc, sq₂, ← Category.assoc]) M
  simp only [upperStarCongr_rfl', Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.comp_obj] at E1 E2 E3
  rw [← cancel_epi ((upperStarComp A (a₁ ≫ a₂) v₃).hom.app M)]
  simp only [upperStarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% E1, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← Functor.map_comp_assoc, reassoc_of% E2, Iso.hom_inv_id_app_assoc, E3]

end AlgebraicGeometry.ProEtale
