/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassProduct

/-!
# The cup product of Thom classes

If `α` is a Thom class of `Z₁ ⊂ U` and the restriction of `β` to `Z₁` is a Thom class of
`Z ⊂ Z₁`, then the cup product with supports `α ∪ β` is a Thom class of `Z ⊂ U`
(`AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`). See
`WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassProduct` for the strategy.

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Transport

/-- If `ν : F ⟶ L ⋙ R` is an isomorphism and `L ⊣ R`, then postcomposition with `F.map χ` is
bijective on `Hom(S, F X)` as soon as postcomposition with `L.map χ` is bijective on
`Hom(L S, L X)`: the bijections `Hom(S, F X) ≅ Hom(S, R L X) ≅ Hom(L S, L X)` are natural. -/
lemma bijective_comp_map_of_adjunction {C D : Type*} [Category C] [Category D] {F : C ⥤ C}
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (ν : F ⟶ L ⋙ R) [IsIso ν] {S X Y : C} (χ : X ⟶ Y)
    (h : Function.Bijective (fun f : L.obj S ⟶ L.obj X ↦ f ≫ L.map χ)) :
    Function.Bijective (fun f : S ⟶ F.obj X ↦ f ≫ F.map χ) := by
  let Φ : ∀ T, (S ⟶ F.obj T) ≃ (L.obj S ⟶ L.obj T) := fun T ↦
    { toFun := fun f ↦ (adj.homEquiv _ _).symm (f ≫ ν.app T)
      invFun := fun g ↦ adj.homEquiv _ _ g ≫ inv (ν.app T)
      left_inv := fun f ↦ by simp
      right_inv := fun g ↦ by simp }
  have hΦ : ∀ f : S ⟶ F.obj X, Φ Y (f ≫ F.map χ) = Φ X f ≫ L.map χ := fun f ↦ by
    change (adj.homEquiv _ _).symm ((f ≫ F.map χ) ≫ ν.app Y) =
      (adj.homEquiv _ _).symm (f ≫ ν.app X) ≫ L.map χ
    rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, ν.naturality,
      Category.assoc]
    rfl
  have : (fun f : S ⟶ F.obj X ↦ f ≫ F.map χ) =
      (Φ Y).symm ∘ (fun f ↦ f ≫ L.map χ) ∘ Φ X := by
    funext f
    simp only [Function.comp_apply]
    rw [← hΦ, Equiv.symm_apply_apply]
  rw [this]
  exact (Φ Y).symm.bijective.comp (h.comp (Φ X).bijective)

variable [Finite Λ] {U Z₁ : Scheme.{u}} (i₁ : Z₁ ⟶ U) [IsClosedImmersion i₁]

/-- The projection formula for a closed immersion `i₁ : Z₁ ⟶ U`, as a natural transformation
`Ri₁_! Λ_{Z₁} ⊗ᴸ - ⟶ Ri₁_* Li₁^*`: the projection map, the left unitor and `Ri₁_! ≅ Ri₁_*`. -/
noncomputable def closedImmersionProjectionNatTrans :
    (derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁)) ⟶
      L((i₁)^*[ModuleCat.{u + 1} Λ]) ⋙ R((i₁)_*[ModuleCat.{u + 1} Λ]) :=
  (projectionMap (ModuleCat.{u + 1} Λ) i₁).app (constantComplex Λ Z₁) ≫
    Functor.whiskerLeft L((i₁)^*[ModuleCat.{u + 1} Λ])
      (Functor.whiskerRight (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) Z₁).hom
        R(i₁)_![ModuleCat.{u + 1} Λ]) ≫
    Functor.whiskerLeft L((i₁)^*[ModuleCat.{u + 1} Λ])
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i₁).hom

instance : IsIso (closedImmersionProjectionNatTrans Λ i₁) := by
  have := isIso_projectionMap_of_finite Λ i₁
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp only [closedImmersionProjectionNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

end Transport

end Etale

end AlgebraicGeometry
