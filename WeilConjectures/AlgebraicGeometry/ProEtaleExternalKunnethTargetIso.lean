/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExternalSwap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp

/-! # A constructed direct-image target comparison for external Kunneth

Source: sk-lem-sf-kunneth-star, Two morphisms, direct-image composition
(blueprint: lem-sf-external-kunneth-target-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The target comparison for composing the two identity-factor direct images.
Source: sk-lem-sf-kunneth-star, Two morphisms
(blueprint: lem-sf-external-kunneth-target-iso).

Construction: use product extensionality to identify the composite of the second
identity-factor map, factor interchange, and first identity-factor map with factor
interchange followed by the full product map. Compose the two direct-image
compositors, transport by this equality, undo the final compositor, and apply the
full direct image to the inverse constructed external-product swap isomorphism. -/
def externalKunnethTargetIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ B) (b₂ : Y₂ ⟶ B) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (M₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A)))
    (M₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A))) :
    (lowerStar (ModuleCat.{u + 1} A)
        (pullback.mapOverBaseRight f₁ b₁ b₂)).rightDerivedFunctor.obj
      ((lowerStar (ModuleCat.{u + 1} A)
          (pullbackSymmetry (f₁ ≫ b₁) b₂).inv).rightDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A)
            (pullback.mapOverBaseRight f₂ b₂ (f₁ ≫ b₁))).rightDerivedFunctor.obj
          (externalProduct (ModuleCat.{u + 1} A) (f₂ ≫ b₂) (f₁ ≫ b₁) M₂ M₁))) ≅
      (lowerStar (ModuleCat.{u + 1} A)
          (pullback.mapOverBase f₁ f₂ b₁ b₂)).rightDerivedFunctor.obj
        (externalProduct (ModuleCat.{u + 1} A) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) := by
  let g := pullback.mapOverBaseRight f₂ b₂ (f₁ ≫ b₁)
  let s := (pullbackSymmetry (f₁ ≫ b₁) b₂).inv
  let h := pullback.mapOverBaseRight f₁ b₁ b₂
  let t := (pullbackSymmetry (f₁ ≫ b₁) (f₂ ≫ b₂)).inv
  let v := pullback.mapOverBase f₁ f₂ b₁ b₂
  let N := externalProduct (ModuleCat.{u + 1} A) (f₂ ≫ b₂) (f₁ ≫ b₁) M₂ M₁
  have hw : (g ≫ s) ≫ h = t ≫ v := by
    apply pullback.hom_ext
    · simp [g, s, h, t, v, Category.assoc]
    · simp [g, s, h, t, v, Category.assoc]
  exact ((lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.mapIso
      ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) g s).app N)) ≪≫
    (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A) hw).app N ≪≫
    ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) t v).symm.app N) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor.mapIso
      (externalKunnethSwapIso A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂).symm

end AlgebraicGeometry.ProEtale
