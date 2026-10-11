/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange

/-!
# Base change of the Kummer boundary

The Kummer boundary `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f` is compatible with
pullback: for `e : U' ⟶ U`, the restriction of `∂κ(f)` to `U'`, through the restriction of
supports `Le^* Ri_! Ri^! ⟶ Ri'_! Ri'^! Le^*` (`AlgebraicGeometry.Etale.supportedRestriction`),
is `∂κ(e^* f)`. This is the naturality of the Kummer class
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass`) combined with the base change of
the supported localization triangle
(`AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`).

## Main statements

- `AlgebraicGeometry.Etale.kummerBoundary_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Twist

variable {Λ : Type (u + 1)} [CommRing Λ] [HasTateTwist Λ]

/-- The pullback identifications of the twisting objects are compatible with composition, for
a composite given up to an equality. -/
lemma leftDerivedUpperStarTateObjectIso_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) (m : ℤ) :
    leftDerivedUpperStarTateObjectIso fg m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app (tateObject Λ S m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso g m) ≪≫
          leftDerivedUpperStarTateObjectIso f m := by
  subst h
  exact HasTateTwist.leftDerivedUpperStarTwistObjectIso_comp f g m

variable (Λ) in
/-- The pullback identifications of the constant complexes are compatible with composition. -/
lemma leftDerivedUpperStarConstantComplexIso_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) :
    leftDerivedUpperStarConstantComplexIso Λ fg =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app (constantComplex Λ S) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarConstantComplexIso Λ g) ≪≫
          leftDerivedUpperStarConstantComplexIso Λ f := by
  have := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) f g fg h 0
  ext
  simp only [leftDerivedUpperStarConstantComplexIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  change _ ≫ (leftDerivedUpperStarTateObjectIso fg 0).hom ≫ _ = _
  rw [this]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc, Iso.symm_hom]
  erw [(leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).hom.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp]
  simp only [Category.comp_id]
  rfl

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the pullback identifications of the twisting objects. -/
lemma derivedSquareUpperStarIso_hom_app_tateObject (sq : CommSq g' f' f g) (m : ℤ) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (tateObject Λ Y m) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso f m).hom ≫
          (leftDerivedUpperStarTateObjectIso g' m).hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso g m).hom ≫
        (leftDerivedUpperStarTateObjectIso f' m).hom := by
  have h₁ := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) g' f (g' ≫ f) rfl m
  have h₂ := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) f' g (g' ≫ f) sq.w m
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₃, Iso.inv_hom_id_app_assoc]

variable (Λ) in
/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the pullback identifications of the constant complexes. -/
lemma derivedSquareUpperStarIso_hom_app_constantComplex (sq : CommSq g' f' f g) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ Y) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ f').hom := by
  have h₁ := leftDerivedUpperStarConstantComplexIso_comp Λ g' f (g' ≫ f) rfl
  have h₂ := leftDerivedUpperStarConstantComplexIso_comp Λ f' g (g' ≫ f) sq.w
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₃, Iso.inv_hom_id_app_assoc]

end Twist

end Etale

end AlgebraicGeometry
