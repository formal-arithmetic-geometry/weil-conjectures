/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Coherence of exact closed direct-image exchange on D+

Source: sites-cohomology Tag 0E47, termwise localization of finite exchange.
(blueprint: lem-per-closed-direct-image-plus-coherence).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Etale

/-- Exact closed direct-image exchange respects pasting and identity squares.
The formula defining c is the termwise localization of the ordinary finite exchange;
no support right adjoint occurs in this assertion.

Source: sites-cohomology Tag 0E47; `baseChangeMap_paste_horiz_app` and `baseChangeMap_id`.
(blueprint: lem-per-closed-direct-image-plus-coherence).

Proof: Ordinary exchange is the mate of the inverse-image composition square.
Inverse-image associativity and mate pasting give its horizontal composition law;
the identity law is the mate of the unitor square. Since closed direct images and
all inverse images are exact, apply them degree by degree to bounded below complexes.
Localization preserves the two equalities. Its compositor is precisely
mapDerivedCategoryPlusCompIso, and its image of an ordinary natural isomorphism is
mapDerivedCategoryPlusNatIso. Thus the horizontal inverse-image compositors are
upperStarCompDerivedPlus and upperStarIdDerivedPlus. Invert the exchange maps and
cancel these compositors to obtain the displayed TwoSquare formulas. This does not
use any ind-etale assumption: all closed immersions satisfy finite exchange. -/
theorem closedDirectImagePlus_coherence (A : Type (u + 1)) [CommRing A] :
    let c := fun {Z Z' T T' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T')
      [IsClosedImmersion i] [IsClosedImmersion i']
      (h : Z' ⟶ Z) (g : T' ⟶ T) (sq : IsPullback h i' i g) =>
      have := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
      (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso (asIso (baseChangeMap (ModuleCat.{u + 1} A)
          sq.toCommSq)) ≪≫ Functor.mapDerivedCategoryPlusCompIso _ _
    (∀ {Z Z' Z'' T T' T'' : Scheme.{u}}
      (i : Z ⟶ T) (i' : Z' ⟶ T') (i'' : Z'' ⟶ T'')
      [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion i'']
      (h : Z' ⟶ Z) (g : T' ⟶ T) (h₂ : Z'' ⟶ Z') (g₂ : T'' ⟶ T')
      (sq : IsPullback h i' i g) (sq₂ : IsPullback h₂ i'' i' g₂),
      TwoSquare.mk _ _ _ _ (c i i'' (h₂ ≫ h) (g₂ ≫ g) (sq₂.paste_horiz sq)).inv =
        (((TwoSquare.mk _ _ _ _ (c i i' h g sq).inv ≫ₕ
          TwoSquare.mk _ _ _ _ (c i' i'' h₂ g₂ sq₂).inv).whiskerTop
          (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) h₂ h).hom).whiskerBottom
          (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) g₂ g).inv)) ∧
    (∀ {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i],
      TwoSquare.mk _ _ _ _ (c i i (𝟙 Z) (𝟙 T) (IsPullback.id_horiz i)).inv =
        ((TwoSquare.mk _ _ _ _
          ((Functor.leftUnitor (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus).hom ≫
            (Functor.rightUnitor _).inv)).whiskerTop
            (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) Z).hom).whiskerBottom
            (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) T).inv) := by sorry

end AlgebraicGeometry.Etale
