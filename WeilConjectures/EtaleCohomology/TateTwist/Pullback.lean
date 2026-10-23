/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-!
# Inverse images of Tate twists

For a morphism `f : X ⟶ Y` of schemes on which the characteristic `n` of `Λ` is invertible:

* the comparison `f^* μₙ ⟶ μₙ` is an isomorphism
  (`AlgebraicGeometry.Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit`);
* the twist sheaves and the twisting objects pull back to the twist sheaves and the twisting
  objects, `f^* Λ_Y(d) ≅ Λ_X(d)` (`AlgebraicGeometry.Etale.upperStarTateTwistSheafIso`) and
  `Lf^* Λ_Y(d) ≅ Λ_X(d)` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTateTwistObjectIso`);
* hence `Lf^*(K(d)) ≅ (Lf^* K)(d)`, naturally in `K`
  (`AlgebraicGeometry.Etale.leftDerivedUpperStarTateTwistIso`).

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_tateTwist`: blueprint
  `det-prop-sfb-cartesian-coefficients-twists`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ Y]

/-- The derived pullback commutes with the Tate twist: `Lf^*(K(d)) ≅ (Lf^* K)(d)`, naturally in
`K`, through the monoidal structure of `Lf^*` and the identification `Lf^* Λ_Y(d) ≅ Λ_X(d)` of
the twist datum. -/
noncomputable def leftDerivedUpperStarTateTwistIso [HasTateTwist Λ] (f : X ⟶ Y) (d : ℤ) :
    tateTwist Λ Y d ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ tateTwist Λ X d :=
  derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f (tateObject Λ Y d) ≪≫
    Functor.isoWhiskerLeft _
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso (leftDerivedUpperStarTateObjectIso f d))

variable [NeZero (ringChar Λ)]

/-- The pullback of the twist sheaf `Λ_Y(d) = (μₙ ⊗ Λ)^{⊗ d}` is the twist sheaf `Λ_X(d)`: both
are pulled back from `Spec ℤ[1/n]`. -/
noncomputable def upperStarTateTwistSheafIso (f : X ⟶ Y) (d : ℤ) :
    (f)^*[ModuleCat.{u + 1} Λ].obj (tateTwistSheaf Λ Y d) ≅ tateTwistSheaf Λ X d :=
  ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f (toInvertibleExponentBase (Λ := Λ) Y)
    (toInvertibleExponentBase (Λ := Λ) X) (comp_toInvertibleExponentBase f).symm).app _).symm

/-- Blueprint `det-prop-sfb-cartesian-coefficients-twists`: Inverse image of Tate twists

For a morphism `f : X ⟶ Y` of schemes on which the characteristic `n` of `Λ` is invertible:

1. the comparison `f^* μₙ ⟶ μₙ` is an isomorphism;
2. `f^* Λ_Y(d) ≅ Λ_X(d)` for the twist sheaves and `Lf^* Λ_Y(d) ≅ Λ_X(d)` for the twisting
   objects (`AlgebraicGeometry.Etale.upperStarTateTwistSheafIso`,
   `AlgebraicGeometry.Etale.leftDerivedUpperStarTateTwistObjectIso`; the latter are compatible
   with composition and with the products of twists,
   `AlgebraicGeometry.Etale.leftDerivedUpperStarTateTwistObjectIso_comp` and
   `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_tateTwistObjectAddIso`);
3. consequently `Lf^*(K(d)) ≅ (Lf^* K)(d)`, naturally in `K`
   (`AlgebraicGeometry.Etale.leftDerivedUpperStarTateTwistIso`).

This is the case of a finite coefficient ring `Λ`; the étale twists of the integral and rational
coefficient rings are not constructed in the repository. -/
theorem leftDerivedUpperStar_tateTwist (f : X ⟶ Y) :
    IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f) ∧
    (∀ d : ℤ, Nonempty ((f)^*[ModuleCat.{u + 1} Λ].obj (tateTwistSheaf Λ Y d) ≅
      tateTwistSheaf Λ X d)) ∧
    (∀ d : ℤ, Nonempty ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateTwistObject Λ Y d) ≅
      tateTwistObject Λ X d)) ∧
    ∀ d : ℤ, Nonempty (tateTwist Λ Y d ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ tateTwist Λ X d) :=
  ⟨isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit _ f
      (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) Y),
    fun d ↦ ⟨upperStarTateTwistSheafIso Λ f d⟩,
    fun d ↦ ⟨leftDerivedUpperStarTateTwistObjectIso Λ f d⟩,
    fun d ↦ ⟨leftDerivedUpperStarTateTwistIso Λ f d⟩⟩

end Etale

end AlgebraicGeometry
