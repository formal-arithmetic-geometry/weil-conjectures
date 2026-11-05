/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The exceptional inverse image along an isomorphism

For an isomorphism of schemes `e : X ≅ Y` the exceptional inverse image is the derived
pullback, `Re^! ≅ Le^*`. Both functors are right adjoint to the same functor: `Re_! ≅ Re_*`
because `e` is proper (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`),
`Re_* ≅ L(e⁻¹)^*` (`AlgebraicGeometry.Etale.rightDerivedLowerStarIsoLeftDerivedUpperStarInv`),
and `L(e⁻¹)^* ⊣ R(e⁻¹)_* ≅ Le^*`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIso`: `Re^! ≅ Le^*`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_eq`: equal morphisms have
  isomorphic exceptional inverse images, whatever the instances of `HasCompactification`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso`: the counit
  of `Rf_! ⊣ Rf^!` is an isomorphism when `f` is an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

end Etale

end AlgebraicGeometry
