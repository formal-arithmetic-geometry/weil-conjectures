/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.Basic

/-!
# Coefficient comparisons and the base change of extension by zero
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **Unfinished (B).**
The base change isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` of the extension by
zero is compatible with the coefficient comparisons. -/
lemma coeffCompatible_derivedOpenImmersionLowerShriekBaseChangeIso {U' U X' X : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g'' : X' ⟶ X} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'') :
    CoeffCompatible
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j'))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
        (leftDerivedUpperStarRestrictScalarsIso ρ g''))
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).hom
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ') hsq).hom :=
  sorry

end AlgebraicGeometry.Etale
