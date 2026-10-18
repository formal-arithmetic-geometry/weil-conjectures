/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.Basic

/-!
# Coefficient comparisons and the derived base change map
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

variable [Finite Λ]

/-- **Unfinished (A).**
The derived base change map `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` is compatible with the
coefficient comparisons of `Rf_*`, `Rf'_*`, `Lg^*` and `Lg'^*`. -/
lemma coeffCompatible_derivedBaseChangeMap {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (d d' : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd' : ∀ (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d' < q →
      IsZero ((((f')_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd)
        (leftDerivedUpperStarRestrictScalarsIso ρ g))
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f' d' hd'))
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq)
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ') sq) :=
  sorry


end AlgebraicGeometry.Etale
