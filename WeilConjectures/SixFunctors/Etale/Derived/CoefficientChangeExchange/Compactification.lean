/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.Basic

/-!
# Coefficient comparisons and the comparison of compactifications
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

variable [Finite Λ] [Finite Λ'] {X Y : Scheme.{u}} {f : X ⟶ Y} [CompactSpace Y]

/-- **Unfinished (C).**
The comparison of derived lower shrieks along a refinement of compactifications is
compatible with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison
    {c d : Compactification f} (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    CoeffCompatible (compactificationRestrictScalarsIso ρ d)
      (compactificationRestrictScalarsIso ρ c)
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ) r hcart)
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ') r hcart) :=
  sorry

end AlgebraicGeometry.Etale
