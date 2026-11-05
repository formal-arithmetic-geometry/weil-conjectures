/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.RetractionLift

/-!
# Split restricted base change maps from unique torsion retractions

For a commutative square `sq : g' ≫ p' = p ≫ g` of quasi-compact quasi-separated schemes,
`i : Z ⟶ Y'` and a derived complete `𝒪_E`-complex `K₀`, the restricted base change map
`Li^* BC_sq(K₀)` with `𝒪_E`-coefficients is a split monomorphism if it has unique torsion
retractions (`ProEtale.CondensedRing.HasUniqueTorsionRetractions`): its reductions modulo `ℓⁿ⁺¹`
have unique retractions with a property preserved by reduction. This follows from
`ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`: the source
`Li^* Lg^* Rp_* K₀` is derived complete.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end AlgebraicGeometry.ProEtale.CondensedRing
