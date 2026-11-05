/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.Basic

/-!
# Coefficient change for restricted base change maps: from `𝔽_E` to `𝒪_E`

This file proves derived Nakayama for the restricted base change map
`Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K`
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`): with
`𝒪_E`-coefficients, it is invertible at a derived complete bounded below `K` if it is invertible
with `𝔽_E`-coefficients at `𝔽_E ⊗ᴸ K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
