/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMono.Basic

/-!
# Split restricted base change maps: from `E` to `ℚ̄_ℓ`

Flat extension of scalars along `E ⟶ ℚ̄_ℓ` carries split restricted base change maps to split
restricted base change maps
(`ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`).
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
