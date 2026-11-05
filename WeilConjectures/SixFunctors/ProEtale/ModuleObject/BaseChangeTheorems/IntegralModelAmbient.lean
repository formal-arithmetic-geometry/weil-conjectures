/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted

/-!
# Integral models in the ambient derived category

On a noetherian scheme `X`, every bounded constructible `ℚ̄_ℓ`-complex `K` is
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for a finite subextension `E` and a bounded constructible
`𝒪_E`-complex `K₀` (`ProEtale.exists_padicAlgCl_iso_integralModel`). This file restates this in the
ambient derived categories, with the properties of `K₀` used to lift split monomorphisms: `K₀` is
derived complete and bounded below
(`ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
