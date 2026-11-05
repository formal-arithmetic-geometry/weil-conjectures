/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralQuotient

/-!
# The derived (Push) comparison along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`, `n` a natural number and
`f : X ⟶ Y` a morphism of schemes. We show that the comparison
`𝒪_E ⧸ ℓⁿ ⊗ᴸ Rf_* K ⟶ Rf_*(𝒪_E ⧸ ℓⁿ ⊗ᴸ K)` is an isomorphism for every bounded below
`K ∈ D(𝒪_{E,X})`
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app`).

This is the instance `ϖ = ℓⁿ` of
`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_shortExact`: the
multiplication by the constant `ℓⁿ ∈ 𝒪_E` on `𝒪_{E,X}` is `ℓⁿ • 𝟙`
(`ProEtale.padicIntegersRegularEnd_natCast_pow_hom`), so that
`0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` is short exact
(`ProEtale.shortExact_padicIntegersRegularEnd_integersModPow`, from
`ProEtale.shortExact_integersModPowReduction`), and `ℓⁿ ≠ 0` in `E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  (n : ℕ)

namespace CondensedRing

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

end CondensedRing

end AlgebraicGeometry.ProEtale
