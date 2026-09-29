/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization

/-!

# Derived complete objects with coefficients in an `ℓ`-adic field

Let `E` be an extension of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, with ring of integers
`𝒪_E = PadicAlgCl.integers l E`. This file is meant to pass from derived complete objects of
the derived category of sheaves of `𝒪_E`-modules on the small pro-étale site `X.ProEt` of a
scheme `X` (`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`) to
coefficients in `E`. For now it only records that `E` is the fraction field of the universe
`u + 1` copy `Shrink 𝒪_E` of its ring of integers.

## Main definitions

- `PadicAlgCl.algebraShrink`, `PadicAlgCl.isFractionRing_shrink` : `E` is the fraction field
  of the universe `u + 1` copy `Shrink 𝒪_E` of its ring of integers.

-/

@[expose] public section

universe w u

section RingOfIntegers

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E]

/-- `E` as an algebra over the universe `u + 1` copy `Shrink 𝒪_E` of its ring of integers,
through `Shrink.ringEquiv : Shrink 𝒪_E ≃+* 𝒪_E`. -/
noncomputable instance algebraShrink : Algebra (Shrink.{u + 1} (integers l E)) E :=
  ((algebraMap (integers l E) E).comp (Shrink.ringEquiv (integers l E)).toRingHom).toAlgebra

/-- `E` is the fraction field of the universe `u + 1` copy `Shrink 𝒪_E` of its ring of
integers, as it is of `𝒪_E` itself. -/
instance isFractionRing_shrink : IsFractionRing (Shrink.{u + 1} (integers l E)) E :=
  IsFractionRing.of_ringEquiv_left (Shrink.ringEquiv (integers l E)) fun _ ↦ rfl

end PadicAlgCl

end RingOfIntegers
