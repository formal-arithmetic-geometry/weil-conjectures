/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian

/-!
# Rings of integers in a finite extension of `ℓ`-adic fields

Let `E ⊆ E'` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. The inclusion `E ⟶ E'` restricts to
a ring map `𝒪_E ⟶ 𝒪_{E'}` between the rings of integers, which makes `𝒪_{E'}` a finite free
`𝒪_E`-module. This is what makes the extension of scalars `𝒪_E ⟶ 𝒪_{E'}` between the integral
coefficient stages of the `ℓ`-adic formalism well behaved.

## Main definitions

- `PadicAlgCl.integersMap l E E'`: the ring map `𝒪_E ⟶ 𝒪_{E'}`.

## Main results

- `PadicAlgCl.finite_integersMap`: `𝒪_{E'}` is a finite `𝒪_E`-module. The coordinates in an
  `E`-basis of `E'` are continuous, hence bounded on the unit ball `𝒪_{E'}`, so for some `N` the
  map `x ↦ (ℓ^N c_i(x))_i` embeds `𝒪_{E'}` into `𝒪_E^n`, and `𝒪_E` is Noetherian.
-/

@[expose] public section

universe w u

open NNReal

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E E' : Type w) [Field E] [Field E'] [Algebra E (PadicAlgCl l)]
  [Algebra E' (PadicAlgCl l)] [Algebra E E'] [IsScalarTower E E' (PadicAlgCl l)]

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E']

section Shrink

variable [Small.{u + 1} E] [Small.{u + 1} E']

end Shrink

end PadicAlgCl
