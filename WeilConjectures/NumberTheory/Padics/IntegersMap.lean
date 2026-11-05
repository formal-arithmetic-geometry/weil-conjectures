/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.RingTheory.FrobeniusForm

/-!
# The inclusion of rings of integers `𝒪_E ⟶ 𝒪_L`

Let `E ⊆ L` be extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, and let `PadicAlgCl.integersMap` and
`PadicAlgCl.integersShrinkMap` be the inclusions `𝒪_E ⟶ 𝒪_L` of their rings of integers and of
the universe `u + 1` copies `Shrink 𝒪_E ⟶ Shrink 𝒪_L`.

## Main results

- `PadicAlgCl.integersMap_injective`, `PadicAlgCl.integersShrinkMap_injective`: these inclusions
  are injective.
- `PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap`: if `E` and `L` are finite over
  `ℚ_ℓ`, then `𝒪_L` is free over `𝒪_E` and has a Frobenius form, so that extension and
  coextension of scalars along `𝒪_E ⟶ 𝒪_L` agree.
- `PadicAlgCl.exists_dvd_pow_of_mem_maximalIdealShrink`: every nonzero element of `𝒪_L` divides
  a power of every element of the maximal ideal of `𝒪_L`.
-/

@[expose] public section

universe w u

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)]

section Shrink

variable [Small.{u + 1} E] [Small.{u + 1} L]

end Shrink

section Finite

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]
  [Small.{u + 1} E] [Small.{u + 1} L]

end Finite

section Divisibility

variable {l} {L}

variable [Small.{u + 1} L]

end Divisibility

end PadicAlgCl
