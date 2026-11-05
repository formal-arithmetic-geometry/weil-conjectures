/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice

/-!
# `𝒪_E`-lattices spanned by lattices of `Eⁿ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`
(`PadicAlgCl.integers`). The `𝒪_E`-span of a lattice `L ⊆ Eⁿ` (a compact open subgroup,
`PadicAlgCl.CompactOpenLattice`) is `g 𝒪_Eⁿ` for some `g ∈ GL_n(E)`
(`PadicAlgCl.CompactOpenLattice.exists_glBasis_integers`): it is squeezed between two scalings
of `𝒪_Eⁿ`, hence a free `𝒪_E`-module of rank `n`, `𝒪_E` being a principal ideal domain.

The span is compatible with the action of `GL_n(E)`, so that if `A L = L'` and the spans of `L`,
`L'` are `g 𝒪_Eⁿ`, `g' 𝒪_Eⁿ`, then `g'⁻¹ A g` has integral entries
(`PadicAlgCl.CompactOpenLattice.norm_integersBasisGL_inv_mul_mul_le_one`). This turns a
lattice-valued twisted section of a `GL_n(E)`-valued cocycle into a change of trivialisation
making the cocycle integral.
-/

@[expose] public section

open Matrix

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}

end PadicAlgCl

namespace PadicAlgCl.CompactOpenLattice

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)} {n : ℕ}

variable [FiniteDimensional ℚ_[l] E]

end PadicAlgCl.CompactOpenLattice
