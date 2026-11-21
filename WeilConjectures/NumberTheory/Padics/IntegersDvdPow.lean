/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersSubalgebra

/-!
# Nonzero integers of a subfield of `ℚ̄_ℓ` divide a power of `ℓ`

For a subfield `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E = {x ∈ E | ‖x‖ ≤ 1}`, every nonzero
`r ∈ 𝒪_E` divides a power of `ℓ` in `𝒪_E` (`PadicAlgCl.exists_mul_eq_pow_of_ne_zero`), since
`‖ℓ‖ = ℓ⁻¹ < 1`.
-/

@[expose] public section

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}

/-- Every nonzero element `r` of the ring of integers `𝒪_E` of a subfield `E ⊆ ℚ̄_ℓ` divides a
power of `ℓ`: `r * s = ℓ ^ N` for some `s ∈ 𝒪_E` and `N : ℕ`. -/
theorem exists_mul_eq_pow_of_ne_zero {r : integers l E} (hr : r ≠ 0) :
    ∃ (s : integers l E) (N : ℕ), r * s = (l : integers l E) ^ N := by
  have hr' : ((r : E) : PadicAlgCl l) ≠ 0 := by
    intro h
    exact hr (Subtype.ext (Subtype.ext (by simpa using h)))
  have hpos : 0 < ‖((r : E) : PadicAlgCl l)‖ := norm_pos_iff.2 hr'
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hs : (l : E) ^ N / (r : E) ∈ integers l E := by
    rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    change ‖(((l : E) ^ N / (r : E) : E) : PadicAlgCl l)‖ ≤ 1
    have hl : (((l : E)) : PadicAlgCl l) = (l : PadicAlgCl l) := by simp
    rw [IntermediateField.coe_div, IntermediateField.coe_pow, hl, norm_div, norm_pow,
      norm_natCast_self_padicAlgCl, div_le_one hpos]
    exact hN.le
  refine ⟨⟨_, hs⟩, N, Subtype.ext ?_⟩
  change (r : E) * ((l : E) ^ N / (r : E)) = ((l : integers l E) ^ N : E)
  rw [mul_div_cancel₀ _ (fun h ↦ hr' (by simp [h]))]
  simp

end PadicAlgCl
