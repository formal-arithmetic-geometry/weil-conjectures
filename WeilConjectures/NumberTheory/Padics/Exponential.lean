/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.Logarithm

/-!
# The logarithm and the exponential on deep principal units

Let `E / ℚ_ℓ` be a finite extension inside `ℚ̄_ℓ = PadicAlgCl l`, with the norm restricted from
`ℚ̄_ℓ`, and let `K = ℓ ^ (1 / (ℓ - 1))` (`PadicAlgCl.logExpConst`). On the ball
`K ‖x‖ < 1`, i.e. `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`, the logarithm series
`log (1 + x) = ∑ (-1)^(n+1) x ^ n / n` (`PadicAlgCl.smallLog`) and the exponential series
`exp x = ∑ x ^ n / n!` (`PadicAlgCl.smallExp`) converge, are isometries, and are mutually
inverse group isomorphisms between the principal units `1 + x` and the additive group of the
ball (blueprint `lem-wf-deep-principal-unit-log`). For a uniformizer `ϖ` and `r > e / (ℓ - 1)`
the ideal `𝔪_E ^ r` is a closed sub-ball of this ball.

The inverse identities are proved without composing power series: `f x = log (exp x)` is
additive with `‖f x - x‖ ≤ K ‖x‖ ^ 2`, and evaluating at `ℓⁿ x` forces `f x = x`.

## Main statements

- `PadicAlgCl.smallLog_add_add_mul`, `PadicAlgCl.smallExp_add`: the homomorphism properties.
- `PadicAlgCl.smallLog_smallExp_sub_one`, `PadicAlgCl.smallExp_smallLog`: the inverse identities.
- `PadicAlgCl.norm_smallLog_sub_smallLog`, `PadicAlgCl.norm_smallExp_sub_smallExp`: isometry.
- `PadicAlgCl.smallLog_smallExp_deep`: summary on a closed ball of radius `ρ < ℓ ^ (-1 / (ℓ - 1))`.
- `PadicAlgCl.exists_pow_norm_sub_one_le`: some power `u ^ N` of every unit of `𝒪_E` is a deep
  principal unit.
-/

@[expose] public section

universe w

open Filter Topology
open scoped Nat NNReal

namespace PadicAlgCl

section Constant

variable (l : ℕ) [Fact l.Prime]

/-- The constant `ℓ ^ (1 / (ℓ - 1))`. The logarithm and the exponential series converge on the
open ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`, of radius the inverse of this constant, since
`v_ℓ(n!) ≤ (n - 1) / (ℓ - 1)`. -/
noncomputable def logExpConst : ℝ := (l : ℝ) ^ (((l - 1 : ℕ) : ℝ)⁻¹)

variable {l}


end Constant

section Estimates

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]


end Estimates

section Series

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- Blueprint `lem-wf-deep-principal-unit-log`: The logarithm on sufficiently deep principal
units.

`smallExp l E x` is the sum of the exponential series `exp x = ∑_{n ≥ 0} x ^ n / n!`, formed in
the topology restricted from `ℚ̄_ℓ`. It converges for `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`
(`PadicAlgCl.summable_expSeries`). -/
noncomputable def smallExp (x : E) : E :=
  letI := normedFieldOfAlgebra l E
  ∑' n : ℕ, x ^ n / (n ! : E)

variable {l E}


variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]


end Series
section Inverse

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]


end Inverse

section Units

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- An element of the maximal ideal of `𝒪_E` has norm `< 1`. -/
theorem norm_lt_one_of_mem_maximalIdeal {x : integers l E}
    (hx : x ∈ IsLocalRing.maximalIdeal (integers l E)) :
    ‖algebraMap E (PadicAlgCl l) (x : E)‖ < 1 := by
  have hle : ‖algebraMap E (PadicAlgCl l) (x : E)‖ ≤ 1 := by
    exact_mod_cast (mem_integers_iff l E _).1 x.2
  refine lt_of_le_of_ne hle fun h ↦ ?_
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, norm_zero] at h
    exact zero_ne_one h
  have hinv : (x : E)⁻¹ ∈ integers l E := by
    rw [mem_integers_iff, map_inv₀, nnnorm_inv, ← NNReal.coe_le_coe, NNReal.coe_inv, coe_nnnorm,
      h, inv_one, NNReal.coe_one]
  refine (IsLocalRing.mem_maximalIdeal x).1 hx ⟨⟨x, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)


end Units
section Characters

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]


end Characters

end PadicAlgCl
