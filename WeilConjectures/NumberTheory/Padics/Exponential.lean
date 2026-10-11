/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.Logarithm

/-!
# The logarithm and the exponential on deep principal units

test
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

theorem logExpConst_pos : 0 < logExpConst l :=
  Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _

theorem logExpConst_pow : logExpConst l ^ (l - 1) = l :=
  Real.rpow_inv_natCast_pow (Nat.cast_nonneg l)
    (by have := (Fact.out : l.Prime).two_le; omega)

theorem one_le_logExpConst : 1 ≤ logExpConst l :=
  Real.one_le_rpow (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) (by positivity)

/-- Legendre's bound `(ℓ - 1) v_ℓ((n + 1)!) ≤ n`, in the form `ℓ ^ v_ℓ((n + 1)!) ≤ K ^ n` for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem pow_padicValNat_factorial_le (n : ℕ) :
    (l : ℝ) ^ padicValNat l (n + 1)! ≤ logExpConst l ^ n := by
  have hl1 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  have hK : (logExpConst l ^ n) ^ (l - 1) = (l : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, logExpConst_pow]
  rw [← pow_le_pow_iff_left₀ (by positivity) (pow_nonneg logExpConst_pos.le n) hl1, hK,
    ← pow_mul]
  refine pow_le_pow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) ?_
  have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l (n := n + 1) (by omega)
  rw [mul_comm] at this
  omega

/-- `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` if and only if `‖x‖ ^ (ℓ - 1) < ‖ℓ‖ = ℓ⁻¹`. -/
theorem mul_logExpConst_lt_one_iff {a : ℝ} (ha : 0 ≤ a) :
    a * logExpConst l < 1 ↔ a ^ (l - 1) < (l : ℝ)⁻¹ := by
  have hl1 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [← pow_lt_one_iff_of_nonneg (mul_nonneg ha logExpConst_pos.le) hl1, mul_pow,
    logExpConst_pow, ← lt_div_iff₀ hl, one_div]

end Constant

section Estimates

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]

/-- The `(n + 1)`-st term of the exponential series has norm at most `‖x‖ (K ‖x‖) ^ n`, for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem norm_expSeries_term_le (x : E) (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖x ^ (n + 1) / ((n + 1)! : E)‖ ≤ ‖x‖ * (logExpConst l * ‖x‖) ^ n := by
  let := normedFieldOfAlgebra l E
  rw [norm_div, norm_pow, norm_natCast_eq_pow_padicValNat (Nat.factorial_ne_zero _), inv_pow,
    div_inv_eq_mul, pow_succ', mul_pow, mul_assoc, mul_comm (logExpConst l ^ n)]
  gcongr
  exact pow_padicValNat_factorial_le n

/-- The `(n + 1)`-st term `(-1)^n x ^ (n + 1) / (n + 1)` of the logarithm series has norm at
most `‖x‖ (K ‖x‖) ^ n`, for `K = ℓ ^ (1 / (ℓ - 1))`, since `‖(n + 1)!‖ ≤ ‖n + 1‖`. -/
theorem norm_logSeries_term_le' (x : E) (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖(-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)‖ ≤ ‖x‖ * (logExpConst l * ‖x‖) ^ n := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have : NormOneClass E := ⟨by change ‖algebraMap E (PadicAlgCl l) 1‖ = 1; simp⟩
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  refine le_trans ?_ (norm_expSeries_term_le x n)
  rw [norm_div, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hpos : 0 < ‖((n + 1)! : E)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  refine div_le_div_of_nonneg_left (by positivity) hpos ?_
  rw [Nat.factorial_succ, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one E _)

/-- For `K ‖x‖ ≤ 1` the difference quotient `((1 + x) ^ q - 1) / q` agrees with the `q`-th
partial sum of the logarithm series up to an error of norm at most `‖q‖ ‖x‖`: the coefficient of
`x ^ (j + 1)` in their difference is `(C(q - 1, j) - (-1)^j) / (j + 1)`, and
`j! (C(q - 1, j) - (-1)^j)` is divisible by `q`. -/
theorem norm_pow_sub_one_div_sub_sum_le' {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ ≤ 1) (q : ℕ) :
    letI := normedFieldOfAlgebra l E
    ‖((1 + x) ^ q - 1) / q - ∑ j ∈ Finset.range q, (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)‖ ≤
      ‖(q : E)‖ * ‖x‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  obtain _ | p := q
  · simp
  have hq : ((p + 1 : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr p.succ_ne_zero
  have hsum : ((1 + x) ^ (p + 1) - 1) / (p + 1 : ℕ) =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : E) * x ^ (j + 1) / (j + 1 : ℕ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h := congrArg (fun m : ℕ ↦ (m : E)) (Nat.add_one_mul_choose_eq p j)
    have hj : ((j + 1 : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr j.succ_ne_zero
    push_cast at h hq hj ⊢
    rw [div_eq_div_iff hq hj]
    linear_combination -x ^ (j + 1) * h
  rw [hsum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j hj ↦ ?_
  obtain ⟨w, hw⟩ := Nat.add_one_dvd_factorial_mul_choose_sub_neg_one_pow
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hw' : (j ! : E) * ((p.choose j : E) - (-1) ^ j) = ((p + 1 : ℕ) : E) * (w : E) := by
    exact_mod_cast hw
  have hfac : ((j + 1)! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hterm : ((p.choose j : E) * x ^ (j + 1) / (j + 1 : ℕ) -
      (-1) ^ j * x ^ (j + 1) / (j + 1 : ℕ)) =
      ((p + 1 : ℕ) : E) * (w : E) * (x ^ (j + 1) / ((j + 1)! : E)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, ← hw']
    have hj : (j ! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  rw [hterm, norm_mul, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖(w : E)‖ * ‖x ^ (j + 1) / ((j + 1)! : E)‖
      ≤ 1 * (‖x‖ * (logExpConst l * ‖x‖) ^ j) := by
        gcongr
        · exact IsUltrametricDist.norm_intCast_le_one E w
        · exact norm_expSeries_term_le x j
    _ ≤ ‖x‖ := by
        rw [one_mul]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (mul_nonneg logExpConst_pos.le (norm_nonneg _)) hx)

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

theorem smallLog_zero : smallLog l E 0 = 0 := by
  simp [smallLog]

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- The logarithm series converges on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`. -/
theorem summable_logSeries' {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ) := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one
    (mul_nonneg logExpConst_pos.le (norm_nonneg _)) hx).mul_left ‖x‖)
    (norm_logSeries_term_le' x)

/-- The norms of the terms of the exponential series are summable on the ball
`‖x‖ < ℓ ^ (-1 / (ℓ - 1))`. -/
theorem summable_norm_expSeries {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ ‖x ^ n / (n ! : E)‖ := by
  let := normedFieldOfAlgebra l E
  refine (summable_nat_add_iff 1).mp ?_
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_expSeries_term_le x)
    ((summable_geometric_of_lt_one (mul_nonneg logExpConst_pos.le (norm_nonneg _)) hx).mul_left
      ‖x‖)

/-- Blueprint `lem-wf-deep-principal-unit-log`: The logarithm on sufficiently deep principal
units.

The exponential series converges on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`: its `n`-th term has
norm `‖x‖ ^ n ℓ ^ v_ℓ(n!)` and `v_ℓ(n!) ≤ (n - 1) / (ℓ - 1)`. -/
theorem summable_expSeries {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ x ^ n / (n ! : E) := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  exact (summable_norm_expSeries hx).of_norm

/-- On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` one has `‖log (1 + x) - x‖ ≤ K ‖x‖ ^ 2`, for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem norm_smallLog_sub_le {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallLog l E x - x‖ ≤ logExpConst l * ‖x‖ ^ 2 := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have hsplit := (summable_logSeries' hx).tsum_eq_zero_add
  change smallLog l E x = _ at hsplit
  simp only [pow_zero, zero_add, pow_one, one_mul, Nat.cast_one, div_one] at hsplit
  rw [hsplit, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg logExpConst_pos.le (sq_nonneg _)) fun n ↦
    (norm_logSeries_term_le' x (n + 1)).trans ?_
  calc ‖x‖ * (logExpConst l * ‖x‖) ^ (n + 1) ≤ ‖x‖ * (logExpConst l * ‖x‖) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (mul_nonneg logExpConst_pos.le
          (norm_nonneg _)) hx.le n.succ_ne_zero) (norm_nonneg x)
    _ = logExpConst l * ‖x‖ ^ 2 := by ring

/-- On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` one has `‖exp x - 1 - x‖ ≤ K ‖x‖ ^ 2`, for
`K = ℓ ^ (1 / (ℓ - 1))`. -/
theorem norm_smallExp_sub_le {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallExp l E x - 1 - x‖ ≤ logExpConst l * ‖x‖ ^ 2 := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have := completeSpace_ofAlgebra l E
  have hs := summable_expSeries hx
  have hsplit := hs.tsum_eq_zero_add
  rw [((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add] at hsplit
  change smallExp l E x = _ at hsplit
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one] at hsplit
  rw [hsplit, add_sub_cancel_left, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg logExpConst_pos.le (sq_nonneg _)) fun n ↦
    (norm_expSeries_term_le x (n + 1)).trans ?_
  calc ‖x‖ * (logExpConst l * ‖x‖) ^ (n + 1) ≤ ‖x‖ * (logExpConst l * ‖x‖) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (mul_nonneg logExpConst_pos.le
          (norm_nonneg _)) hx.le n.succ_ne_zero) (norm_nonneg x)
    _ = logExpConst l * ‖x‖ ^ 2 := by ring

/-- An element `x + t` with `‖t‖ ≤ K ‖x‖ ^ 2` and `K ‖x‖ < 1` has the norm of `x`. -/
theorem norm_eq_of_norm_sub_le {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; ‖y - x‖ ≤ logExpConst l * ‖x‖ ^ 2) :
    letI := normedFieldOfAlgebra l E
    ‖y‖ = ‖x‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hy
  have hlt : ‖y - x‖ < ‖x‖ := by
    refine hy.trans_lt ?_
    rw [sq, ← mul_assoc]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hx0) hx
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne'
  rwa [add_sub_cancel, max_eq_left hlt.le] at h

/-- Blueprint `lem-wf-deep-principal-unit-log`: The logarithm on sufficiently deep principal
units.

On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the logarithm preserves the norm:
`‖log (1 + x)‖ = ‖x‖`. -/
theorem norm_smallLog_eq {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallLog l E x‖ = ‖x‖ :=
  norm_eq_of_norm_sub_le hx (norm_smallLog_sub_le hx)

/-- Blueprint `lem-wf-deep-principal-unit-log`: The logarithm on sufficiently deep principal
units.

On the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))` the exponential satisfies `‖exp x - 1‖ = ‖x‖`. -/
theorem norm_smallExp_sub_one_eq {x : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1) :
    letI := normedFieldOfAlgebra l E
    ‖smallExp l E x - 1‖ = ‖x‖ :=
  norm_eq_of_norm_sub_le hx (norm_smallExp_sub_le hx)

/-- Blueprint `lem-wf-deep-principal-unit-log`: The logarithm on sufficiently deep principal
units.

The exponential turns addition into multiplication on the ball `‖x‖ < ℓ ^ (-1 / (ℓ - 1))`:
`exp (x + y) = exp x exp y`, by the Cauchy product formula, the norms of the terms of both
series being summable. -/
theorem smallExp_add {x y : E}
    (hx : letI := normedFieldOfAlgebra l E; logExpConst l * ‖x‖ < 1)
    (hy : letI := normedFieldOfAlgebra l E; logExpConst l * ‖y‖ < 1) :
    smallExp l E (x + y) = smallExp l E x * smallExp l E y := by
  let := normedFieldOfAlgebra l E
  have := completeSpace_ofAlgebra l E
  have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
  change ∑' n : ℕ, (x + y) ^ n / (n ! : E) =
    (∑' n : ℕ, x ^ n / (n ! : E)) * ∑' n : ℕ, y ^ n / (n ! : E)
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (R := E) (summable_norm_expSeries hx)
    (summable_norm_expSeries hy)]
  refine tsum_congr fun n ↦ ?_
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [nsmul_eq_mul, ← hkl, Nat.cast_add_choose E]
  have h1 : (kl.1 ! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (kl.2 ! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((kl.1 + kl.2)! : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

end Series

end PadicAlgCl
