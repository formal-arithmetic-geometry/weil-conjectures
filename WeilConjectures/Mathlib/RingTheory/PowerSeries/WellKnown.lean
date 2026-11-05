/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Power series supported on the multiples of an integer

The inverse of `1 - X ^ e` is the series `∑ₖ X ^ (e k)`, supported on the multiples of `e`. The
power series whose coefficients vanish outside the multiples of `f` form a submonoid
(`PowerSeries.dvdSupportSubmonoid`), and its elements are invariant under the rescaling
`X ↦ ζ X` by an `f`-th root of unity `ζ`.

## Main statements

- `PowerSeries.inv_one_sub_X_pow_eq_mk`: `(1 - X ^ e)⁻¹ = ∑ₖ X ^ (e k)`.
- `PowerSeries.rescale_eq_self_of_mem_dvdSupportSubmonoid`: a power series supported on the
  multiples of `f` is invariant under `X ↦ ζ X` for `ζ ^ f = 1`.
- `Polynomial.coe_comp_C_mul_X`: the substitution `X ↦ ζ X` in a polynomial is the rescaling of
  the power series.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [Field R]

/-- The geometric series `∑ₖ X ^ (e k)` is the inverse of `1 - X ^ e`. -/
theorem inv_one_sub_X_pow_eq_mk {e : ℕ} (he : e ≠ 0) :
    ((1 : R⟦X⟧) - X ^ e)⁻¹ = mk fun n ↦ if e ∣ n then 1 else 0 := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · ext n
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [he]
    rw [if_neg hn.ne']
    by_cases hen : e ≤ n
    · rw [if_pos hen, coeff_mk, sub_eq_zero]
      exact if_congr (Nat.dvd_sub_iff_left hen dvd_rfl).symm rfl rfl
    · rw [if_neg hen, if_neg fun h ↦ hen (Nat.le_of_dvd hn h), sub_zero]
  · simp [he]

end PowerSeries

