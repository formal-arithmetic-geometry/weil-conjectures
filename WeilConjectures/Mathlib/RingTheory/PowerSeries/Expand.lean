/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Complements on the expansion `T ↦ T ^ p` of power series

## Main results

- `PowerSeries.expand_inv`: over a field, expansion commutes with taking inverses.
- `PowerSeries.X_pow_dvd_expand_sub_C_constantCoeff`: the expansion `f (T ^ p)` is congruent to
  its constant coefficient modulo `T ^ p`.
-/

@[expose] public section

namespace PowerSeries

/-- Over a field, the expansion `T ↦ T ^ p` commutes with taking inverses. -/
theorem expand_inv {K : Type*} [Field K] (p : ℕ) (hp : p ≠ 0) (f : K⟦X⟧) :
    expand p hp f⁻¹ = (expand p hp f)⁻¹ := by
  by_cases hf : constantCoeff f = 0
  · rw [inv_eq_zero.2 hf, map_zero, inv_eq_zero.2 (by rwa [constantCoeff_expand])]
  · rw [eq_inv_iff_mul_eq_one (by rwa [constantCoeff_expand]), ← map_mul,
      PowerSeries.inv_mul_cancel _ hf, map_one]

/-- The expansion `f (T ^ p)` of a power series is congruent to its constant coefficient modulo
`T ^ p`. -/
theorem X_pow_dvd_expand_sub_C_constantCoeff {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f : R⟦X⟧) : X ^ p ∣ expand p hp f - C (constantCoeff f) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_expand, coeff_C]
  rcases eq_or_ne m 0 with rfl | h0
  · simp
  · rw [if_neg fun h ↦ (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h).not_gt hm, if_neg h0,
      sub_zero]

end PowerSeries
