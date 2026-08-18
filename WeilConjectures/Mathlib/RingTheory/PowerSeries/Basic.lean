/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The submonoid of power series with constant coefficient one

Power series with constant coefficient `1` are closed under multiplication; this file
bundles them as `PowerSeries.oneSubmonoid`, the target of the exponential bijection built
in `WeilConjectures.Mathlib.RingTheory.PowerSeries.Log`.  It also records the alternating
geometric series as the inverse of `1 + X`.

## Main definitions

- `PowerSeries.oneSubmonoid`, the submonoid of power series with constant coefficient `1`

## Main results

- `PowerSeries.mem_oneSubmonoid`
- `PowerSeries.mk_neg_one_pow_mul_one_add_X`
-/

@[expose] public section

namespace PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

variable (R) in
/-- The submonoid of power series with constant coefficient `1`.
(blueprint: `def:weil-one-submonoid`) -/
def oneSubmonoid : Submonoid R⟦X⟧ :=
  MonoidHom.mker (constantCoeff (R := R))

/-- Membership in `PowerSeries.oneSubmonoid` is the condition `constantCoeff f = 1`.
(blueprint: `lemma:weil-mem-one-submonoid`) -/
@[simp]
theorem mem_oneSubmonoid {f : R⟦X⟧} : f ∈ oneSubmonoid R ↔ constantCoeff f = 1 :=
  MonoidHom.mem_mker

variable (R) in
/-- The alternating geometric series is inverse to `1 + X`.
(blueprint: `lemma:weil-mk-neg-one-pow-mul-one-add-X`) -/
theorem mk_neg_one_pow_mul_one_add_X :
    (mk fun n ↦ (-1 : R) ^ n) * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, coeff_one]
  cases n with
  | zero => rw [coeff_zero_mul_X, add_zero, coeff_mk, pow_zero, if_pos rfl]
  | succ k =>
    rw [coeff_succ_mul_X, coeff_mk, coeff_mk, if_neg (Nat.succ_ne_zero k), pow_succ]
    ring

end

end PowerSeries

end
