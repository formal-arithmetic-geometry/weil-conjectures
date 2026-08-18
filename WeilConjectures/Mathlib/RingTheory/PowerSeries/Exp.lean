/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The formal exponential of a power series

Mathlib provides the exponential power series `PowerSeries.exp`.  This file adds the
substituted exponential `PowerSeries.expOf f = (exp R).subst f`, the companion of
`PowerSeries.logOf`, and proves that it turns sums of power series with vanishing
constant coefficient into products.

## Main definitions

- `PowerSeries.expOf`

## Main results

- `PowerSeries.constantCoeff_expOf`, `PowerSeries.derivative_expOf`
- `PowerSeries.expOf_add`, `PowerSeries.expOf_zero`
-/

@[expose] public section

namespace PowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `expOf f` is `exp` substituted at `f`, that is `1 + f + f²/2 + f³/6 + ⋯`.  It is
inverse to `PowerSeries.logOf` on the power series with constant coefficient `0`.
(blueprint: `def:weil-formal-exp`) -/
def expOf (f : R⟦X⟧) : R⟦X⟧ :=
  (exp R).subst f

/-- The defining equation of `PowerSeries.expOf`. -/
theorem expOf_eq (f : R⟦X⟧) : expOf f = (exp R).subst f := rfl

/-- The formal exponential of a series with vanishing constant coefficient is normalized.
(blueprint: `lemma:weil-constant-coeff-exp`) -/
@[simp]
theorem constantCoeff_expOf {f : R⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (expOf f) = 1 := by
  have hs : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hmv : MvPowerSeries.constantCoeff (f : R⟦X⟧) = 0 := by rw [← constantCoeff_eq, hf]
  have key : expOf f - 1 = (exp R - 1).subst f := by
    rw [expOf_eq, subst_sub hs, ← coe_substAlgHom hs, map_one]
  have h0 : constantCoeff ((exp R - 1).subst f) = 0 :=
    constantCoeff_subst_eq_zero hmv _ (by rw [map_sub, map_one, constantCoeff_exp, sub_self])
  rw [← sub_eq_zero, ← map_one (constantCoeff (R := R)), ← map_sub, key, h0]

/-- Chain rule for the formal exponential.
(blueprint: `lemma:weil-derivative-exp`) -/
theorem derivative_expOf {f : R⟦X⟧} (hf : constantCoeff f = 0) :
    d⁄dX R (expOf f) = d⁄dX R f * expOf f := by
  have hs : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  rw [expOf_eq, derivative_subst R hs, derivative_exp, mul_comm]

variable [IsAddTorsionFree R]

/-- The formal exponential converts sums into products.
(blueprint: `lemma:weil-exp-add`) -/
theorem expOf_add {f g : R⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    expOf (f + g) = expOf f * expOf g := by
  have hfg : constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  refine eq_of_derivative_eq_mul (H := d⁄dX R f + d⁄dX R g) (constantCoeff_expOf hfg)
    (by rw [map_mul, constantCoeff_expOf hf, constantCoeff_expOf hg, mul_one])
    (by rw [derivative_expOf hfg, map_add]) ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_expOf hf, derivative_expOf hg]
  ring

/-- The formal exponential of `0` is `1`.
(blueprint: `lemma:weil-exp-zero`) -/
@[simp]
theorem expOf_zero : expOf (0 : R⟦X⟧) = 1 :=
  eq_one_of_derivative_eq_zero (constantCoeff_expOf (map_zero _))
    (by rw [derivative_expOf (map_zero _), map_zero, zero_mul])

end

end PowerSeries

end
