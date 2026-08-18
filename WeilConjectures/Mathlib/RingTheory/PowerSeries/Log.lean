/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Basic
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Exp

/-!
# The formal logarithm is inverse to the formal exponential

Mathlib provides the logarithmic power series `PowerSeries.log` together with the
substituted logarithm `PowerSeries.logOf f = (log R).subst (f - 1)`.  This file shows that
over a torsion-free `ℚ`-algebra `PowerSeries.logOf` and `PowerSeries.expOf` are mutually
inverse bijections between the power series with constant coefficient `0` and the power
series with constant coefficient `1`, exchanging sums for products.

The engine is `PowerSeries.eq_of_derivative_eq_mul`: two power series with constant
coefficient `1` satisfying the same logarithmic differential equation `d⁄dX F = H * F`
are equal.

## Main definitions

- `PowerSeries.expOfMulEquiv`, the exponential/logarithm bijection bundled as a
  multiplicative equivalence

## Main results

- `PowerSeries.derivative_logOf`
- `PowerSeries.logOf_expOf`, `PowerSeries.expOf_logOf`
- `PowerSeries.logOf_mul`, `PowerSeries.logOf_prod`
-/

@[expose] public section

namespace PowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R] {ι : Type*}

/-- The derivative of `log` substituted at `f - 1` is the inverse of `f`.
(blueprint: `lemma:weil-subst-derivative-log`) -/
theorem subst_derivative_log {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    (d⁄dX R (log R)).subst (f - 1) = invOfUnit f 1 := by
  have hs : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_sub, map_one, hf, sub_self])
  have hgeom : d⁄dX R (log R) = mk fun n ↦ (-1 : R) ^ n := by
    rw [deriv_log]
    exact congrArg mk (funext fun n ↦ by rw [map_pow, map_neg, map_one])
  have hone : (1 : R⟦X⟧) + (f - 1) = f := by ring
  have key : (d⁄dX R (log R)).subst (f - 1) * f = 1 := by
    have h := congrArg (substAlgHom (R := R) hs) (mk_neg_one_pow_mul_one_add_X R)
    rw [map_mul, map_one, map_add, map_one, substAlgHom_X, coe_substAlgHom, hone] at h
    rw [hgeom]
    exact h
  have hinv : f * invOfUnit f 1 = 1 := mul_invOfUnit f 1 (by rw [hf, Units.val_one])
  linear_combination invOfUnit f 1 * key - ((d⁄dX R (log R)).subst (f - 1)) * hinv

/-- Chain rule for the formal logarithm.
(blueprint: `lemma:weil-derivative-log`) -/
theorem derivative_logOf {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX R (logOf f) = d⁄dX R f * invOfUnit f 1 := by
  have hs : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_sub, map_one, hf, sub_self])
  rw [logOf_eq, derivative_subst R hs, subst_derivative_log hf, map_sub,
    Derivation.map_one_eq_zero, sub_zero, mul_comm]

variable [IsAddTorsionFree R]

/-- The formal logarithm is a left inverse of the formal exponential.
(blueprint: `prop:weil-log-exp`) -/
theorem logOf_expOf {f : R⟦X⟧} (hf : constantCoeff f = 0) : logOf (expOf f) = f := by
  have hc := constantCoeff_expOf hf
  refine derivative.ext ?_ (by rw [constantCoeff_logOf hc, hf])
  rw [derivative_logOf hc, derivative_expOf hf]
  linear_combination d⁄dX R f * mul_invOfUnit (expOf f) 1 (by rw [hc, Units.val_one])

/-- The formal exponential is a left inverse of the formal logarithm.
(blueprint: `prop:weil-exp-log`) -/
theorem expOf_logOf {f : R⟦X⟧} (hf : constantCoeff f = 1) : expOf (logOf f) = f := by
  refine eq_of_derivative_eq_mul (H := d⁄dX R f * invOfUnit f 1)
    (constantCoeff_expOf (constantCoeff_logOf hf)) hf
    (by rw [derivative_expOf (constantCoeff_logOf hf), derivative_logOf hf]) ?_
  linear_combination (-(d⁄dX R f)) * invOfUnit_mul f 1 (by rw [hf, Units.val_one])

/-- The formal logarithm of `1` is `0`.
(blueprint: `lemma:weil-log-one`) -/
@[simp]
theorem logOf_one : logOf (1 : R⟦X⟧) = 0 := by
  rw [← expOf_zero (R := R), logOf_expOf (map_zero _)]

/-- The formal logarithm converts products into sums.
(blueprint: `prop:weil-log-mul`) -/
theorem logOf_mul {f g : R⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hsum : constantCoeff (logOf f + logOf g) = 0 := by
    rw [map_add, constantCoeff_logOf hf, constantCoeff_logOf hg, add_zero]
  have h := expOf_add (constantCoeff_logOf hf) (constantCoeff_logOf hg)
  rw [expOf_logOf hf, expOf_logOf hg] at h
  rw [← h, logOf_expOf hsum]

/-- The formal logarithm converts finite products into finite sums.
(blueprint: `prop:weil-log-prod`) -/
theorem logOf_prod (S : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ S, constantCoeff (f i) = 1) :
    logOf (∏ i ∈ S, f i) = ∑ i ∈ S, logOf (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hprod : constantCoeff (∏ i ∈ s, f i) = 1 := by
      rw [map_prod]
      exact Finset.prod_eq_one fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      logOf_mul (hf a (Finset.mem_insert_self a s)) hprod,
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-! ### The exponential/logarithm bijection -/

/-- The formal exponential is a bijection from the power series with constant coefficient
`0` onto the power series with constant coefficient `1`, taking sums to products; its
inverse is the formal logarithm.
(blueprint: `thm:weil-exp-log-equiv`) -/
def expOfMulEquiv :
    Multiplicative (RingHom.ker (constantCoeff (R := R))) ≃* oneSubmonoid R where
  toFun f :=
    ⟨expOf f.toAdd.1, constantCoeff_expOf (RingHom.mem_ker.1 f.toAdd.2)⟩
  invFun f :=
    Multiplicative.ofAdd
      ⟨logOf f.1, RingHom.mem_ker.2 (constantCoeff_logOf (mem_oneSubmonoid.1 f.2))⟩
  left_inv f := Subtype.ext (logOf_expOf (RingHom.mem_ker.1 f.toAdd.2))
  right_inv f := Subtype.ext (expOf_logOf (mem_oneSubmonoid.1 f.2))
  map_mul' f g := Subtype.ext (expOf_add (RingHom.mem_ker.1 f.toAdd.2)
    (RingHom.mem_ker.1 g.toAdd.2))

@[simp]
theorem expOfMulEquiv_apply (f : Multiplicative (RingHom.ker (constantCoeff (R := R)))) :
    (expOfMulEquiv f : R⟦X⟧) = expOf f.toAdd.1 :=
  rfl

@[simp]
theorem expOfMulEquiv_symm_apply (f : oneSubmonoid R) :
    ((expOfMulEquiv.symm f).toAdd : R⟦X⟧) = logOf f.1 :=
  rfl

end

end PowerSeries

end
