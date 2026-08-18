/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# The formal exponential, and its inverse the formal logarithm

Mathlib provides the logarithmic power series `PowerSeries.log` together with the
substituted logarithm `PowerSeries.logOf f = (log R).subst (f - 1)`.  This file adds the
companion `PowerSeries.expOf f = (exp R).subst f` and shows that over a torsion-free
`ℚ`-algebra `expOf` and `logOf` are mutually inverse bijections between the power series
with constant coefficient `0` and the power series with constant coefficient `1`,
exchanging sums for products.

The engine is `PowerSeries.eq_of_derivative_eq_mul`: two power series with constant
coefficient `1` satisfying the same logarithmic differential equation `d⁄dX F = H * F`
are equal.  That statement needs no denominators and holds over any torsion-free
commutative ring.

## Main definitions

- `PowerSeries.expOf`
- `PowerSeries.oneSubmonoid`, the submonoid of power series with constant coefficient `1`
- `PowerSeries.expOfMulEquiv`, the exponential/logarithm bijection bundled as a
  multiplicative equivalence

## Main results

- `PowerSeries.eq_of_derivative_eq_mul`
- `PowerSeries.derivative_expOf`, `PowerSeries.derivative_logOf`
- `PowerSeries.expOf_add`, `PowerSeries.logOf_mul`, `PowerSeries.logOf_prod`
- `PowerSeries.logOf_expOf`, `PowerSeries.expOf_logOf`
-/

@[expose] public section

namespace PowerSeries

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

/-! ### Uniqueness for logarithmic differential equations -/

/-- Two power series with constant coefficient `1` solving the same logarithmic
differential equation `d⁄dX F = H * F` are equal.
(blueprint: `lemma:weil-eq-of-derivative-eq-mul`) -/
theorem eq_of_derivative_eq_mul [IsAddTorsionFree R] {H P Q : R⟦X⟧}
    (hP : constantCoeff P = 1) (hQ : constantCoeff Q = 1)
    (hP' : d⁄dX R P = H * P) (hQ' : d⁄dX R Q = H * Q) : P = Q := by
  have h1 : Q * invOfUnit Q 1 = 1 := mul_invOfUnit Q 1 (by rw [hQ, Units.val_one])
  have h2 : Q * d⁄dX R (invOfUnit Q 1) + invOfUnit Q 1 * (H * Q) = 0 := by
    have h := congrArg (d⁄dX R) h1
    rwa [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.map_one_eq_zero, hQ'] at h
  have h3 : d⁄dX R (invOfUnit Q 1) = -(H * invOfUnit Q 1) := by
    linear_combination invOfUnit Q 1 * h2 - (d⁄dX R (invOfUnit Q 1) + H * invOfUnit Q 1) * h1
  have hd : d⁄dX R (P * invOfUnit Q 1) = d⁄dX R (1 : R⟦X⟧) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP', h3, Derivation.map_one_eq_zero]
    ring
  have hc : constantCoeff (P * invOfUnit Q 1) = constantCoeff (1 : R⟦X⟧) := by
    rw [map_mul, hP, constantCoeff_invOfUnit, map_one, one_mul, inv_one, Units.val_one]
  have heq : P * invOfUnit Q 1 = 1 := derivative.ext hd hc
  linear_combination Q * heq - P * h1

/-- A power series with constant coefficient `1` and vanishing derivative is `1`.
(blueprint: `lemma:weil-eq-one-of-derivative-eq-zero`) -/
theorem eq_one_of_derivative_eq_zero [IsAddTorsionFree R] {P : R⟦X⟧}
    (hP : constantCoeff P = 1) (hP' : d⁄dX R P = 0) : P = 1 :=
  derivative.ext (by rw [hP', Derivation.map_one_eq_zero]) (by rw [hP, map_one])

/-! ### The submonoid of series with constant coefficient one -/

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

/-! ### The alternating geometric series -/

/-- The alternating geometric series is inverse to `1 + X`.
(blueprint: `lemma:weil-mk-neg-one-pow-mul-one-add-X`) -/
theorem mk_neg_one_pow_mul_one_add_X (R : Type*) [CommRing R] :
    (mk fun n ↦ (-1 : R) ^ n) * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, coeff_one]
  cases n with
  | zero => rw [coeff_zero_mul_X, add_zero, coeff_mk, pow_zero, if_pos rfl]
  | succ k =>
    rw [coeff_succ_mul_X, coeff_mk, coeff_mk, if_neg (Nat.succ_ne_zero k), pow_succ]
    ring

variable [Algebra ℚ R]

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

/-! ### The formal exponential -/

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

/-- Chain rule for the formal logarithm.
(blueprint: `lemma:weil-derivative-log`) -/
theorem derivative_logOf {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX R (logOf f) = d⁄dX R f * invOfUnit f 1 := by
  have hs : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_sub, map_one, hf, sub_self])
  rw [logOf_eq, derivative_subst R hs, subst_derivative_log hf, map_sub,
    Derivation.map_one_eq_zero, sub_zero, mul_comm]

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
