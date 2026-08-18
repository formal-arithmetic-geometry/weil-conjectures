/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Uniqueness for logarithmic differential equations

Mathlib's `PowerSeries.derivative.ext` says that a power series is determined by its
derivative and its constant coefficient.  This file records the multiplicative form: a
power series with constant coefficient `1` is determined by its logarithmic derivative.
Neither statement needs denominators, so both hold over any torsion-free commutative ring.

## Main results

- `PowerSeries.eq_of_derivative_eq_mul`
- `PowerSeries.eq_one_of_derivative_eq_zero`
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- Two power series with constant coefficient `1` solving the same logarithmic
differential equation `d⁄dX F = H * F` are equal.
(blueprint: `lemma:weil-eq-of-derivative-eq-mul`) -/
theorem eq_of_derivative_eq_mul {H P Q : R⟦X⟧}
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
theorem eq_one_of_derivative_eq_zero {P : R⟦X⟧}
    (hP : constantCoeff P = 1) (hP' : d⁄dX R P = 0) : P = 1 :=
  derivative.ext (by rw [hP', Derivation.map_one_eq_zero]) (by rw [hP, map_one])

end PowerSeries

end
