/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.LinearRecurrence

/-!
# Linear recurrence from a rational power series

Source: Milne, Lectures on Étale Cohomology, Ch. II, §27, proof of Lemma 27.9,
p. 157 (quoting Bourbaki, Algèbre, IV.5, Exercise 3(a)); blueprint
`sec-zeta-weil/sk-prop-criterion/prop-weil-rationality-criterion.proof.md`, final paragraph
(blueprint: lem-weil-rational-series-linear-recurrence).
-/

@[expose] public section

universe u

namespace PowerSeries

/-- A normalized polynomial denominator gives a recurrence of order `max Q.natDegree 1`
from every index `m` for which the numerator vanishes in degrees at least `m` plus that order.
Mathlib's recurrence coefficients are the negatives of `aᵢ = Q.coeff (d - i)`, because
`LinearRecurrence.IsSolution` puts the finite sum on the right side of the equality.

Source: Milne, Lectures on Étale Cohomology, Ch. II, §27, proof of Lemma 27.9, p. 157,
quoting Bourbaki IV.5, Exercise 3(a); the final paragraph of the blueprint proof of
`prop-weil-rationality-criterion` (blueprint: lem-weil-rational-series-linear-recurrence).

Proof: Write `d = max Q.natDegree 1`. First, `Q.coeff 0 = 1` makes `Q` nonzero, and
`Q.coeff j = 0` for `j > d`, by the polynomial degree and coefficient definitions
(def-weil-polynomial-ring, def-weil-polynomial-coefficient). Second, for `n ≥ m`, put
`N = n + d`. The assumed vanishing gives `P.coeff N = 0`. Comparing coefficients in
`Q * C = P`, using the coefficient-preserving polynomial inclusion and the Cauchy product
(def-weil-polynomial-as-power-series, def-weil-formal-power-series), gives
`0 = C.coeff (n + d) + ∑ j = 1, …, d, Q.coeff j * C.coeff (n + d - j)`.
Third, reindex by `i = d - j`, obtaining the recurrence with `aᵢ = Q.coeff (d - i)`
(def-weil-eventual-linear-recurrence). Moving this sum to the right and shifting the
sequence by `m` gives precisely `LinearRecurrence.IsSolution` below. Finally,
`m = P.natDegree + 1` always meets the vanishing condition, and `m = 0` does when `P = 0`.
For `Q = 1` the order is `1`, its sole recurrence coefficient is `0`, and the relation
reduces to `C.coeff (n + 1) = 0` for `n ≥ m`, including `P = 0, m = 0`. -/
theorem isSolution_of_polynomial_mul_eq_polynomial {K : Type u} [Field K]
    (C : PowerSeries K) (P Q : Polynomial K) (hQ : Q.coeff 0 = 1)
    (hQC : (Q : PowerSeries K) * C = (P : PowerSeries K)) (m : ℕ)
    (hP : ∀ N : ℕ, m + max Q.natDegree 1 ≤ N → P.coeff N = 0) :
    LinearRecurrence.IsSolution
      ({ order := max Q.natDegree 1
         coeffs := fun i : Fin (max Q.natDegree 1) ↦
           -Q.coeff (max Q.natDegree 1 - (i : ℕ)) } : LinearRecurrence K)
      (fun n : ℕ ↦ PowerSeries.coeff (n + m) C) := by
  sorry

end PowerSeries
