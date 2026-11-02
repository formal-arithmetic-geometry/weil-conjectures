/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

import WeilConjectures.Mathlib.RingTheory.PowerSeries.FormalExpAbsoluteSummability
import WeilConjectures.Mathlib.RingTheory.PowerSeries.FormalExpEvaluationIdentity
import WeilConjectures.Mathlib.RingTheory.PowerSeries.FormalExpDegreeRegrouping
import WeilConjectures.Mathlib.RingTheory.PowerSeries.FormalExpDegreeEvaluation

/-! # Evaluation of the formal exponential of an absolutely convergent series

Source: blueprint `latest`,
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The L-function on U_0": the logarithmic coefficient series converges,
and its exponential is nonvanishing
(blueprint: lem-wf-formal-exp-summable-evaluation).

The positive-degree coefficients of `U` are the sequence in the informal statement. The formal
exponential is the existing `PowerSeries.exp` substituted at `U`.
-/

@[expose] public section

open scoped BigOperators

namespace PowerSeries

/-- Absolute convergence at a point permits evaluation of the formal exponential.

Source: blueprint `latest`,
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The L-function on U_0" (blueprint: lem-wf-formal-exp-summable-evaluation).

Proof:
1. Put `a_n = u_n z^n`, `A = ∑ |a_n|`, and `s = ∑ a_n`. The bounded-subsums and
   domination clauses of `lem-sfb-absolute-series-domination` convert absolute series
   convergence into summability. For each `r`, induction using
   `lem-wf-absolutely-summable-product` on ordered tuples gives the row products and their
   norm sums.
2. Weight each row by `1/r!`; the scalar exponential majorant and absolute domination give
   the factorial-weighted tuple family.
3. Regroup by tuple length and use the scalar exponential series to identify the complex sum.
4. The finite coefficient formula and finite degree fibres identify the degree regrouping;
   the triangle inequality gives the norm summability.
5. Regroup the complex family by degree and identify its sum with the evaluated formal
   exponential and with `Complex.exp s`; the latter is nonzero.
-/
theorem summable_norm_exp_subst_and_tsum_eq (U : PowerSeries ℂ) (z : ℂ)
    (hU : constantCoeff U = 0)
    (hsum : Summable fun n : ℕ ↦ ‖coeff (n + 1) U * z ^ (n + 1)‖) :
    (Summable fun m : ℕ ↦ ‖coeff m ((exp ℂ).subst U) * z ^ m‖) ∧
      (∑' m : ℕ, coeff m ((exp ℂ).subst U) * z ^ m) =
        Complex.exp (∑' n : ℕ, coeff (n + 1) U * z ^ (n + 1)) ∧
      Complex.exp (∑' n : ℕ, coeff (n + 1) U * z ^ (n + 1)) ≠ 0 := by
  have hrows : ∀ r : ℕ, Summable (fun v : Fin r → ℕ ↦
      ∏ i, coeff (v i + 1) U * z ^ (v i + 1)) := by
    intro r
    exact (summable_ordered_tuple_products
      (fun n : ℕ ↦ coeff (n + 1) U * z ^ (n + 1)) r hsum).1
  have hcoef : ∀ m : ℕ, coeff m ((exp ℂ).subst U) =
      ∑ d ∈ Finset.range (m + 1),
        (algebraMap ℚ ℂ (1 / Nat.factorial d)) •
          (∑ l ∈ Finset.finsuppAntidiag (Finset.range d) m,
            ∏ i ∈ Finset.range d, coeff (l i) U) := by
    intro m
    exact coeff_exp_subst_finite_formula U hU m
  have hnorm := norm_degree_regrouping_from_rows U z hU hsum hrows hcoef
  have hvalue := tsum_degree_regrouping_from_rows U z hU hsum hrows hcoef
  exact ⟨hnorm, hvalue, Complex.exp_ne_zero _⟩

end PowerSeries
