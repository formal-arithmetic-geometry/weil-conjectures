/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Evaluation of the formal exponential of an absolutely convergent series

Source: blueprint `latest`, `part-weights-riemann-hypothesis/sec-purity-real-sheaves/`
`sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The `L`-function on `U_0`": the logarithmic coefficient series converges, and its
exponential is nonvanishing
(blueprint: lem-wf-formal-exp-summable-evaluation).

The positive-degree coefficients of `U` are the sequence in the informal statement.
The formal exponential is the existing `PowerSeries.exp` substituted at `U`.
-/

@[expose] public section

namespace PowerSeries

/-- Absolute convergence at a point permits evaluation of the formal exponential.

Source: blueprint `latest`, `part-weights-riemann-hypothesis/sec-purity-real-sheaves/`
`sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The `L`-function on `U_0`", logarithmic coefficient series
(blueprint: lem-wf-formal-exp-summable-evaluation).

The sequence indexed by positive integers is `coeff (n + 1) U`, with `n : ℕ`.
The condition `constantCoeff U = 0` says precisely that `U` is the series formed
from these coefficients. No strict inequality involving its radius is required.

Proof:
1. Put `a_n = u_n * z^n`, `A = ∑ |a_n|`, and `s = ∑ a_n`. The bounded-subsums
   and domination clauses of lem-sfb-absolute-series-domination convert absolute
   series convergence into summability. For each `r`, induction using
   lem-wf-absolutely-summable-product on ordered `r`-tuples of positive integers
   shows that the products of the `a_n` sum to `s^r`, and their norms sum to `A^r`.
   For `r = 0`, there is one empty tuple and its product is one.
2. On the disjoint union of these tuple sets, divide each product by `r!`.
   Every finite absolute subsum is at most `exp A`, by the row sums and
   lem-wf-scalar-exponential-series. The bounded-subsums and domination clauses
   of lem-sfb-absolute-series-domination give absolute and complex summability.
3. Regroup by tuple length using lem-wf-summable-family-regrouping. The row sums
   are `s^r / r!`, whose sum is `Complex.exp s` by lem-wf-scalar-exponential-series.
4. Regroup the absolute majorant by total degree. Each degree fiber is finite:
   length and coordinates are bounded by the degree, except for the sole empty
   tuple of degree zero. The coefficient formula of def-weil-power-series-exponential
   identifies the corresponding complex fiber sum with `b_m * z^m`. The triangle
   inequality and lem-sfb-absolute-series-domination give its absolute summability.
5. Regroup the complex family by degree using lem-wf-summable-family-regrouping.
   Its sum is both the evaluated formal exponential and `Complex.exp s`.
   Cofinal finite initial segments identify these sums with the ordinary series
   limits. Finally lem-wf-scalar-exponential-series gives nonvanishing.
-/
theorem summable_norm_exp_subst_and_tsum_eq (U : PowerSeries ℂ) (z : ℂ)
    (hU : constantCoeff U = 0)
    (hsum : Summable fun n : ℕ ↦ ‖coeff (n + 1) U * z ^ (n + 1)‖) :
    (Summable fun m : ℕ ↦ ‖coeff m ((exp ℂ).subst U) * z ^ m‖) ∧
      (∑' m : ℕ, coeff m ((exp ℂ).subst U) * z ^ m) =
        Complex.exp (∑' n : ℕ, coeff (n + 1) U * z ^ (n + 1)) ∧
      Complex.exp (∑' n : ℕ, coeff (n + 1) U * z ^ (n + 1)) ≠ 0 := by
  sorry

end PowerSeries
