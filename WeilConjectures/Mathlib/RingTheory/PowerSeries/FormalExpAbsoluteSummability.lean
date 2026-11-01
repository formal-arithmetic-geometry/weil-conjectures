/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-! Ordered tuple products used in the boundary evaluation of the formal exponential.

Source: blueprint `latest`,
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The L-function on U_0" (blueprint: lem-wf-formal-exp-tuple-product-rows).

This lemma is the row-wise Cauchy-product calculation.  It is strictly below the
formal-exponential evaluation statement: it knows only an absolutely summable sequence and
one fixed tuple length.
-/

@[expose] public section

open scoped BigOperators
namespace PowerSeries

/-- Ordered products of an absolutely summable sequence form an absolutely summable row, and
its norm sum is the corresponding power of the original norm sum. -/
theorem summable_ordered_tuple_products (a : ℕ → ℂ) (r : ℕ)
    (ha : Summable fun n : ℕ ↦ ‖a n‖) :
    Summable (fun v : Fin r → ℕ ↦ ∏ i, a (v i)) ∧
      (∑' v : Fin r → ℕ, ‖∏ i, a (v i)‖) = (∑' n : ℕ, ‖a n‖) ^ r := by
  sorry

end PowerSeries
