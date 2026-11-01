/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-! Complex degree regrouping for the formal exponential boundary argument.

Source: blueprint `latest`,
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The L-function on U_0" (blueprint: lem-wf-formal-exp-degree-regrouping).

This bridge is the complex-valued regrouping step.  It consumes the row products and finite
coefficient identity, and is strictly smaller than the complete item because it does not
construct those inputs.
-/

@[expose] public section

open scoped BigOperators
namespace PowerSeries

/-- The complex degree regrouping of the factorial-weighted tuple family is the ordinary
complex exponential of the sum of the input sequence.
(blueprint: lem-wf-formal-exp-degree-evaluation)
-/
theorem tsum_degree_regrouping_from_rows (U : PowerSeries ℂ) (z : ℂ)
    (hU : constantCoeff U = 0)
    (hsum : Summable fun n : ℕ ↦ ‖coeff (n + 1) U * z ^ (n + 1)‖)
    (hrows : ∀ r : ℕ, Summable (fun v : Fin r → ℕ ↦
      ∏ i, coeff (v i + 1) U * z ^ (v i + 1)))
    (hcoef : ∀ m : ℕ, coeff m ((exp ℂ).subst U) =
      ∑ d ∈ Finset.range (m + 1),
        (algebraMap ℚ ℂ (1 / Nat.factorial d)) •
          (∑ l ∈ Finset.finsuppAntidiag (Finset.range d) m,
            ∏ i ∈ Finset.range d, coeff (l i) U)) :
    (∑' m : ℕ, coeff m ((exp ℂ).subst U) * z ^ m) =
      Complex.exp (∑' n : ℕ, coeff (n + 1) U * z ^ (n + 1)) := by
  sorry

end PowerSeries
