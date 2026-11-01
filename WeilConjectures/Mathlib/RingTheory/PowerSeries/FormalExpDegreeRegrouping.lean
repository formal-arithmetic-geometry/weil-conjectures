/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-! Absolute degree regrouping for the formal exponential boundary argument.

Source: blueprint `latest`,
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The L-function on U_0" (blueprint: lem-wf-formal-exp-degree-regrouping).

This bridge consumes the fixed-row Cauchy-product calculation and the finite coefficient
formula.  The conclusion is only the norm-summability part of the parent theorem.
-/

@[expose] public section

open scoped BigOperators
namespace PowerSeries

/-- Regrouping the factorial-weighted ordered-tuple majorant by total degree gives absolute
summability of the evaluated formal exponential coefficients. -/
theorem norm_degree_regrouping_from_rows (U : PowerSeries ℂ) (z : ℂ)
    (hU : constantCoeff U = 0)
    (hsum : Summable fun n : ℕ ↦ ‖coeff (n + 1) U * z ^ (n + 1)‖)
    (hrows : ∀ r : ℕ, Summable (fun v : Fin r → ℕ ↦
      ∏ i, coeff (v i + 1) U * z ^ (v i + 1)))
    (hcoef : ∀ m : ℕ, coeff m ((exp ℂ).subst U) =
      ∑ d ∈ Finset.range (m + 1),
        (algebraMap ℚ ℂ (1 / Nat.factorial d)) •
          (∑ l ∈ Finset.finsuppAntidiag (Finset.range d) m,
            ∏ i ∈ Finset.range d, coeff (l i) U)) :
    Summable (fun m : ℕ ↦ ‖coeff m ((exp ℂ).subst U) * z ^ m‖) := by
  sorry

end PowerSeries
