/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-! Finite coefficient data for the formal exponential substitution.

Source: blueprint `latest`,
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-at-the-boundary-points/sk-p-real-semi/sk-p-real-semi.proof.md`, paragraph
"The L-function on U_0" (blueprint: lem-wf-formal-exp-finite-coefficients).

The coefficient formula is finite because a zero constant coefficient makes all sufficiently
large powers vanish at any fixed coefficient.  This is a finite algebraic fact, independent of
analytic regrouping.
-/

@[expose] public section

open scoped BigOperators
namespace PowerSeries

/-- The coefficient of a substituted formal exponential is a finite sum of finite Cauchy
products. (blueprint: lem-wf-formal-exp-evaluation-identity)
-/
theorem coeff_exp_subst_finite_formula (U : PowerSeries ℂ)
    (hU : constantCoeff U = 0) (m : ℕ) :
    coeff m ((exp ℂ).subst U) =
      ∑ d ∈ Finset.range (m + 1),
        (algebraMap ℚ ℂ (1 / Nat.factorial d)) •
          (∑ l ∈ Finset.finsuppAntidiag (Finset.range d) m,
            ∏ i ∈ Finset.range d, coeff (l i) U) := by
  sorry

end PowerSeries
