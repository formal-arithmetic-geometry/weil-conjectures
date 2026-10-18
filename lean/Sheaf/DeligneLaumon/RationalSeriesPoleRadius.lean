/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# An uncancelled polynomial denominator root bounds the convergence radius

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/
sk-l-dl-a1-energy/thm-wf-l2-dictionary.proof.md, final paragraph, Taylor-radius
conclusion (blueprint: lem-wf-rational-series-pole-radius).
-/

@[expose] public section

open scoped ENNReal NNReal PowerSeries

namespace PowerSeries

/-- If a formal power series over `ℂ` satisfies a polynomial fraction identity, then an
uncancelled root of the denominator bounds its convergence radius.

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/
sk-l-dl-a1-energy/thm-wf-l2-dictionary.proof.md, final paragraph, Taylor-radius
conclusion (blueprint: lem-wf-rational-series-pole-radius).
The proof assumes a radius larger than `‖a‖`, evaluates the absolutely convergent series at
`a`, and evaluates the finite Cauchy product in `Q * f = P` to obtain `P.eval a = Q.eval a * f(a)`,
contradicting `Q.eval a = 0` and `P.eval a ≠ 0`. -/
theorem radius_le_of_polynomial_mul_eq
    (P Q : Polynomial ℂ) (f : PowerSeries ℂ)
    (hQ0 : Q.coeff 0 ≠ 0) (hQf : (Q : PowerSeries ℂ) * f = (P : PowerSeries ℂ))
    {a : ℂ} (haQ : Q.eval a = 0) (haP : P.eval a ≠ 0) :
    f.radius ≤ ENNReal.ofReal ‖a‖ := by
  sorry

end PowerSeries
