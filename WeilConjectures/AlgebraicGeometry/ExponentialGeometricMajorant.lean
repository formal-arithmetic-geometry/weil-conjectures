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

/-! # Evaluation of a formal exponential under a geometric majorant

Source: latest blueprint, `sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md`,
paragraphs 2–3 (blueprint: lem-wf-exponential-geometric-majorant).
-/

@[expose] public section

set_option autoImplicit false

namespace PowerSeries

/-- A geometric bound on the logarithmic coefficients gives absolute convergence of the
logarithm and its formal exponential, and the latter evaluates to the nonzero complex
exponential of the logarithm's sum. The unused value `c 0` imposes no condition: the formal
logarithm has constant coefficient zero, and the analytic logarithm is indexed by `n + 1`.

Source: latest blueprint, `sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md`,
paragraphs 2–3 (blueprint: lem-wf-exponential-geometric-majorant).

Proof: Set `t = B * ‖z‖`. Positivity of `B` and the strict disc condition give `0 ≤ t < 1`.
For each positive `n`, multiplicativity of the norm and `1 / n ≤ 1` bound
`‖c n * z ^ n / n‖` by `M * t ^ n`. The geometric series is summable by
`lem-wf-real-geometric-summability`; the nonnegative comparison test
`lem-rp-nonnegative-summable-comparison` gives absolute convergence of the logarithm.
Apply `lem-wf-formal-exp-summable-evaluation` with coefficients `u n = c n / n` for
positive `n`. Its formal series is the displayed zero-constant-coefficient series, so its
formal exponential has exactly the displayed coefficients. That lemma gives absolute
convergence of the exponential series, the equality with the usual complex exponential,
and nonvanishing. -/
theorem exponential_geometric_majorant (c : ℕ → ℂ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 < B)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ M * B ^ n)
    (z : ℂ) (hz : ‖z‖ < B⁻¹) :
    (Summable fun n : ℕ ↦ ‖c (n + 1) * z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)‖) ∧
    (Summable fun m : ℕ ↦
      ‖coeff m ((exp ℂ).subst
        (mk fun n : ℕ ↦ if n = 0 then 0 else c n / (n : ℂ))) * z ^ m‖) ∧
    (∑' m : ℕ, coeff m ((exp ℂ).subst
        (mk fun n : ℕ ↦ if n = 0 then 0 else c n / (n : ℂ))) * z ^ m) =
      Complex.exp (∑' n : ℕ, c (n + 1) * z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) ∧
    Complex.exp (∑' n : ℕ, c (n + 1) * z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
  sorry

end PowerSeries
