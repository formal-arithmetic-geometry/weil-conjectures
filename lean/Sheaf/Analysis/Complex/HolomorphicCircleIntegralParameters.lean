module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint analyticity of a circle Cauchy integral with parameters

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A (3.3),
printed p.21, and I §3.B (3.8)--(3.9), printed p.22; parameter-integral consequence
of the uniform Cauchy expansions, formulated in the DAG.
(blueprint: lem-sfb-holomorphic-circle-integral-parameters)

Functions on the open product are represented by total functions with analyticity
required only on that product. Values outside it do not affect the circle integral.
-/

@[expose] public section

set_option autoImplicit false

namespace Complex

/-- The normalized positively oriented Cauchy integral of an analytic family on an
annulus is integrable and jointly analytic in the interior point and the parameters.
`AnalyticOnNhd` means locally represented by a convergent complex power series;
the first coordinate and all `d` parameter coordinates vary jointly.

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A (3.3),
printed p.21, and I §3.B (3.8)--(3.9), printed p.22; the parameter-integral
consequence is formulated by the DAG worker, not separately numbered there.
(blueprint: lem-sfb-holomorphic-circle-integral-parameters)

Proof plan (the accepted agent-written parameter-integral assembly):
1. At `(z₀,w₀)` set `δ = R - ‖z₀-c‖ > 0`. Choose `0 < r < δ` and a closed
   parameter polydisc of radius `s > ρ > 0` contained in `P`. Analyticity gives
   continuity (lem-sfb-complex-analytic-function-operations), so the integrand is
   continuous on the circle and integrable. The compact parameter Taylor lemma
   (lem-sfb-compact-parameter-taylor-expansion) gives continuous coefficients
   `a_α(ζ)` with bounds `‖a_α(ζ)‖ ≤ M s^(-|α|)`, uniformly on the circle.
2. Expand the kernel as `∑ n, u^n / (ζ-z₀)^(n+1)` using
   lem-sfb-scalar-geometric-series. Since `‖ζ-z₀‖ ≥ δ`, the terms are bounded
   by `δ⁻¹ (r/δ)^n` and the geometric tail bound is uniform in `ζ` and `u`.
3. Multiply the two expansions. With `p = r/δ < 1` and `q = ρ/s < 1`, the
   product terms have majorant `M δ⁻¹ p^n q^|α|`. Rectangular finite sums have
   limit `C = M / (δ (1-p) (1-q)^d)`, and the tail outside the box of side `N`
   is at most `C (p^N + d q^N)`. Every finite set is in a box. Thus the double
   series converges absolutely and uniformly; lem-sfb-absolute-series-domination
   also gives summability of its norms and of all families with this majorant.
4. Parametrize the circle by `γ(t)=c+R exp(t I)`, with `‖γ'(t)‖=R`.
   Apply lem-sfb-normal-series-interval-integration to integrate term by term.
   The coefficients are the normalized integrals of
   `a_α(γ(t)) γ'(t) / (γ(t)-z₀)^(n+1)` and have norm at most
   `R M δ^(-n-1) s^(-|α|)`. Domination gives a convergent power series for
   the displayed function in all `d+1` coordinates at `(z₀,w₀)`. The point was
   arbitrary. When `P` is empty the conclusions are vacuous; when `d=0` there
   is a single parameter multi-index and the same argument applies. -/
theorem analyticOnNhd_circleIntegral_parameters
    (d : ℕ) (P : Set (Fin d → ℂ)) (hP : IsOpen P)
    (c : ℂ) (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R)
    (g : (ℂ × (Fin d → ℂ)) → ℂ)
    (hg : AnalyticOnNhd ℂ g
      ({ζ : ℂ | R - ε < ‖ζ - c‖ ∧ ‖ζ - c‖ < R + ε} ×ˢ P)) :
    (∀ z ∈ Metric.ball c R, ∀ w ∈ P,
      CircleIntegrable (fun ζ : ℂ ↦ g (ζ, w) / (ζ - z)) c R) ∧
    AnalyticOnNhd ℂ
      (fun x : ℂ × (Fin d → ℂ) ↦
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral (fun ζ : ℂ ↦ g (ζ, x.2) / (ζ - x.1)) c R)
      (Metric.ball c R ×ˢ P) := by
  sorry

end Complex
