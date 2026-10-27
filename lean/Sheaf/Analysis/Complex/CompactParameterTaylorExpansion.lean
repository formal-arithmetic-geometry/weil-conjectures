module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Uniform parameter Taylor expansion on a compact set

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A (3.3),
I §3.B (3.8)--(3.9); the compact-uniform parameter version is the auxiliary
formulated in the DAG, with an accepted agent-written iterated Cauchy proof.
(blueprint: lem-sfb-compact-parameter-taylor-expansion)

The supremum norms are taken in `ℝ≥0`, so a supremum over an empty compact set
is zero. The finite-subsum filter expresses uniform convergence without choosing
an enumeration of the multi-indices. Total functions represent functions on the
open product, and analyticity is required only on that product.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Complex

open scoped Classical in
/-- A holomorphic function on an open product has continuous parameter Taylor
coefficients on any compact subset of its first factor, with a common Cauchy
bound from a closed parameter polydisc. On every smaller closed polydisc the
sum of the supremum norms is summable and satisfies the geometric bound, and
the net of finite subsums converges uniformly. For nonempty `K` the same `M`
is the maximum of `‖g‖` on the compact product. The zero-dimensional parameter
case has just its constant coefficient.

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A (3.3),
I §3.B (3.8)--(3.9); compact-uniform auxiliary formulated in the DAG.
(blueprint: lem-sfb-compact-parameter-taylor-expansion)

Proof plan (the accepted agent-written iterated Cauchy argument):
1. For empty `K`, choose `M=0` and the empty coefficient maps. Otherwise analytic
   continuity (lem-sfb-complex-analytic-function-operations), compactness of the
   product (lem-sfb-complex-polydisc-compactness), and the minimum theorem for
   `-‖g‖` (lem-sfb-compact-real-function-minimum) give its maximum `M≥0`.
   For `d=0`, use `a₀(ζ)=g(ζ,w₀)` and the single-term series.
2. For positive `d`, set `θⱼ(t)=w₀ⱼ+s exp(it)` and define `a_α` by the nested
   integrals of `g(ζ,θ(t)) exp(-i∑ⱼαⱼtⱼ)`, normalized by `(2π)^(-d)s^(-|α|)`.
   Integrate `t_d` first and `t₁` last. Compact uniform continuity
   (lem-sfb-compact-uniform-continuity) and the interval integral bound
   (lem-sfb-normal-series-interval-integration) show inductively that intermediate
   integrals are continuous, exist, and give `‖a_α(ζ)‖≤M s^(-|α|)`.
3. Each coordinate slice is analytic by composition and hence differentiable
   (lem-sfb-analytic-germ-differentiable). Apply lem-sfb-cauchy-circle-formula
   successively to coordinates `1,...,d`, inserting each new integral innermost.
   After parametrization this represents `g(ζ,w₀+v)` by the same nested integrals
   with kernel `∏ⱼ(1-vⱼ/(s exp(itⱼ)))⁻¹`. No integration order is exchanged.
4. For `0<ρ<s`, expand each kernel by lem-sfb-scalar-geometric-series and multiply
   with lem-sfb-absolute-series-product. Their monomial terms have common bounds
   `M (ρ/s)^|α|`, whose sum is `M (1-ρ/s)^(-d)`.
   Lemma lem-sfb-absolute-series-domination gives absolute convergence.
5. Apply lem-sfb-normal-series-interval-integration successively in `t_d,...,t₁`.
   At each step the terms remain continuous and have the summable majorant
   `(2π)^k M (ρ/s)^|α|`. This justifies all interchanges and identifies each
   integrated coefficient with `a_α`, giving the series identity for `‖vⱼ‖≤ρ`.
6. Each term's supremum norm is bounded by `M (ρ/s)^|α|`; domination gives the
   stated sum bound. Summable tails bound all finite-subsum remainders uniformly
   in `ζ,v`, proving uniform convergence. Any point of the open polydisc lies in
   a smaller closed polydisc, giving the full identity. Empty `K` and `d=0`
   have already been included. -/
theorem exists_compact_parameter_taylor_expansion
    (d : ℕ) (U : Set ℂ) (P : Set (Fin d → ℂ))
    (hU : IsOpen U) (hP : IsOpen P) (K : Set ℂ)
    (hKU : K ⊆ U) (hK : IsCompact K)
    (g : (ℂ × (Fin d → ℂ)) → ℂ) (hg : AnalyticOnNhd ℂ g (U ×ˢ P))
    (w₀ : Fin d → ℂ) (hw₀ : w₀ ∈ P) (s : ℝ) (hs : 0 < s)
    (hQ : {w : Fin d → ℂ | ∀ j, ‖w j - w₀ j‖ ≤ s} ⊆ P) :
    ∃ (M : ℝ) (a : (Fin d → ℕ) → C(K, ℂ)), 0 ≤ M ∧
      (∀ (α : Fin d → ℕ) (ζ : K),
        ‖a α ζ‖ ≤ M * (s ^ (∑ j, α j))⁻¹) ∧
      (∀ (ζ : K) (v : Fin d → ℂ), (∀ j, ‖v j‖ < s) →
        HasSum (fun α : Fin d → ℕ ↦ a α ζ * ∏ j, v j ^ α j)
          (g (ζ, w₀ + v))) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < s →
        Summable (fun α : Fin d → ℕ ↦
          ((⨆ (ζ : K) (v : {v : Fin d → ℂ // ∀ j, ‖v j‖ ≤ ρ}),
            ‖a α ζ * ∏ j, v.val j ^ α j‖₊) : ℝ)) ∧
        (∑' α : Fin d → ℕ,
          ((⨆ (ζ : K) (v : {v : Fin d → ℂ // ∀ j, ‖v j‖ ≤ ρ}),
            ‖a α ζ * ∏ j, v.val j ^ α j‖₊) : ℝ)) ≤
          M * ((1 - ρ / s) ^ d)⁻¹ ∧
        TendstoUniformlyOn
          (fun F : Finset (Fin d → ℕ) ↦ fun x : K × (Fin d → ℂ) ↦
            ∑ α ∈ F, a α x.1 * ∏ j, x.2 j ^ α j)
          (fun x : K × (Fin d → ℂ) ↦ g (x.1, w₀ + x.2)) Filter.atTop
          {x : K × (Fin d → ℂ) | ∀ j, ‖x.2 j‖ ≤ ρ}) ∧
      (K.Nonempty → IsGreatest
        ((fun x : ℂ × (Fin d → ℂ) ↦ ‖g x‖) ''
          (K ×ˢ {w : Fin d → ℂ | ∀ j, ‖w j - w₀ j‖ ≤ s})) M) ∧
      (d = 0 → ∀ ζ : K, a (fun _ : Fin d ↦ 0) ζ = g (ζ, w₀)) := by
  sorry

end Complex
