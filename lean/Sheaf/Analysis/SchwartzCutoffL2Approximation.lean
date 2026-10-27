module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Compact smooth approximation of Schwartz derivatives in L²

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, the weak-derivative
Sobolev setup before (2.1), printed p.289; the compact-cutoff argument is agent-written
and is not a separately numbered assertion of that source.
(blueprint: lem-sfb-schwartz-cutoff-l2-approximation)

For a multi-index β, the flattened list below lists coordinate j exactly β j times,
in increasing coordinate order. Evaluating the iterated real Fréchet derivative on
these unit vectors is exactly ∂^β for a smooth function. This uses Mathlib's existing
derivative construction directly, without introducing a second partial-derivative definition.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ContDiff

namespace SchwartzMap

/-- Every complex Schwartz function admits smooth compactly supported approximants whose
multi-index derivatives through any prescribed finite order converge in L². All derivatives
in the convergence assertion are square integrable.
Source: Demailly, VI §2, weak-derivative Sobolev setup before (2.1), printed p.289;
the following compact-cutoff proof is supplied by the agent, not a numbered source assertion.
(blueprint: lem-sfb-schwartz-cutoff-l2-approximation)

Proof plan:
1. Choose a real smooth cutoff χ between zero and one, equal to one on the unit closed
ball and supported on the radius-two closed ball, using lem-sfb-euclidean-smooth-ball-bump.
Regard χ as complex. By lem-sfb-schwartz-test-inclusion-integrability it is Schwartz.
Iterating lem-sfb-schwartz-l2-coordinate-calculus makes each coordinate derivative of χ
bounded, and each derivative of ψ Schwartz and square integrable.
2. Set R_n = n + 1, χ_n(x) = χ(x / R_n), and ψ_n = χ_n ψ. Composition with dilation
and multiplication preserve smoothness. The support is closed in the compact dilation
of the support of χ, hence compact. The same two Schwartz lemmas give square
integrability of every derivative of every ψ_n.
3. Induction with the first-order chain and product rules gives
∂^γ χ_n(x) = R_n^(-|γ|) (∂^γ χ)(x / R_n) and
∂^β ψ_n = ∑_{γ ≤ β} binomial(β, γ) (∂^γ χ_n) ∂^(β-γ) ψ.
The induction differentiates either factor and combines coefficients with Pascal's identity;
smoothness allows coordinate derivatives to commute.
4. Subtract ∂^β ψ. The γ = 0 term is (χ_n - 1) ∂^β ψ, and each positive-order
term carries R_n^(-|γ|). For each fixed x, eventually χ_n equals one on a neighborhood
of x, so the entire derivative error vanishes. Its square is integrable because the two
derivatives are square integrable.
5. Bound the squared error by q times the sum of A_γ² |∂^(β-γ) ψ|², over γ ≤ β,
where q is the number of summands, A_0 = 1, and A_γ = binomial(β, γ) B_γ for γ > 0.
Here B_γ bounds ∂^γ χ, R_n ≥ 1, and |χ_n - 1| ≤ 1. The finite-sum square inequality
provides this bound. It is independent of n and integrable by
lem-sfb-schwartz-l2-coordinate-calculus. The squared errors are continuous and measurable.
6. Apply lem-sfb-real-dominated-integral-convergence to the squared errors and this bound.
Their integrals tend to zero, and taking square roots gives the asserted L² convergence.
The same sequence was chosen before β, so it works for every |β| ≤ s, including β = 0.
-/
theorem exists_compactlySupported_multiIndex_l2_approximation
    (m : ℕ) (hm : 1 ≤ m) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (s : ℕ) :
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin m) → ℂ,
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n)) ∧
      ∀ β : Fin m → ℕ, (∑ j, β j) ≤ s →
        MemLp (fun x ↦ iteratedFDeriv ℝ
          (List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.length ψ x
          (fun i ↦ EuclideanSpace.single
            ((List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.get i) 1)) 2 volume ∧
        (∀ n, MemLp (fun x ↦ iteratedFDeriv ℝ
          (List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.length (φ n) x
          (fun i ↦ EuclideanSpace.single
            ((List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.get i) 1)) 2 volume) ∧
        Tendsto (fun n ↦ Real.sqrt (∫ x,
          ‖iteratedFDeriv ℝ
          (List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.length (φ n) x
          (fun i ↦ EuclideanSpace.single
            ((List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.get i) 1) -
            iteratedFDeriv ℝ
          (List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.length ψ x
          (fun i ↦ EuclideanSpace.single
            ((List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.get i) 1)‖ ^ 2 ∂volume))
          atTop (𝓝 0) := by
  sorry

end SchwartzMap
