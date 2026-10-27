module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Compact probability kernels approximate the identity in L²

Source: agent assembly from Mathlib's Bochner integration, Jacobian, Tonelli and L²
translation-continuity results, especially
`Mathlib/MeasureTheory/Function/LpSpace/DomAct/Continuous.lean`, lines 53–59
(blueprint: lem-sfb-l2-compact-kernel-approximation).
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

/-- Compactly supported probability kernels give L² contractions converging to the identity.
Source: the agent-assembled approximate-identity argument based on Mathlib's continuous
translation action, `LpSpace/DomAct/Continuous.lean`, lines 53–59
(blueprint: lem-sfb-l2-compact-kernel-approximation).

The rescaled kernel is `fun y ↦ ε⁻¹ ^ m * k (ε⁻¹ • y)`. The bilinear map in
`convolution` is scalar multiplication, so its value at `x` is exactly
`∫ y, (ε⁻¹ ^ m * k (ε⁻¹ • y)) • g (x - y)`. `MemLp` expresses Lebesgue
measurability and finite squared-norm integral. The existential family takes values in
Mathlib's quotient L² space, with its usual square-root-of-integral norm. Only positive
parameters are constrained; the right-hand limit uses `nhdsWithin 0 (Set.Ioi 0)`.

Proof plan:
1. By `lem-sfb-euclidean-bochner-integral-calculus`, choose Borel representatives of the
   kernel and vector function. Replace the kernel by its nonnegative part on the closed
   unit ball. The Jacobian formula of `lem-sfb-euclidean-jacobian-nonnegative-integrability`
   for the affine maps `y ↦ x - y` and `y ↦ ε⁻¹ • y` shows they preserve null sets.
   Thus these replacements preserve the integrability and integral of every section,
   and ultimately the resulting L² class, by the Bochner calculus node.
2. The same Jacobian formula for dilation shows that the rescaled kernel is integrable,
   nonnegative, supported in the radius-ε ball, and has integral one.
3. Apply `lem-sfb-tonelli-nonnegative-product` to
   `H(x) = ∫ y, k_ε(y) * ‖g(x-y)‖²`. The translation Jacobian is one, hence the
   integral of H is the squared L² norm of g. In particular H is finite almost everywhere.
4. At every such x, Cauchy–Schwarz from `lem-sfb-real-l2-hilbert-pairing` applied to
   `sqrt(k_ε)` and `sqrt(k_ε) * ‖g(x-·)‖` bounds the norm integral by `sqrt(H(x))`.
   The Bochner norm criterion proves section integrability, and the integral norm bound
   gives `‖A_ε g(x)‖² ≤ H(x)`.
5. Parameter-integral measurability from the Bochner calculus node makes the convolution
   measurable. Integrating the last inequality with Tonelli proves L² membership and
   the contraction bound, giving the displayed quotient classes.
6. Bochner linearity and normalization express `A_ε g - g` as the average of
   `g(x-y)-g(x)`. Tonelli bounds the integral of the corresponding squared-norm average
   by `4 * ‖g‖₂²`. Cauchy–Schwarz and the Bochner norm estimate then give
   `‖A_ε g-g‖₂² ≤ ∫ y, k_ε(y) * ‖T_y g-g‖₂²`.
7. Given η > 0, `lem-sfb-l2-translation-continuity` gives δ > 0 for which the translation
   difference norm is below η/2 when ‖y‖ < δ. For 0 < ε < δ the kernel is supported
   there, so Tonelli monotonicity bounds the last integral by `(η/2)²`. This proves
   the right-hand limit. Step 1 proves independence of both representatives.
-/
theorem l2_compact_kernel_approximation
    (m r : ℕ) (hm : 1 ≤ m)
    (k : EuclideanSpace ℝ (Fin m) → ℝ)
    (hk : Integrable k volume)
    (hk_nonneg : ∀ᵐ y ∂volume, 0 ≤ k y)
    (hk_integral : ∫ y, k y ∂volume = 1)
    (hk_support : ∀ᵐ y ∂volume, y ∉ Metric.closedBall 0 1 → k y = 0)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r))
    (hg : MemLp g 2 volume) :
    ∃ A : ℝ → Lp (EuclideanSpace ℝ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin m))),
      (∀ ε : ℝ, 0 < ε →
        (∀ᵐ x ∂volume, ConvolutionExistsAt
          (fun y ↦ ε⁻¹ ^ m * k (ε⁻¹ • y)) g x (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧
        (A ε : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r)) =ᵐ[volume]
          convolution (fun y ↦ ε⁻¹ ^ m * k (ε⁻¹ • y)) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume ∧
        ‖A ε‖ ≤ ‖hg.toLp g‖) ∧
      Tendsto (fun ε : ℝ ↦ ‖A ε - hg.toLp g‖)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) ∧
      (∀ (k' : EuclideanSpace ℝ (Fin m) → ℝ)
          (g' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r)),
        k' =ᵐ[volume] k → g' =ᵐ[volume] g → ∀ ε : ℝ, 0 < ε →
          convolution (fun y ↦ ε⁻¹ ^ m * k' (ε⁻¹ • y)) g'
            (ContinuousLinearMap.lsmul ℝ ℝ) volume =ᵐ[volume]
          (A ε : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r))) := by
  sorry

end MeasureTheory
