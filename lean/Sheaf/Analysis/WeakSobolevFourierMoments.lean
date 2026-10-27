module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Data.List.FinRange
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Fourier moments from square-integrable weak derivatives

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, Sobolev lemma (2.1),
printed p.289. This is the agent-stated Euclidean Fourier input to that lemma.
(blueprint: lem-sfb-weak-sobolev-fourier-moments)
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform ContDiff

namespace Real

/-- Square-integrable weak partial derivatives through order `t` give all integrable Fourier
moments through order `r`, when `t > r + m / 2`, for every measurable Fourier representative.

The folded expression differentiates `α i` times in the `i`-th standard coordinate direction,
in increasing coordinate order. For smooth tests this is precisely the multi-index derivative.
The complex test pairing is bilinear, with no conjugation.

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, (2.1), printed p.289;
agent-stated supporting lemma (blueprint: lem-sfb-weak-sobolev-fourier-moments).

Proof plan: apply lem-sfb-l2-weak-derivative-fourier-identity to each derivative with multi-index
`t eᵢ`, giving square integrability of `ξᵢ ^ t` times the Fourier transform `h`. Put
`w = 1 + ‖ξ‖ ^ 2` and `M = max (1, |ξ₁|², ..., |ξₘ|²)`. The inequalities
`w ≤ (m + 1) M` and `M ^ t ≤ 1 + ∑ i, |ξᵢ| ^ (2 * t)` imply square integrability of
`a = w ^ (t / 2) |h|`. For `j ≤ r`, put `s = t - j > m / 2`.
The lemma lem-sfb-euclidean-bracket-integrable gives integrability of `w ^ (-s)`.
Since `b = ‖ξ‖ ^ j * w ^ (-t / 2)` satisfies `b² ≤ w ^ (-s)`, it is square-integrable.
Apply lem-sfb-l2-product-integrable to `a,b`: their product is `‖ξ‖ ^ j * |h|`.
Finally, replacing `h` on a null set changes this integrand only on a null set, so its
nonnegative integral and integrability are independent of the measurable representative. -/
theorem integrable_fourier_moments_of_weak_derivatives
    {m : ℕ} (hm : 1 ≤ m) (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (t r : ℕ) (htr : (r : ℝ) + (m : ℝ) / 2 < (t : ℝ))
    (hweak : ∀ α : Fin m → ℕ, (∑ i, α i) ≤ t →
      ∃ v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))),
        ∀ φ : EuclideanSpace ℝ (Fin m) → ℂ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ x, v x * φ x) = (-1 : ℂ) ^ (∑ i, α i) *
            ∫ x, u x * ((List.finRange m).foldr
              (fun i f ↦ (fun g y ↦ fderiv ℝ g y (EuclideanSpace.single i 1))^[α i] f)
              φ) x) :
    ∀ h : EuclideanSpace ℝ (Fin m) → ℂ, Measurable h →
      h =ᵐ[volume] (𝓕 u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m)))) →
      ∀ j : ℕ, j ≤ r → Integrable (fun ξ ↦ ‖ξ‖ ^ j * ‖h ξ‖) volume := by
  sorry

end Real
