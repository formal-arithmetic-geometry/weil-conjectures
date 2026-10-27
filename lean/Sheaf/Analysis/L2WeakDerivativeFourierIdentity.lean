module

public import Mathlib.Analysis.Fourier.LpSpace
public import Sheaf.Analysis.MultiIndexPartialDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Plancherel transform of an L² weak partial derivative

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, Sobolev lemma (2.1),
printed p.289, and the supporting agent-written Fourier argument recorded in the DAG.
(blueprint: lem-sfb-l2-weak-derivative-fourier-identity)

The coordinate derivative is imported and re-exported from its definition module. The Fourier
transform is Mathlib's continuous Plancherel extension from Schwartz functions. All test
pairings are bilinear complex products, without conjugation.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory FourierTransform
open scoped ContDiff

namespace MeasureTheory.Lp

/-- The Plancherel transform of an L² weak partial derivative is the corresponding
frequency monomial times the transform, for every measurable choice of representatives.
The unscaled frequency monomial times the representative is also square integrable.
Source: Demailly, VI §2, Sobolev lemma (2.1), printed p.289, supporting agent-written
Fourier prerequisite; Mathlib `Analysis/Fourier/LpSpace` and
`Analysis/Distribution/TemperedDistribution` supply the Fourier interfaces.
(blueprint: lem-sfb-l2-weak-derivative-fourier-identity)

Proof plan:
1. Let n = ∑ j, α j and c = 2πi. Extend the compact-test identity to Schwartz tests
using lem-sfb-schwartz-cutoff-l2-approximation at order n. The approximating functions
and their α derivatives converge in L². The bilinear L² product estimate
(lem-sfb-l2-product-integral-bound) bounds each pairing error by the fixed L² norm
of u or v times the corresponding error norm, so the identity passes to the limit.
2. Coordinate multiplication and differentiation preserve Schwartz functions by
lem-sfb-schwartz-l2-coordinate-calculus. Iterate lem-sfb-schwartz-fourier-coordinate-rule
in the helper's coordinate order to obtain ∂^α(𝓕 ψ) = 𝓕(q ψ), where
q(ξ) = (-c)^n ∏ j, ξ_j^(α j). Every intermediate polynomial times ψ is Schwartz;
no lower derivative of u is assumed.
3. By lem-sfb-l2-inverse-fourier-test-duality, apply inverse duality to 𝓕₂ a and
the Schwartz test 𝓕 ψ. The two inverse laws yield ∫ b ψ = ∫ a₀ (𝓕 ψ) for any
representatives a₀ of a and b of 𝓕₂ a. All products are integrable by
lem-sfb-schwartz-l2-coordinate-calculus and lem-sfb-l2-product-integral-bound.
4. Use this identity for (v,k) and for (u,h) with test q ψ. Steps 1 and 2 give
∫ k ψ = (-1)^n ∫ h q ψ = ∫ c^n (∏ j, ξ_j^(α j)) h ψ, since
(-1)^n (-c)^n = c^n. The bilinear convention introduces no conjugation or reflection.
5. Set w(ξ) = k(ξ) - c^n (∏ j, ξ_j^(α j)) h(ξ). Both representatives are locally
integrable by lem-sfb-lp-local-integrability. Polynomial multiplication preserves local
integrability, since the polynomial is bounded on a sufficiently small bounded
neighborhood. Thus w is locally integrable. Compact smooth real tests, embedded into
ℂ, are Schwartz by lem-sfb-schwartz-test-inclusion-integrability, so step 4 makes all
their pairings with w zero. Apply lem-sfb-smooth-test-ae-separation on the whole space
to conclude w = 0 almost everywhere.
6. Since c ≠ 0, the monomial times h equals c^(-n) k almost everywhere. Its squared
integral is |c|^(-2n) times that of k and is finite. This includes n = 0. Both
representatives were arbitrary throughout.
-/
theorem fourier_weak_multiIndex_derivative
    (m : ℕ) (hm : 1 ≤ m) (α : Fin m → ℕ)
    (u v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin m) → ℂ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, v x * φ x ∂volume) =
          (-1 : ℂ) ^ (∑ j, α j) *
            ∫ x, u x * EuclideanSpace.multiIndexPartialDeriv α φ x ∂volume)
    (h k : EuclideanSpace ℝ (Fin m) → ℂ) (hh : Measurable h) (hk : Measurable k)
    (hrep : h =ᵐ[volume]
      (𝓕 u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m)))))
    (krep : k =ᵐ[volume]
      (𝓕 v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))))) :
    (∀ᵐ ξ ∂volume,
      k ξ = (2 * (Real.pi : ℂ) * Complex.I) ^ (∑ j, α j) *
        (∏ j, (ξ j : ℂ) ^ (α j)) * h ξ) ∧
    MemLp (fun ξ ↦ (∏ j, (ξ j : ℂ) ^ (α j)) * h ξ) 2 volume := by
  sorry

end MeasureTheory.Lp
