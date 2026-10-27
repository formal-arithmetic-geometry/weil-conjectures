module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Fourier moments and the specified L² class

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, Sobolev lemma (2.1),
and the agent-written supporting Fourier argument recorded in the DAG
(blueprint: lem-sfb-fourier-moment-representative).
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory FourierTransform

namespace MeasureTheory.Lp

/-- Integrable Fourier moments give a `C^r` inverse integral representing the specified L² class.

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, (2.1), supporting
agent-written Fourier argument (blueprint: lem-sfb-fourier-moment-representative).
Here `𝓕 u` is Mathlib's continuous Plancherel extension from Schwartz functions, and
`𝓕⁻ h x` is the integral of `exp (2πi ⟪ξ,x⟫) * h ξ` by `Real.fourierInv_eq`.

Proof plan:
1. The zeroth moment makes `h` integrable. The phase has modulus one, so the inverse
integral converges absolutely at every point. Apply
[lem-sfb-bilinear-fourier-moment-regularity] (`VectorFourier.contDiff_fourierIntegral`)
with the negative inner product to obtain `C^r` regularity, including `r = 0`.
2. The canonical representative of `u` is locally integrable by
[lem-sfb-lp-local-integrability] (`MemLp.locallyIntegrable`). The continuous inverse
integral is locally integrable by [lem-sfb-continuous-local-integrability]
(`ContinuousOn.locallyIntegrableOn`) on the whole space.
3. For each real smooth compactly supported test, regard it as complex valued and apply
[lem-sfb-schwartz-test-inclusion-integrability] (`HasCompactSupport.toSchwartzMap` and
`SchwartzMap.integrable`). Apply [lem-sfb-l1-bilinear-fourier-duality]
(`VectorFourier.integral_fourierIntegral_smul_eq_flip`) to transpose the inverse integral.
Apply [lem-sfb-l2-inverse-fourier-test-duality]
(`Lp.fourierInv_toTemperedDistribution_eq` evaluated on the Schwartz test), and the
inverse law `Lp.instFourierPair`, to identify the same test integral with that of `u`.
Commutativity of complex multiplication identifies the two expressions.
4. The locally integrable difference of the inverse integral and the representative of `u`
therefore has zero pairing with every such test. Apply [lem-sfb-smooth-test-ae-separation]
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) on the whole space to conclude
almost-everywhere equality. Consequently the inverse integral is square integrable and
its L² class is the original `u`.
-/
theorem fourier_moments_inverse_representative
    (m : ℕ) (hm : 1 ≤ m)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (h : EuclideanSpace ℝ (Fin m) → ℂ) (hh : Measurable h)
    (hrep : ∀ᵐ ξ ∂volume,
      h ξ = (𝓕 u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m)))) ξ)
    (r : ℕ)
    (hmom : ∀ j : ℕ, j ≤ r → Integrable (fun ξ ↦ ‖ξ‖ ^ j * ‖h ξ‖) volume) :
    (∀ x : EuclideanSpace ℝ (Fin m),
      Integrable (fun ξ ↦ (Real.fourierChar (inner ℝ ξ x) : ℂ) * h ξ) volume) ∧
    ContDiff ℝ r (𝓕⁻ h) ∧
    (𝓕⁻ h =ᵐ[volume] (u : EuclideanSpace ℝ (Fin m) → ℂ)) := by
  sorry

end MeasureTheory.Lp
