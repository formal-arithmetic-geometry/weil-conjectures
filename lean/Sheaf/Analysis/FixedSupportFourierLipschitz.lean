/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform bounds for fixed-support Fourier integrals

Source: Demailly, Differential and pseudodifferential operators on manifolds,
§2, Lemma 2.7, pp.5–6; first-spatial-moment specialization of the compact-support
Fourier equicontinuity argument (blueprint: lem-sfb-fixed-support-fourier-lipschitz).
-/

@[expose] public section

set_option autoImplicit false

universe w

open FourierTransform
open scoped RealInnerProductSpace

namespace MeasureTheory

/-- A square-integrable function supported almost everywhere in a fixed compact set has an
absolutely convergent, bounded, globally Lipschitz Fourier integral. The final clause gives
explicit common constants for every family with the same support and a common `L²` bound.
Here `MemLp u 2 volume` means Lebesgue measurability and finite squared-norm integral;
`Real.fourier_eq'` identifies `𝓕 u` with the displayed exponential integral.

Source: Demailly, Differential and pseudodifferential operators on manifolds, §2,
Lemma 2.7 proof, pp.5–6; agent first-moment specialization
(blueprint: lem-sfb-fixed-support-fourier-lipschitz).

Proof plan:
1. By `lem-sfb-continuous-on-compact-integrable`, the constant function and squared spatial
   norm are integrable on `K`. Apply `lem-sfb-real-l2-hilbert-pairing` to `1_K` and
   `1_K ‖u‖`: Cauchy–Schwarz bounds `∫ ‖u‖` by `sqrt (vol K) ‖u‖₂`, using the almost
   everywhere support condition, so `u` is integrable.
2. By `lem-sfb-complex-phase-exponential-bound`, the exponential phase has norm one.
   Its continuity makes its product with `u` almost everywhere strongly measurable.
   Apply `lem-sfb-integrable-majorant-estimate` with majorant `‖u‖` for absolute
   convergence and the first Fourier bound.
3. Apply scalar Cauchy–Schwarz from `lem-sfb-real-l2-hilbert-pairing` to `1_K ‖x‖`
   and `1_K ‖u‖`, obtaining the integrable first moment bounded by `b ‖u‖₂`.
   The phase identities and scalar phase estimate give a difference bound
   `2π ‖x‖ ‖ξ - η‖`; the Euclidean dot-product bound follows by expanding the
   nonnegative square of the orthogonal projection remainder (the zero-vector case
   is immediate). Use `lem-sfb-bochner-integral-subtraction` to subtract the integrals,
   then `lem-sfb-integrable-majorant-estimate` with the first-moment majorant.
4. The resulting Lipschitz estimate implies continuity. For a family bounded by `M`,
   replace each `L²` norm by `M` in both bounds; their constants depend only on `K` and `M`.
   No pointwise support condition is used. -/
theorem fixed_support_fourier_bounds_lipschitz
    (m : ℕ) (hm : 1 ≤ m) (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K)
    (u : EuclideanSpace ℝ (Fin m) → ℂ) (hu : MemLp u 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ K → u x = 0) :
    volume K ≠ ⊤ ∧
      IntegrableOn (fun x : EuclideanSpace ℝ (Fin m) ↦ ‖x‖ ^ 2) K volume ∧
      Integrable u volume ∧
      (∀ ξ : EuclideanSpace ℝ (Fin m),
        Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
          Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫) : ℂ) * Complex.I) * u x) volume) ∧
      (∀ ξ : EuclideanSpace ℝ (Fin m),
        ‖𝓕 u ξ‖ ≤ Real.sqrt (volume K).toReal * Real.sqrt (∫ x, ‖u x‖ ^ 2)) ∧
      (∀ ξ η : EuclideanSpace ℝ (Fin m),
        ‖𝓕 u ξ - 𝓕 u η‖ ≤
          2 * Real.pi * Real.sqrt (∫ x in K, ‖x‖ ^ 2) *
            Real.sqrt (∫ x, ‖u x‖ ^ 2) * ‖ξ - η‖) ∧
      Continuous (𝓕 u) ∧
      (∀ (I : Type w) (f : I → EuclideanSpace ℝ (Fin m) → ℂ) (M : NNReal),
        (∀ i : I, MemLp (f i) 2 volume) →
        (∀ i : I, ∀ᵐ x ∂volume, x ∉ K → f i x = 0) →
        (∀ i : I, Real.sqrt (∫ x, ‖f i x‖ ^ 2) ≤ M) →
        (∀ (i : I) (ξ : EuclideanSpace ℝ (Fin m)),
          ‖𝓕 (f i) ξ‖ ≤ Real.sqrt (volume K).toReal * M) ∧
        (∀ (i : I) (ξ η : EuclideanSpace ℝ (Fin m)),
          ‖𝓕 (f i) ξ - 𝓕 (f i) η‖ ≤
            2 * Real.pi * Real.sqrt (∫ x in K, ‖x‖ ^ 2) * M * ‖ξ - η‖)) := by
  sorry

end MeasureTheory
