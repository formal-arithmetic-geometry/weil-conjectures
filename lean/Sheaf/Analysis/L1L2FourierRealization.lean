/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Integral realization of the Plancherel transform

Source: Demailly, Differential and pseudodifferential operators on manifolds, §2, p.3,
Fourier transform and the order-zero case of (2.1); Lemma 2.7, p.5.
The `L¹`/`L²` compatibility is an explicit supporting input to the fixed-support argument
(blueprint: lem-sfb-l1-l2-fourier-realization).
-/

@[expose] public section

set_option autoImplicit false

open FourierTransform
open scoped RealInnerProductSpace

namespace MeasureTheory

/-- The Schwartz Fourier integral extends isometrically to `L²`, and its integral on any
integrable representative of an `L²` class represents that extended transform almost everywhere.
The Fourier transform of functions uses the kernel `exp (-2πi ⟪x, ξ⟫)`.

Source: Demailly, Differential and pseudodifferential operators on manifolds, §2, p.3,
Fourier transform and (2.1) at order zero; Lemma 2.7, p.5
(blueprint: lem-sfb-l1-l2-fourier-realization).

Proof plan:
1. Use `Lp.fourierTransformₗᵢ` and `SchwartzMap.toLp_fourier_eq`, the extension clauses of
   `lem-sfb-l2-fourier-isometry-test-duality`. Linearity and isometry give the distance identity.
2. For an integrable representative `u₀`, the exponential has norm one, so its Fourier
   integrand is absolutely integrable at every frequency. The order-zero case of
   `lem-sfb-bilinear-fourier-moment-regularity` makes its Fourier integral continuous.
   By `lem-sfb-continuous-local-integrability` it is locally integrable; an `L²`
   representative of the extended transform is locally integrable by
   `lem-sfb-lp-local-integrability`.
3. Complexify a real smooth compactly supported test function. By
   `lem-sfb-schwartz-test-inclusion-integrability` it is Schwartz and integrable. Apply
   `lem-sfb-l1-bilinear-fourier-duality` to `u₀` and this test. The distribution identity
   of `lem-sfb-l2-fourier-isometry-test-duality`, evaluated on the same test, gives the
   identical integral against the extended `L²` transform. Commute complex products.
4. The difference of the two representatives is locally integrable and has zero integral
   against every real smooth compactly supported test. The products are integrable by
   boundedness of the test and a finite neighborhood cover of its compact support.
   Apply `lem-sfb-smooth-test-ae-separation` on the whole Euclidean space. The resulting
   almost-everywhere equality also proves square integrability of the Fourier integral. -/
theorem exists_l1_l2_fourier_realization (m : ℕ) (hm : 1 ≤ m) :
    ∃ F₂ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))),
      (∀ φ : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ,
        F₂ (φ.toLp 2) = (𝓕 φ).toLp 2) ∧
      (∀ u v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))),
        ‖F₂ u - F₂ v‖ = ‖u - v‖) ∧
      (∀ (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m))))
        (u₀ : EuclideanSpace ℝ (Fin m) → ℂ),
        u₀ =ᵐ[volume] (u : EuclideanSpace ℝ (Fin m) → ℂ) → Integrable u₀ volume →
          (∀ ξ : EuclideanSpace ℝ (Fin m),
            Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
              Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫) : ℂ) * Complex.I) * u₀ x) volume) ∧
          (𝓕 u₀ =ᵐ[volume] (F₂ u : EuclideanSpace ℝ (Fin m) → ℂ)) ∧
          MemLp (𝓕 u₀) 2 volume) := by
  sorry

end MeasureTheory
