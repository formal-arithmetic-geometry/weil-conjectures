/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionSmallLog
import Sheaf.RingTheory.PowerSeries.ExpSubstHom
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.RingTheory.NonarchimedeanSeriesSubstitution
import Sheaf.RingTheory.PowerSeries.LogExpFormalIdentities
import Sheaf.SecPurityRealSheaves.LogExpValuationConvergence

/-!
# Logarithm and exponential on deep principal units

Source: blueprint main-20261015, sec-purity-real-sheaves, sk-d-real-log,
`lem-wf-deep-principal-unit-log` and its proof (blueprint: lem-wf-deep-principal-unit-log).

The normalized valuation of the prime is specified by its unit-times-uniformizer-power
expression. The ideal is taken in the recorded integer ring. Its elements are coerced to
`E`, and every convergence and continuity assertion uses the extended spectral topology.
The existing small-log series is used at every depth where it converges; its argument is
`x`, so it denotes `log (1 + x)`. The exponential is characterized by its convergent series.
-/

@[expose] public section

universe u

namespace Padic

/-- Logarithm and exponential are inverse continuous homomorphisms between `1 + 𝔪^r`
and `𝔪^r` when `r > e / (ℓ - 1)`. The decomposition hypothesis specifies precisely
`e = v_E(ℓ)` for the normalization `v_E(ϖ) = 1`; it chooses no extra structure.
The last clause gives one positive exponent working for every integral unit.

Source: blueprint main-20261015, sec-purity-real-sheaves, sk-d-real-log,
`lem-wf-deep-principal-unit-log`, statement and proof paragraphs 1–3
(blueprint: lem-wf-deep-principal-unit-log).

Proof:
1. Put `I = 𝔪^r`, `q = ℓ^(-r/e)` and `δ = r - e/(ℓ-1) > 0`.
The valuation-convergence lemma bounds the weighted coefficients of the logarithm `L`
and positive-degree exponential `A` by `q θ^(n-1)`, where `θ = ℓ^(-δ/e) < 1`.
Thus both series converge uniformly on `I`, continuously, with sums in `I`.
2. Apply the nonarchimedean-series-substitution lemma with radii `q,q` to `(L,A)`
and `(A,L)`. Their zero constant coefficients, coefficient bounds and decay make
both expanded composition families summable. Evaluate the formal inverse identities
of the log-exp-formal-identities lemma to obtain `L(A(x)) = x` and `A(L(x)) = x`.
3. Apply `PowerSeries.exp_subst_hom` to `aT,bT`. The same coefficient estimates make
all three exponential series restricted at radius one. The Cauchy-product clause
of nonarchimedean-series-substitution evaluates at `T = 1`, giving exponential
additivity for all `a,b ∈ I`.
4. The inverse identities give bijections between `I` and `1+I`. The exponential
at zero is one, and additivity at `a,-a` shows its values are units. Inverting this
homomorphism gives logarithm additivity. The uniform-convergence continuity and
translation by one give both continuous homomorphisms.
5. The coefficient-extension DVR theorem gives a finite residue field and
`𝔪^r = (ϖ^r)`. The valued-DVR finite-quotients lemma makes `𝒪/𝔪^r` finite.
Reduction on integral units has kernel `1+𝔪^r`; the exponent of its finite image
is one positive integer `N` placing every integral unit power in this kernel. -/
theorem deepPrincipalUnit_log_exp (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (e : ℕ)
    (_he : ∃ u : (coefficientExtensionIntegers ℓ E)ˣ,
      (ℓ : E) = ((u : coefficientExtensionIntegers ℓ E) : E) *
        (coefficientExtensionUniformizer ℓ E : E) ^ e)
    (r : ℤ) (_hr : (e : ℚ) / ((ℓ : ℚ) - 1) < (r : ℚ)) :
    ∃ exp : E → E,
      (∀ x : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
        @HasSum E ℕ _ (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
          (fun n : ℕ ↦ (-1 : E) ^ n * (x : E) ^ (n + 1) / (n + 1 : ℕ))
          (coefficientExtensionSmallLog ℓ E (x : E)) (SummationFilter.unconditional ℕ) ∧
        @HasSum E ℕ _ (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
          (fun n : ℕ ↦ (x : E) ^ n / (Nat.factorial n : E)) (exp (x : E))
          (SummationFilter.unconditional ℕ)) ∧
      @ContinuousOn E E
        (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
        (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
        (coefficientExtensionSmallLog ℓ E)
        (Set.range (fun x : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat) ↦ (x : E))) ∧
      @ContinuousOn E E
        (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
        (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace exp
        (Set.range (fun x : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat) ↦ (x : E))) ∧
      (∀ x : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
        (∃ y : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
          coefficientExtensionSmallLog ℓ E (x : E) = (y : E)) ∧
        exp (coefficientExtensionSmallLog ℓ E (x : E)) = 1 + (x : E)) ∧
      (∀ x : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
        (∃ y : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
          exp (x : E) = 1 + (y : E)) ∧
        coefficientExtensionSmallLog ℓ E (exp (x : E) - 1) = (x : E)) ∧
      (∀ x y : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
        coefficientExtensionSmallLog ℓ E ((1 + (x : E)) * (1 + (y : E)) - 1) =
          coefficientExtensionSmallLog ℓ E (x : E) +
            coefficientExtensionSmallLog ℓ E (y : E)) ∧
      (∀ x y : ↥((coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat),
        exp ((x : E) + (y : E)) = exp (x : E) * exp (y : E)) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ u : (coefficientExtensionIntegers ℓ E)ˣ,
        (u : coefficientExtensionIntegers ℓ E) ^ N - 1 ∈
          (coefficientExtensionMaximalIdeal ℓ E) ^ r.toNat := by
  sorry

end Padic
