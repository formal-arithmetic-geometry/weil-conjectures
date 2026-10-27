module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! # Frequency kernel of a compactly supported matrix symbol

Source: Demailly, Hodge AMS, Part I §3.B, Theorem 3.6, printed p.13 (PDF p.25),
and the agent-written Fourier-kernel argument in the DAG. The cited PDF is WANTED locally.
(blueprint: lem-sfb-compact-symbol-frequency-kernel)

The auxiliary definitions expand the coordinate derivatives and the two displayed integrals
of this assertion. Fourier transforms use Mathlib's normalization with phase `exp (-2πi x·ξ)`.
Matrices are continuous complex-linear maps between Euclidean spaces, with operator norm.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory FourierTransform Filter
open scoped ContDiff Topology

namespace EuclideanSpace

/-- The mixed coordinate derivative of a matrix symbol: first the frequency derivatives,
then the spatial derivatives, each in increasing coordinate order with multiplicities.
For smooth symbols these are the usual commuting mixed partial derivatives.
Source: Demailly, Hodge AMS I §3.B, Theorem 3.6, symbol estimates.
(blueprint: lem-sfb-compact-symbol-frequency-kernel) -/
noncomputable def symbolMultiIndexDeriv {m p q : ℕ} (α β : Fin m → ℕ)
    (b : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
  (List.ofFn (fun j : Fin m ↦ List.replicate (α j) j)).flatten.foldr
    (fun j g ↦ fun z ↦ fderiv ℝ (fun x ↦ g (x, z.2)) z.1 (EuclideanSpace.single j 1))
    ((List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.foldr
      (fun j g ↦ fun z ↦ fderiv ℝ (fun ζ ↦ g (z.1, ζ)) z.2 (EuclideanSpace.single j 1)) b)

/-- The absolutely convergent Fourier representation `T_b f`, before asserting convergence.
Source: Demailly, Hodge AMS I §3.B, Theorem 3.6, Fourier-kernel prerequisite.
(blueprint: lem-sfb-compact-symbol-frequency-kernel) -/
noncomputable def compactSymbolOperator {m p q : ℕ}
    (b : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℂ (Fin p)))
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℂ (Fin q) :=
  ∫ ξ, Complex.exp ((2 * (Real.pi : ℂ) * (inner ℝ x ξ : ℂ)) * Complex.I) •
    b (x, (2 * Real.pi) • ξ) (𝓕 f ξ)

/-- The actual regularized double integral defining the oscillatory quantization of `b`.
The product variable is `(y, ζ)`, the frequency cutoff is `χ (ζ/R)`, and the normalization
is exactly `(2π)^(-m)`. No unregularized double integral is used.
Source: Demailly, Hodge AMS I §3.B, Theorem 3.6, oscillatory-integral convention.
(blueprint: lem-sfb-compact-symbol-frequency-kernel) -/
noncomputable def cutoffSymbolOperator {m p q : ℕ}
    (b : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℂ (Fin p)))
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℂ (Fin q) :=
  (2 * (Real.pi : ℂ)) ^ (-(m : ℤ)) •
    ∫ z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      (χ (R⁻¹ • z.2) * Complex.exp ((inner ℝ (x - z.1) z.2 : ℂ) * Complex.I)) •
        b (x, z.2) (f z.1)

/-- A compactly supported symbol has a rapidly decreasing spatial Fourier transform,
its Schwartz-input operator has the stated frequency kernel, and every admissible cutoff
converges to that operator against every compactly supported smooth test.
Source: Demailly, Hodge AMS I §3.B, Theorem 3.6, printed p.13 (PDF p.25), and the
agent-written supporting Fourier argument in the DAG; source PDF WANTED locally.
(blueprint: lem-sfb-compact-symbol-frequency-kernel)

Proof plan:
1. Zero input or output rank gives the zero assertion. Otherwise work entrywise. Compact
spatial support makes each spatial derivative Schwartz by
lem-sfb-schwartz-test-inclusion-integrability. Iterate the coordinate derivative identity of
lem-sfb-schwartz-fourier-l2-identities. The Fourier integral of each derivative is bounded by
volume(K) times its symbol bound, by lem-sfb-integrable-majorant-estimate. For norm(theta) ≥ 1
choose a coordinate of size at least norm(theta)/sqrt(m), and divide by its L-th power.
For norm(theta) ≤ 1 use the undifferentiated bound. Maximize the finitely many constants and
use the sum of entry norms to bound the matrix operator norm. This includes L = 0.
2. By lem-sfb-schwartz-fourier-coordinate-rule the Fourier transform of f is Schwartz.
Its seminorms and lem-sfb-euclidean-bracket-integrable show that every polynomial weight times
its norm is integrable, with either sign of r. The symbol bounds at 2πξ and the unit-modulus
phase give absolute convergence by lem-sfb-integrable-majorant-estimate.
3. Every spatial derivative of the integrand is a finite sum of symbol derivatives times
frequency monomials and the same phase. Step 2 gives integrable bounds uniform in x.
Iterate lem-sfb-dominated-integral-frechet-derivative to get smoothness. The integral vanishes
outside K, which is closed, so its topological support is contained in K.
4. For each η the double kernel is bounded by a constant times the product of the indicator
of K and an integrable weighted Schwartz norm. Apply lem-sfb-product-fubini-integral-swap
and lem-sfb-integrable-majorant-estimate. Integrating in x gives the spatial Fourier transform
of b at (η-ξ,2πξ); evaluating the matrix integral on the vector gives the claimed identity.
5. With the frequency cutoff inserted, the (y,ζ) integral is absolutely convergent by the
same product criterion. Fubini in y gives the Fourier transform of f at ζ/(2π). Substitute
ζ = 2πξ using lem-sfb-euclidean-jacobian-integral. The Jacobian (2π)^m cancels the prefactor,
leaving the integrand of T_b f multiplied by χ(2πξ/R).
6. Against a compact smooth test φ, the product-integrable majorant is a constant times
|φ(x)| times the indicator of K times the weighted Schwartz norm. The bound is uniform in R
since χ is bounded. For fixed ξ, χ(2πξ/R) tends to one. Apply
lem-sfb-oscillatory-cutoff-convergence and Fubini to obtain the asserted limit of pairings.
Scalar complex tests and vector-valued integrals test every output coordinate, hence give
precisely the distributional equality. Empty K and L = 0 are included.
-/
theorem compactSymbol_frequencyKernel
    (m p q : ℕ) (hm : 1 ≤ m) (r : ℤ)
    (b : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hb : ContDiff ℝ ∞ b) (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K)
    (hsupp : ∀ x ζ : EuclideanSpace ℝ (Fin m), x ∉ K → b (x, ζ) = 0)
    (hest : ∀ α β : Fin m → ℕ, ∃ c : ℝ,
      ∀ x ζ : EuclideanSpace ℝ (Fin m),
        ‖symbolMultiIndexDeriv α β b (x, ζ)‖ ≤ c * (1 + ‖ζ‖) ^ (r - (∑ j, β j : ℕ))) :
    (∀ L : ℕ, ∃ C : ℝ, ∀ θ ζ : EuclideanSpace ℝ (Fin m),
      ‖𝓕 (fun x ↦ b (x, ζ)) θ‖ ≤
        C * (1 + ‖θ‖) ^ (-(L : ℤ)) * (1 + ‖ζ‖) ^ r) ∧
    ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℂ (Fin p)),
      (∀ x : EuclideanSpace ℝ (Fin m),
        Integrable (fun ξ ↦
          Complex.exp ((2 * (Real.pi : ℂ) * (inner ℝ x ξ : ℂ)) * Complex.I) •
            b (x, (2 * Real.pi) • ξ) (𝓕 f ξ)) volume) ∧
      ContDiff ℝ ∞ (compactSymbolOperator b f) ∧
      tsupport (compactSymbolOperator b f) ⊆ K ∧
      (∀ η : EuclideanSpace ℝ (Fin m),
        𝓕 (compactSymbolOperator b f) η =
          ∫ ξ, (𝓕 (fun x ↦ b (x, (2 * Real.pi) • ξ)) (η - ξ)) (𝓕 f ξ)) ∧
      (∀ χ : EuclideanSpace ℝ (Fin m) → ℂ,
        ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ᶠ ζ in 𝓝 0, χ ζ = 1) →
        ∀ φ : EuclideanSpace ℝ (Fin m) → ℂ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          Tendsto (fun R : ℝ ↦ ∫ x, φ x • cutoffSymbolOperator b f χ R x)
            atTop (𝓝 (∫ x, φ x • compactSymbolOperator b f x))) := by
  sorry

end EuclideanSpace
