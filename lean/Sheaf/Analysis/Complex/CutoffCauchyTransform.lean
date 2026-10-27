module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # The cutoff Cauchy transform with smooth real parameters

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A, Corollary (3.4),
and I §8, Exercise 8.5. (blueprint: lem-sfb-cauchy-transform-parameters)

The input functions are ambient representatives of functions on the open product domain.
The integrand discards their values outside the disk. Parameter derivatives are taken
within the open parameter domain, in coordinate order, with the prescribed multiplicities.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace Complex

/-- The zero-extended cutoff Cauchy integrand. Complex division gives value zero at
the singular point. Source: Demailly I §3.A, (3.2), and I §8, Exercise 8.5.
(blueprint: lem-sfb-cauchy-transform-parameters) -/
noncomputable def cutoffCauchyIntegrand (m : ℕ) (c : ℂ) (R : ℝ) (χ : ℂ → ℝ)
    (h : ℂ × (Fin m → ℝ) → ℂ) (z : ℂ) (t : Fin m → ℝ) (ζ : ℂ) : ℂ := by
  classical
  exact if ζ ∈ Metric.ball c R then (χ ζ : ℂ) * h (ζ, t) / (z - ζ) else 0

/-- The integral defining the cutoff Cauchy transform, with planar Lebesgue measure.
Source: Demailly I §3.A, Corollary (3.4), and I §8, Exercise 8.5.
(blueprint: lem-sfb-cauchy-transform-parameters) -/
noncomputable def cutoffCauchyTransform (m : ℕ) (c : ℂ) (R : ℝ) (χ : ℂ → ℝ)
    (h : ℂ × (Fin m → ℝ) → ℂ) (q : ℂ × (Fin m → ℝ)) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ ζ : ℂ, cutoffCauchyIntegrand m c R χ h q.1 q.2 ζ

/-- The parameter multi-index derivative used in the cutoff Cauchy identity.
For each coordinate `j`, repeat its real partial derivative `ν j` times; order the
coordinates increasingly. Within an open set these are the usual real derivatives.
Source: Demailly I §8, Exercise 8.5, parameter derivatives of partial convolution.
(blueprint: lem-sfb-cauchy-transform-parameters) -/
noncomputable def cutoffCauchyParameterDeriv (m : ℕ) (P : Set (Fin m → ℝ))
    (ν : Fin m → ℕ) (h : ℂ × (Fin m → ℝ) → ℂ) : ℂ × (Fin m → ℝ) → ℂ :=
  (List.ofFn (fun j : Fin m ↦ List.replicate (ν j) j)).flatten.foldr
    (fun j g ↦ fun q ↦
      fderivWithin ℝ (fun s ↦ g (q.1, s)) P q.2 (Pi.single j 1)) h

/-- A cutoff depending only on the two concentric disks gives an absolutely convergent,
jointly real-smooth, complex-linear Cauchy transform, solves the inhomogeneous
antiholomorphic derivative equation, and commutes with every parameter derivative.
Source: Demailly I §3.A, Corollary (3.4), printed p.21, and I §8, Exercise 8.5,
printed p.61. (blueprint: lem-sfb-cauchy-transform-parameters)

Proof: Choose `r < a < b < R` and a real smooth ball bump with inner radius `a`
and outer radius `b` (lem-sfb-euclidean-smooth-ball-bump). Its support is compact
in the larger disk and it equals one near the closure of the smaller disk.
The zero extension of the product with `h` is smooth, vanishes outside the fixed
compact closed `b`-ball, and so do all its derivatives. Parameter differentiation
commutes with this extension because the cutoff is independent of the parameters.
The kernel `1 / (π w)` is locally integrable by lem-sfb-cauchy-green-test-function.
Apply lem-sfb-locally-integrable-parametric-convolution to obtain convergence and
joint smoothness; the substitution `ζ = z - w` preserves planar measure and gives
the displayed transform. Differentiate in the real directions `1` and `I`, and
combine with coefficients `1/2` and `I/2`. The Cauchy--Green test-function identity
identifies the result with the cutoff product. Iterate the parameter-direction
formula, using the same compact support at each step, to obtain every multi-index
identity. Linearity follows from the linearity of the absolutely convergent integral.
Finally the cutoff is one on the smaller disk. This includes `m = 0`.
-/
theorem exists_cutoffCauchyTransform_parameters (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ℂ → ℝ,
      ContDiff ℝ ∞ χ ∧
      (∃ U : Set ℂ, IsOpen U ∧ closure (Metric.ball c r) ⊆ U ∧
        ∀ z ∈ U, χ z = 1) ∧
      IsCompact (tsupport χ) ∧ tsupport χ ⊆ Metric.ball c R ∧
      ∀ (m : ℕ) (P : Set (Fin m → ℝ)), IsOpen P →
        ∀ h : ℂ × (Fin m → ℝ) → ℂ,
          ContDiffOn ℝ ∞ h (Metric.ball c R ×ˢ P) →
          (∀ (z : ℂ) (t : Fin m → ℝ), t ∈ P →
            Integrable (cutoffCauchyIntegrand m c R χ h z t) volume) ∧
          ContDiffOn ℝ ∞ (cutoffCauchyTransform m c R χ h) (Set.univ ×ˢ P) ∧
          (∀ (z : ℂ) (t : Fin m → ℝ), z ∈ Metric.ball c R → t ∈ P →
            (fderiv ℝ (fun w ↦ cutoffCauchyTransform m c R χ h (w, t)) z 1 +
              I * fderiv ℝ (fun w ↦ cutoffCauchyTransform m c R χ h (w, t)) z I) / 2 =
              (χ z : ℂ) * h (z, t)) ∧
          (∀ (ν : Fin m → ℕ) (z : ℂ) (t : Fin m → ℝ), t ∈ P →
            cutoffCauchyParameterDeriv m P ν (cutoffCauchyTransform m c R χ h) (z, t) =
              cutoffCauchyTransform m c R χ (cutoffCauchyParameterDeriv m P ν h) (z, t)) ∧
          (∀ (z : ℂ) (t : Fin m → ℝ), z ∈ Metric.ball c r → t ∈ P →
            (fderiv ℝ (fun w ↦ cutoffCauchyTransform m c R χ h (w, t)) z 1 +
              I * fderiv ℝ (fun w ↦ cutoffCauchyTransform m c R χ h (w, t)) z I) / 2 =
              h (z, t)) ∧
          (∀ g : ℂ × (Fin m → ℝ) → ℂ,
            ContDiffOn ℝ ∞ g (Metric.ball c R ×ˢ P) →
            ∀ (α β : ℂ) (z : ℂ) (t : Fin m → ℝ), t ∈ P →
              cutoffCauchyTransform m c R χ (fun q ↦ α * h q + β * g q) (z, t) =
                α * cutoffCauchyTransform m c R χ h (z, t) +
                  β * cutoffCauchyTransform m c R χ g (z, t)) := by
  sorry

end Complex
