module

public import Sheaf.Geometry.Manifold.KahlerCoordinateData
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Local complex Hessian forms

Source: Demailly, Complex Analytic and Differential Geometry, I §3.C, (3.13)–(3.19),
printed pp.23–25; V §13; VI §4, Example (4.4), printed p.297
(blueprint: lem-sfb-local-ddbar-potential-calculus).

The coordinate wedge and normalized complex Hessian below are actual continuous alternating
maps on real tangent vectors. All comparisons are restricted to the specified open domains.
The Wirtinger operators are the existing operators of `KahlerCoordinateData`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace ComplexManifold

/-- The constant coordinate two-form `dz_r ∧ dbar_z_s`, obtained by alternating the product
of coordinate evaluation and conjugate coordinate evaluation. There is no factorial divisor
in degree two: its value on `(v,w)` is `v_r conj(w_s) - w_r conj(v_s)`.
Source: Demailly I §3.C, (3.13)–(3.15)
(blueprint: lem-sfb-local-ddbar-potential-calculus). -/
def ddbarCoordinateWedge {d : ℕ} (r s : Fin d) :
    ContinuousAlternatingMap ℝ (Model d) ℂ (Fin 2) :=
  ContinuousMultilinearMap.alternatization
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ 2 ℂ).compContinuousLinearMap
      ![(ContinuousLinearMap.proj r : Model d →L[ℂ] ℂ).restrictScalars ℝ,
        Complex.conjCLE.toContinuousLinearMap.comp
          ((ContinuousLinearMap.proj s : Model d →L[ℂ] ℂ).restrictScalars ℝ)])

/-- The normalized complex Hessian `D_U φ = (i / (2π)) ∂ bar∂ φ`.
The real potential is included into the complex numbers before applying the existing
Wirtinger derivatives. Source: Demailly I §3.C, (3.13)–(3.19), and VI §4, (4.4)
(blueprint: lem-sfb-local-ddbar-potential-calculus). -/
def ddbarPotential {d : ℕ} (U : Set (Model d)) (φ : Model d → ℝ)
    (z : Model d) : ContinuousAlternatingMap ℝ (Model d) ℂ (Fin 2) :=
  ∑ r : Fin d, ∑ s : Fin d,
    (Complex.I / (2 * (Real.pi : ℂ)) *
      wirtingerPartial (wirtingerBarPartial (fun w ↦ (φ w : ℂ)) U s) U r z) •
        ddbarCoordinateWedge r s

/-- The local complex Hessian is smooth, real, closed, of type `(1,1)`, and real-linear;
it commutes with holomorphic pullback and vanishes on the logarithm of the squared modulus
of a holomorphic unit. Holomorphic coordinate functions mean locally convergent complex
power series, expressed by `AnalyticOnNhd ℂ`.

Source: Demailly I §3.C, (3.13)–(3.19), printed pp.23–25; V §13, change of frame for
line-bundle curvature; VI §4, Example (4.4), printed p.297
(blueprint: lem-sfb-local-ddbar-potential-calculus).

Proof plan:
1. Apply smooth real differentiation and second-derivative symmetry
   (`lem-sfb-real-smooth-differentiation`, `lem-sfb-real-second-derivative-symmetry`) to
   commute the constant linear combinations defining Wirtinger derivatives. Conjugation
   exchanges the two operators by the real chain rule.
2. The mixed Hessian coefficients satisfy `conj H_rs = H_sr`. Conjugating the factor `i`
   and reversing the wedge factors gives reality. The coefficients are smooth, the displayed
   sum has type `(1,1)`, and real-linearity follows from linearity of differentiation.
3. Expand the real exterior derivative in the complex coordinate basis. Symmetry in the
   two holomorphic indices cancels the first part against alternatingness; symmetry in the
   two antiholomorphic indices cancels the second part. Thus the form is closed.
4. By `lem-sfb-analytic-real-smooth`, a holomorphic map is real smooth and its real
   differential is complex-linear. Its barred Wirtinger derivatives vanish. Its unbarred
   derivatives remain holomorphic by `lem-sfb-complex-analytic-derivative-rules` and
   `lem-sfb-complex-analytic-function-operations`, applied componentwise to the finite tuple.
5. Twice apply the real chain rule: the mixed Hessian of the composite has coefficients
   `sum r,s, H_rs(F) F_(r,a) conj(F_(s,b))`. Pulling back the two coordinate covectors by
   the real differential gives precisely these coefficients, establishing naturality.
6. For a holomorphic unit put `q = |h|² > 0`. Smoothness follows from real smoothness,
   polynomial operations, and smoothness of the real logarithm on positive numbers.
   The product and chain rules give `∂z_r log q = (∂z_r h) / h` without choosing a logarithm.
7. The quotient is holomorphic by the analytic derivative and inverse rules, so its barred
   derivatives vanish. Commuting mixed derivatives of the smooth logarithm shows that every
   Hessian coefficient is zero. Empty domains and empty coordinate sums require no exceptions.
-/
theorem local_ddbar_potential_calculus
    (d : ℕ) (U : Set (Model d)) (hU : IsOpen U)
    (φ : Model d → ℝ) (hφ : ContDiffOn ℝ ∞ φ U) :
    ContDiffOn ℝ ∞ (ddbarPotential U φ) U ∧
    (∀ z ∈ U, ∀ v : Fin 2 → Model d,
      star (ddbarPotential U φ z v) = ddbarPotential U φ z v) ∧
    (∀ z ∈ U, extDerivWithin (ddbarPotential U φ) U z = 0) ∧
    (∃ H : Model d → Fin d → Fin d → ℂ,
      ∀ z ∈ U, ddbarPotential U φ z =
        ∑ r : Fin d, ∑ s : Fin d, H z r s • ddbarCoordinateWedge r s) ∧
    (∀ (ψ : Model d → ℝ), ContDiffOn ℝ ∞ ψ U → ∀ a b : ℝ,
      Set.EqOn (ddbarPotential U (fun z ↦ a * φ z + b * ψ z))
        (fun z ↦ a • ddbarPotential U φ z + b • ddbarPotential U ψ z) U) ∧
    (∀ (e : ℕ) (V : Set (Model e)), IsOpen V → ∀ F : Model e → Model d,
      Set.MapsTo F V U → (∀ r : Fin d, AnalyticOnNhd ℂ (fun z ↦ F z r) V) →
      ContDiffOn ℝ ∞ (φ ∘ F) V ∧
      Set.EqOn
        (fun z ↦ (ddbarPotential U φ (F z)).compContinuousLinearMap (fderivWithin ℝ F V z))
        (ddbarPotential V (φ ∘ F)) V) ∧
    (∀ h : Model d → ℂ, AnalyticOnNhd ℂ h U → (∀ z ∈ U, h z ≠ 0) →
      ContDiffOn ℝ ∞ (fun z ↦ Real.log (‖h z‖ ^ 2)) U ∧
      Set.EqOn (ddbarPotential U (fun z ↦ Real.log (‖h z‖ ^ 2))) 0 U) := by
  sorry

end ComplexManifold
