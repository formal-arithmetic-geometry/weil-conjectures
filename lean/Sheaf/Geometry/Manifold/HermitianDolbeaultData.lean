module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Smooth Hermitian Dolbeault data in holomorphic coordinates

Source: Kong, Notes on Complex Geometry, §§3.1, 6.1 and 6.2
(blueprint: def-sfb-hermitian-dolbeault-data).

Tangent vectors use the chart at their base point. Other charts act by the derivative of
transition maps. Smooth forms are spans of smooth coefficient fields; the generating sets
are already complex vector spaces. Types are the eigenspaces of the action of the complex
structure on covariant alternating tensors. Volume and the L² pairing use the real part of
the Hermitian metric, its determinant, and the inverse metric on alternating tensors.
Operators are specified by their coordinate exterior derivative and formal adjoint identities.
-/

@[expose] public section

noncomputable section

universe u

open scoped Manifold ContDiff
open MeasureTheory

namespace ComplexManifold

/-- Coordinate tangent model. Source: Kong §3.1
(blueprint: def-sfb-hermitian-dolbeault-data). -/
abbrev Model (n : ℕ) := Fin n → ℂ

/-- Complex-valued real alternating tensor fields, with all exterior degrees recorded.
Source: Kong §3.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
abbrev FormFields (n : ℕ) (M : Type u) :=
  ∀ k : ℕ, M → ContinuousAlternatingMap ℝ (Model n) ℂ (Fin k)

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]

/-- The tangent coordinate change from a chart to the chart at the base point.
Source: Kong §3.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def chartTangent (e : OpenPartialHomeomorph M (Model n)) (z : Model n) :
    Model n →L[ℂ] Model n :=
  fderiv ℂ (fun w ↦ chartAt (Model n) (e.symm z) (e.symm w)) z

/-- Coefficients in an arbitrary holomorphic chart, obtained by tensor pullback.
Source: Kong §3.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def formCoordinates (α : FormFields n M) (k : ℕ)
    (e : OpenPartialHomeomorph M (Model n)) (z : Model n) :
    ContinuousAlternatingMap ℝ (Model n) ℂ (Fin k) :=
  (α k (e.symm z)).compContinuousLinearMap ((chartTangent e z).restrictScalars ℝ)

/-- Smooth complex differential forms, constructed from smooth local coefficients.
The generating set is closed under addition and complex scaling, so its span introduces
no additional fields. Source: Kong §3.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def smoothForms : Submodule ℂ (FormFields n M) :=
  Submodule.span ℂ {α | ∀ (k : ℕ) (e : OpenPartialHomeomorph M (Model n)),
    e ∈ atlas (Model n) M → ContDiffOn ℝ ∞ (formCoordinates α k e) e.target}

/-- Smooth forms of integer bidegree `(p,q)`. A covariant tensor of degree `p+q` has
this type exactly when the sum of insertions of `J` has eigenvalue `i(p-q)`.
Invalid types give the zero subspace. Source: Kong §3.1
(blueprint: def-sfb-hermitian-dolbeault-data). -/
def typeForms (p q : ℤ) : Submodule ℂ (smoothForms (n := n) (M := M)) :=
  if 0 ≤ p ∧ p ≤ n ∧ 0 ≤ q ∧ q ≤ n then
    Submodule.span ℂ {α | (∀ k : ℕ, k ≠ (p + q).toNat → α.val k = 0) ∧
      ∀ (x : M) (v : Fin (p + q).toNat → Model n),
        (∑ j : Fin (p + q).toNat,
          α.val (p + q).toNat x (Function.update v j (Complex.I • v j))) =
        ((p - q : ℤ) : ℂ) * Complex.I * α.val (p + q).toNat x v}
  else ⊥

/-- The real coordinate basis `(∂/∂x_j, ∂/∂y_j)` of complex tangent space.
Source: Kong §3.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def realCoordinateVector (j : Fin n × Bool) : Model n :=
  Pi.single j.1 (if j.2 then Complex.I else 1)

/-- A Hermitian matrix evaluated on two tangent vectors, conjugate linear in the first.
Source: Kong §6.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def metricPair (h : M → Matrix (Fin n) (Fin n) ℂ) (x : M) (v w : Model n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, star (v i) * h x i j * w j

/-- Real Gram matrix of a Hermitian metric in a holomorphic chart.
Source: Kong §6.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def chartGram (h : M → Matrix (Fin n) (Fin n) ℂ)
    (e : OpenPartialHomeomorph M (Model n)) (z : Model n) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ :=
  fun i j ↦ (metricPair h (e.symm z)
    (chartTangent e z (realCoordinateVector i))
    (chartTangent e z (realCoordinateVector j))).re

/-- A smooth positive definite Hermitian tangent metric, in preferred-chart frames.
Smoothness is tested after transforming to every holomorphic chart; it is real smoothness.
Source: Kong §6.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
structure HermitianMetric (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Model n) M] where
  matrix : M → Matrix (Fin n) (Fin n) ℂ
  hermitian : ∀ x : M, (matrix x).IsHermitian
  positive : ∀ (x : M) (v : Model n), v ≠ 0 → 0 < (metricPair matrix x v v).re
  smooth : ∀ e : OpenPartialHomeomorph M (Model n), e ∈ atlas (Model n) M →
    ∀ i j : Fin n × Bool, ContDiffOn ℝ ∞ (fun z ↦ chartGram matrix e z i j) e.target

variable [MeasurableSpace M]

/-- The metric volume measure, characterized on every holomorphic chart by the density
`sqrt(det(Re g))` relative to ordinary real Lebesgue measure on `ℂ^n`.
Source: Kong §6.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
structure MetricVolume (g : HermitianMetric n M) where
  measure : Measure M
  chart_density : ∀ e : OpenPartialHomeomorph M (Model n), e ∈ atlas (Model n) M →
    Measure.map e (measure.restrict e.source) =
      ((volume : Measure (Model n)).withDensity
        (fun z ↦ ENNReal.ofReal (Real.sqrt (chartGram g.matrix e z).det))).restrict e.target

/-- Real Gram matrix at the preferred tangent frame.
Source: Kong §6.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def tangentGram (g : HermitianMetric n M) (x : M) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ :=
  fun i j ↦ (metricPair g.matrix x (realCoordinateVector i) (realCoordinateVector j)).re

/-- The induced metric on alternating covariant tensors: contraction with the inverse
real Gram matrix, normalized by `1/k!`. Source: Kong §6.1
(blueprint: def-sfb-hermitian-dolbeault-data). -/
def pointwiseFormPair (g : HermitianMetric n M) (k : ℕ) (x : M)
    (α η : FormFields n M) : ℂ :=
  (Nat.factorial k : ℂ)⁻¹ *
    ∑ a : Fin k → (Fin n × Bool), ∑ b : Fin k → (Fin n × Bool),
      star (α k x (fun j ↦ realCoordinateVector (a j))) *
        η k x (fun j ↦ realCoordinateVector (b j)) *
        ∏ j : Fin k, ((tangentGram g x)⁻¹ (a j) (b j) : ℂ)

/-- Integration of the pointwise metric, with different exterior degrees orthogonal.
There is no Hilbert completion. Source: Kong §6.1
(blueprint: def-sfb-hermitian-dolbeault-data). -/
def l2Pair (g : HermitianMetric n M) (μ : MetricVolume g)
    (α η : smoothForms (n := n) (M := M)) : ℂ :=
  ∑ k ∈ Finset.range (2 * n + 1), ∫ x, pointwiseFormPair g k x α.val η.val ∂μ.measure

/-- The Dolbeault operators and the smooth formal adjoint, specified on actual smooth
forms. Their sum is the coordinate exterior derivative, and they preserve the required
bidegrees. These normalizations exclude arbitrary differentials and arbitrary pairings.
Source: Kong §3.1 and §6.1, Lemma 6.2
(blueprint: def-sfb-hermitian-dolbeault-data). -/
structure DolbeaultOperators (g : HermitianMetric n M) (μ : MetricVolume g) where
  dbar : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  del : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  adjoint : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  dbar_type : ∀ (p q : ℤ) (α : smoothForms (n := n) (M := M)),
    α ∈ typeForms p q → dbar α ∈ typeForms p (q + 1)
  del_type : ∀ (p q : ℤ) (α : smoothForms (n := n) (M := M)),
    α ∈ typeForms p q → del α ∈ typeForms (p + 1) q
  adjoint_type : ∀ (p q : ℤ) (α : smoothForms (n := n) (M := M)),
    α ∈ typeForms p q → adjoint α ∈ typeForms p (q - 1)
  exterior_derivative : ∀ (α : smoothForms (n := n) (M := M)) (k : ℕ)
    (e : OpenPartialHomeomorph M (Model n)), e ∈ atlas (Model n) M →
    ∀ z ∈ e.target,
      formCoordinates (dbar α).val (k + 1) e z +
        formCoordinates (del α).val (k + 1) e z =
      extDerivWithin (formCoordinates α.val k e) e.target z
  square_zero : dbar.comp dbar = 0
  formal_adjoint : ∀ α η : smoothForms (n := n) (M := M),
    l2Pair g μ (dbar α) η = l2Pair g μ α (adjoint η)

/-- The Dolbeault Laplacian on smooth forms, `D D* + D* D`.
Source: Kong §6.1 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def DolbeaultOperators.laplacian {g : HermitianMetric n M} {μ : MetricVolume g}
    (D : DolbeaultOperators g μ) :
    smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M) :=
  D.dbar.comp D.adjoint + D.adjoint.comp D.dbar

/-- Harmonic smooth forms of a fixed integer type.
Source: Kong §6.2, Theorem 6.7 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def DolbeaultOperators.harmonic {g : HermitianMetric n M} {μ : MetricVolume g}
    (D : DolbeaultOperators g μ) (p q : ℤ) :
    Submodule ℂ (smoothForms (n := n) (M := M)) :=
  typeForms p q ⊓ D.laplacian.ker

/-- The actual image of smooth forms in the preceding type under `bar∂`.
Source: Kong §6.2, Theorem 6.7 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def DolbeaultOperators.exact {g : HermitianMetric n M} {μ : MetricVolume g}
    (D : DolbeaultOperators g μ) (p q : ℤ) :
    Submodule ℂ (smoothForms (n := n) (M := M)) :=
  (typeForms p (q - 1)).map D.dbar

/-- The actual image of smooth forms in the following type under `bar∂*`.
Source: Kong §6.2, Theorem 6.7 (blueprint: def-sfb-hermitian-dolbeault-data). -/
def DolbeaultOperators.coexact {g : HermitianMetric n M} {μ : MetricVolume g}
    (D : DolbeaultOperators g μ) (p q : ℤ) :
    Submodule ℂ (smoothForms (n := n) (M := M)) :=
  (typeForms p (q + 1)).map D.adjoint

end ComplexManifold
