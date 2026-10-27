module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Determinant
public import Sheaf.Geometry.Manifold.BundleSobolevSpace

/-! # The local weak equation for a real elliptic bundle operator

Source: Demailly, Complex Analytic and Differential Geometry, VI §§1–2, especially
(2.1) and (2.3), printed pp.288–289 (blueprint: def-sfb-elliptic-weak-bundle-equation).

The manifold, bundles, metrics and smooth sections are Mathlib's. The additional data
record a positive smooth volume measure, local finite-order coefficients, and the weak
equation. The latter is integration by parts in coordinates with respect to Lebesgue
measure, so the derivative acts on the product of a coefficient and a test function.
L² sections and real multi-index derivatives are the published BundleSobolev definitions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v w

open MeasureTheory Bundle
open BundleSobolev (Model)
open scoped Manifold ContDiff

namespace RealEllipticBundle

/-- An oriented subatlas. Positive transition determinants express the orientation;
the charts cover the manifold. Source: Demailly VI §1
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
structure OrientedAtlas (m : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (Model m) N] where
  charts : Set (OpenPartialHomeomorph N (Model m))
  subatlas : charts ⊆ IsManifold.maximalAtlas (𝓘(ℝ, Model m)) ∞ N
  covers : ∀ x : N, ∃ e ∈ charts, x ∈ e.source
  positive : ∀ e ∈ charts, ∀ e' ∈ charts, ∀ x ∈ e.source ∩ e'.source,
    0 < LinearMap.det (fderiv ℝ (fun z ↦ e' (e.symm z)) (e x)).toLinearMap

/-- A positive smooth volume form, represented by its measure and chart densities.
Compatibility with chart changes is enforced by equality of the pushed-forward measure.
Source: Demailly VI §§1–2 (blueprint: def-sfb-elliptic-weak-bundle-equation). -/
structure SmoothVolume (m : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (Model m) N] [MeasurableSpace N] where
  measure : Measure N
  density : OpenPartialHomeomorph N (Model m) → Model m → ℝ
  smooth : ∀ e ∈ atlas (Model m) N, ContDiffOn ℝ ∞ (density e) e.target
  positive : ∀ e ∈ atlas (Model m) N, ∀ z ∈ e.target, 0 < density e z
  chart_measure : ∀ e ∈ atlas (Model m) N,
    Measure.map e (measure.restrict e.source) =
      ((volume : Measure (Model m)).withDensity
        (fun z ↦ ENNReal.ofReal (density e z))).restrict e.target

/-- Smooth rank-`q` real bundles with a positive definite smooth fibre metric. All bundle
and metric notions are the existing Mathlib structures. Source: Demailly VI §§1–2
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
structure MetricBundle (m q : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (Model m) N] where
  Fiber : N → Type v
  normed : ∀ x, NormedAddCommGroup (Fiber x)
  innerProduct : ∀ x, InnerProductSpace ℝ (Fiber x)
  totalTopology : TopologicalSpace (TotalSpace (Model q) Fiber)
  fiberBundle : FiberBundle (Model q) Fiber
  vectorBundle : VectorBundle ℝ (Model q) Fiber
  smoothBundle : ContMDiffVectorBundle ∞ (Model q) Fiber (𝓘(ℝ, Model m))
  smoothMetric : IsContMDiffRiemannianBundle (𝓘(ℝ, Model m)) ∞ (Model q) Fiber

attribute [instance] MetricBundle.normed MetricBundle.innerProduct MetricBundle.totalTopology
attribute [instance] MetricBundle.fiberBundle MetricBundle.vectorBundle MetricBundle.smoothBundle
attribute [instance] MetricBundle.smoothMetric

variable {m q : ℕ} {N : Type u} [TopologicalSpace N] [ChartedSpace (Model m) N]

/-- Smooth sections, using Mathlib's section type. Source: Demailly VI §1
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
abbrev Sections (B : MetricBundle.{u, v} m q N) :=
  ContMDiffSection (𝓘(ℝ, Model m)) (Model q) ∞ B.Fiber

/-- Coordinate expression of a section in the preferred frame at `p`. The local equation
is imposed on the intersection of this frame domain and the chart at `p`.
Source: Demailly VI §§1–2 (blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def coordinates (B : MetricBundle.{u, v} m q N) (p : N) (s : ∀ x, B.Fiber x)
    (z : Model m) : Model q :=
  (trivializationAt (Model q) B.Fiber p
    (TotalSpace.mk' (Model q) ((chartAt (Model m) p).symm z)
      (s ((chartAt (Model m) p).symm z)))).2

/-- The chart/frame intersection used for a pair of bundles. These neighborhoods cover
`N`, since every one contains its indexing point. Source: Demailly VI §§1–2
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def coordinateDomain (G : MetricBundle.{u, v} m q N) (H : MetricBundle.{u, w} m q N)
    (p : N) : Set (Model m) :=
  (chartAt (Model m) p).target ∩
    (chartAt (Model m) p).symm ⁻¹'
      ((trivializationAt (Model q) G.Fiber p).baseSet ∩
        (trivializationAt (Model q) H.Fiber p).baseSet)

/-- Multi-indices of degree at most `k`. Source: Demailly VI §1
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def indices (m k : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter (fun α ↦ ∑ j, (α j).val ≤ k)

/-- A real-linear smooth differential operator of order at most `k`, with its actual
local coefficients in the chart/frame intersections. Source: Demailly VI §1
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
structure DifferentialOperator (G : MetricBundle.{u, v} m q N)
    (H : MetricBundle.{u, w} m q N) (k : ℕ) where
  operator : Sections G →ₗ[ℝ] Sections H
  coefficient : N → (Fin m → Fin (k + 1)) → Model m → Matrix (Fin q) (Fin q) ℝ
  smooth : ∀ p α a b,
    ContDiffOn ℝ ∞ (fun z ↦ coefficient p α z a b) (coordinateDomain G H p)
  expression : ∀ (s : Sections G) (p : N) (z : Model m),
    z ∈ coordinateDomain G H p → ∀ a : Fin q,
      coordinates H p (operator s) z a =
        ∑ α ∈ indices m k, ∑ b : Fin q,
          coefficient p α z a b * BundleSobolev.multiPartial (fun j ↦ (α j).val)
            (fun y ↦ coordinates G p s y b) z

/-- The degree-`k` principal symbol, with no factor of `i`. Source: Demailly VI §1
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def DifferentialOperator.symbol {G : MetricBundle.{u, v} m q N}
    {H : MetricBundle.{u, w} m q N} {k : ℕ} (Q : DifferentialOperator G H k)
    (p : N) (z ξ : Model m) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ α ∈ (indices m k).filter (fun α ↦ ∑ j, (α j).val = k),
    (∏ j, ξ j ^ (α j).val) • Q.coefficient p α z

/-- Ellipticity of the specified degree-`k` symbol, on every nonzero real cotangent
coordinate vector. Source: Demailly VI §2
(blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def DifferentialOperator.IsElliptic {G : MetricBundle.{u, v} m q N}
    {H : MetricBundle.{u, w} m q N} {k : ℕ} (Q : DifferentialOperator G H k) : Prop :=
  ∀ p z, z ∈ coordinateDomain G H p → ∀ ξ : Model m, ξ ≠ 0 →
    IsUnit (Q.symbol p z ξ)

variable [MeasurableSpace N]

/-- The local distributional equation `Qu = f`. It uses the representative of the
existing dependent almost-everywhere quotient of bundle sections. The tests are scalar,
smooth, and compactly supported inside the local coordinate domain; the derivative falls
on `b_α φ`, with sign `(-1)^|α|`.
Source: Demailly VI §§1–2 (blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def DifferentialOperator.WeakEquation {G : MetricBundle.{u, v} m q N}
    {H : MetricBundle.{u, w} m q N} {k : ℕ} (Q : DifferentialOperator G H k)
    (μ : Measure N) (u : BundleSobolev.L2 (q := q) G.Fiber μ) (f : Sections H) : Prop :=
  ∀ (p : N) (a : Fin q) (φ : Model m → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ coordinateDomain G H p →
        (∫ z in coordinateDomain G H p, coordinates H p f z a * φ z) =
          ∑ α ∈ indices m k, ∑ b : Fin q,
            (-1 : ℝ) ^ (∑ j, (α j).val) *
              ∫ z in coordinateDomain G H p, coordinates G p (Quotient.out u.val) z b *
                BundleSobolev.multiPartial (fun j ↦ (α j).val)
                  (fun y ↦ Q.coefficient p α y a b * φ y) z

/-- The given L² class has a smooth representative, with respect to its specified measure.
Source: Demailly VI §2 (blueprint: def-sfb-elliptic-weak-bundle-equation). -/
def HasSmoothRepresentative (B : MetricBundle.{u, v} m q N) (μ : Measure N)
    (u : BundleSobolev.L2 (q := q) B.Fiber μ) : Prop :=
  ∃ f : Sections B, ∀ᵐ x ∂μ, f x = Quotient.out u.val x

end RealEllipticBundle
