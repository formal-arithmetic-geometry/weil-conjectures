module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Determinant

/-!
# Coordinate data for real bundle elliptic estimates

Source: Demailly, Complex Analytic and Differential Geometry, VI §§1–2,
(1.1)–(1.4) and the Sobolev setup before (2.1), printed pp.287–289
(blueprint: def-sfb-bundle-elliptic-estimate-data).

These data use Mathlib's manifolds, vector bundles, sections, fibre metrics and partitions.
The additional structures specify smooth coordinate frames, a positive smooth volume,
local differential expressions, and the literal localized integer Sobolev norm.
-/

@[expose] public section

noncomputable section

universe u v w

open Bundle MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace RealManifold

/-- The standard real coordinate model. Source: Demailly VI §1, p.287
(blueprint: def-sfb-bundle-elliptic-estimate-data). -/
abbrev CoordinateModel (m : ℕ) := EuclideanSpace ℝ (Fin m)

variable {m r : ℕ} {N : Type u} [TopologicalSpace N]
  [ChartedSpace (CoordinateModel m) N]

/-- An arbitrary smooth chart compatible with the given manifold, including its smooth inverse.
Source: Demailly VI §1, p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure SmoothCoordinateChart (m : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (CoordinateModel m) N] where
  chart : OpenPartialHomeomorph N (CoordinateModel m)
  smooth : ContMDiffOn 𝓘(ℝ, CoordinateModel m) 𝓘(ℝ, CoordinateModel m) ∞ chart chart.source
  smooth_symm : ContMDiffOn 𝓘(ℝ, CoordinateModel m) 𝓘(ℝ, CoordinateModel m) ∞
    chart.symm chart.target

/-- An orientation is a covering smooth atlas with positive transition Jacobians.
It need not be the atlas chosen to define the Sobolev norm.
Source: Demailly VI §1, p.288 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure OrientedAtlas (m : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (CoordinateModel m) N] where
  charts : Set (SmoothCoordinateChart m N)
  covers : ∀ x : N, ∃ e ∈ charts, x ∈ e.chart.source
  positive : ∀ e ∈ charts, ∀ f ∈ charts, ∀ x ∈ e.chart.source ∩ f.chart.source,
    0 < LinearMap.det (fderiv ℝ (fun z ↦ f.chart (e.chart.symm z)) (e.chart x)).toLinearMap

variable [MeasurableSpace N]

/-- A smooth positive volume, specified by its measure and smooth strictly positive densities
in every smooth chart. This permits any positive volume form, independently of the metric.
Source: Demailly VI (1.4), p.288 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure PositiveSmoothVolume (m : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (CoordinateModel m) N] [MeasurableSpace N] where
  measure : Measure N
  density : SmoothCoordinateChart m N → CoordinateModel m → ℝ
  smooth : ∀ e, ContDiffOn ℝ ∞ (density e) e.chart.target
  positive : ∀ e, ∀ z ∈ e.chart.target, 0 < density e z
  chart_density : ∀ e, Measure.map e.chart (measure.restrict e.chart.source) =
    ((volume : Measure (CoordinateModel m)).withDensity
      (fun z ↦ ENNReal.ofReal (density e z))).restrict e.chart.target

variable {E : N → Type v} [TopologicalSpace (TotalSpace (CoordinateModel r) E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle (CoordinateModel r) E] [VectorBundle ℝ (CoordinateModel r) E]

/-- A linear bundle trivialization smooth in both directions. Requiring smooth maps directly
allows every smooth frame, without restricting to a preselected bundle atlas.
Source: Demailly VI §1, p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure SmoothCoordinateFrame (m r : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (CoordinateModel m) N] (E : N → Type v)
    [TopologicalSpace (TotalSpace (CoordinateModel r) E)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [FiberBundle (CoordinateModel r) E] [VectorBundle ℝ (CoordinateModel r) E] where
  triv : Trivialization (CoordinateModel r) (TotalSpace.proj : TotalSpace (CoordinateModel r) E → N)
  linear : triv.IsLinear ℝ
  smooth : ContMDiffOn
    (𝓘(ℝ, CoordinateModel m).prod 𝓘(ℝ, CoordinateModel r))
    (𝓘(ℝ, CoordinateModel m).prod 𝓘(ℝ, CoordinateModel r)) ∞ triv triv.source
  smooth_symm : ContMDiffOn
    (𝓘(ℝ, CoordinateModel m).prod 𝓘(ℝ, CoordinateModel r))
    (𝓘(ℝ, CoordinateModel m).prod 𝓘(ℝ, CoordinateModel r)) ∞
    triv.toOpenPartialHomeomorph.symm triv.target

/-- Frame coefficients on a smooth coordinate chart. Values off the chart target are immaterial.
Source: Demailly VI (1.1), p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def sectionCoordinates (e : SmoothCoordinateChart m N) (f : SmoothCoordinateFrame m r N E)
    (s : ∀ x, E x) (z : CoordinateModel m) : CoordinateModel r :=
  (f.triv ⟨e.chart.symm z, s (e.chart.symm z)⟩).2

/-- Coordinate partial derivatives in the order `1,...,m`, each repeated its multi-index entry.
Source: Demailly VI (1.1), p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def coordinatePartial (α : Fin m → ℕ) (f : CoordinateModel m → CoordinateModel r) :
    CoordinateModel m → CoordinateModel r :=
  ((List.ofFn (fun j : Fin m ↦ j)).flatMap (fun j ↦ List.replicate (α j) j)).foldr
    (fun j h z ↦ fderiv ℝ h z (EuclideanSpace.single j 1)) f

/-- The finite set of multi-indices through order `k`, with no multiplicities.
Source: Demailly VI §2 Sobolev setup (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def coordinateMultiIndices (m k : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter (fun α ↦ ∑ j, (α j).val ≤ k)

/-- A finite smooth chart and frame cover with subordinate compactly supported partition.
The frames are required only for this bundle; a second bundle can have its own local charts.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure BundleLocalization (m r : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (CoordinateModel m) N] (E : N → Type v)
    [TopologicalSpace (TotalSpace (CoordinateModel r) E)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [FiberBundle (CoordinateModel r) E] [VectorBundle ℝ (CoordinateModel r) E] where
  count : ℕ
  chart : Fin count → SmoothCoordinateChart m N
  frame : Fin count → SmoothCoordinateFrame m r N E
  frame_domain : ∀ i, (chart i).chart.source ⊆ (frame i).triv.baseSet
  covers : ∀ x : N, ∃ i, x ∈ (chart i).chart.source
  partition : SmoothPartitionOfUnity (Fin count) 𝓘(ℝ, CoordinateModel m) N
  subordinate : partition.IsSubordinate (fun i ↦ (chart i).chart.source)
  compact_support : ∀ i, HasCompactSupport (partition i)

/-- Localized frame coefficients, extended by zero outside the chart target.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def BundleLocalization.localized (A : BundleLocalization m r N E) (i : Fin A.count)
    (s : ∀ x, E x) (z : CoordinateModel m) : CoordinateModel r :=
  (A.chart i).chart.target.indicator (fun w ↦
    (A.partition i ((A.chart i).chart.symm w)) •
      sectionCoordinates (A.chart i) (A.frame i) s w) z

/-- Square root of the sum of squared Euclidean L² norms of all localized derivatives.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def BundleLocalization.sobolevNorm (A : BundleLocalization m r N E) (k : ℕ)
    (s : ∀ x, E x) : ℝ :=
  Real.sqrt (∑ i, ∑ α ∈ coordinateMultiIndices m k,
    ∫ z : CoordinateModel m,
      ‖coordinatePartial (fun j ↦ (α j).val) (A.localized i s) z‖ ^ 2)

/-- Integrated norm for the specified fibre metric and positive volume.
Source: Demailly VI (1.4), p.288 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def bundleL2Norm
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, CoordinateModel m) ∞ (CoordinateModel r) E)
    (μ : PositiveSmoothVolume m N) (s : ∀ x, E x) : ℝ :=
  Real.sqrt (∫ x, g.inner x (s x) (s x) ∂μ.measure)

variable {H : N → Type w} [TopologicalSpace (TotalSpace (CoordinateModel r) H)]
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℝ (H x)]
  [FiberBundle (CoordinateModel r) H] [VectorBundle ℝ (CoordinateModel r) H]

/-- A local differential expression for the specified real-linear operator, including its
smooth coefficients and its identity on every smooth section.
Source: Demailly VI (1.1), p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure LocalDifferentialExpression (k : ℕ)
    (Q : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ E →ₗ[ℝ]
      ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ H) where
  chart : SmoothCoordinateChart m N
  domainFrame : SmoothCoordinateFrame m r N E
  codomainFrame : SmoothCoordinateFrame m r N H
  domain_frame : chart.chart.source ⊆ domainFrame.triv.baseSet
  codomain_frame : chart.chart.source ⊆ codomainFrame.triv.baseSet
  coefficient : (Fin m → Fin (k + 1)) → CoordinateModel m →
    CoordinateModel r →L[ℝ] CoordinateModel r
  smooth : ∀ α, ContDiffOn ℝ ∞ (coefficient α) chart.chart.target
  expression : ∀ (s : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ E)
    (z : CoordinateModel m), z ∈ chart.chart.target →
    sectionCoordinates chart codomainFrame (Q s) z =
      ∑ α ∈ coordinateMultiIndices m k, coefficient α z
        (coordinatePartial (fun j ↦ (α j).val) (sectionCoordinates chart domainFrame s) z)

/-- The degree-`k` symbol in the coordinate cotangent and fibre frames.
Source: Demailly VI (1.2), p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def LocalDifferentialExpression.symbol {k : ℕ}
    {Q : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ E →ₗ[ℝ]
      ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ H}
    (L : LocalDifferentialExpression k Q) (z ξ : CoordinateModel m) :
    CoordinateModel r →L[ℝ] CoordinateModel r :=
  ∑ α ∈ (coordinateMultiIndices m k).filter (fun α ↦ ∑ j, (α j).val = k),
    (∏ j, ξ j ^ (α j).val) • L.coefficient α z

/-- A smooth differential operator of order at most `k`, with local expressions covering N.
Source: Demailly VI (1.1), p.287 (blueprint: def-sfb-bundle-elliptic-estimate-data). -/
structure BundleDifferentialOperator (k : ℕ)
    (Q : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ E →ₗ[ℝ]
      ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ H) where
  localExpression : N → LocalDifferentialExpression k Q
  covers : ∀ x : N, x ∈ (localExpression x).chart.chart.source

/-- Invertibility of the top-degree symbol at every nonzero coordinate covector. Because each
chart and frame is an isomorphism, this is precisely invertibility on the actual fibres.
Source: Demailly VI (1.2), (1.8), pp.287–289
(blueprint: def-sfb-bundle-elliptic-estimate-data). -/
def BundleDifferentialOperator.IsElliptic {k : ℕ}
    {Q : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ E →ₗ[ℝ]
      ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ H}
    (D : BundleDifferentialOperator k Q) : Prop :=
  ∀ (x : N) (z : CoordinateModel m), z ∈ (D.localExpression x).chart.chart.target →
    ∀ ξ : CoordinateModel m, ξ ≠ 0 → Function.Bijective ((D.localExpression x).symbol z ξ)

end RealManifold
