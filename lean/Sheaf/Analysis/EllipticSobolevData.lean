/-
Copyright (c) 2026 The Weil SHEAF project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil SHEAF project
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.List.FinRange

/-! # Geometric data and specifications for elliptic Sobolev realization

Source: Demailly, Complex Analytic and Differential Geometry, VI §1 (1.1), (1.4),
and VI §2 before (2.1) and Corollary (2.4)(ii), printed pp.287–290
(blueprint: def-sfb-elliptic-sobolev-realization-data).

Completion spaces are specified by complete inner product spaces with dense linear images
and the stated norm formula. This characterizes the completions up to their unique isometry;
no completion, measurable representative, or extension is assumed to exist in the input.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

open Bundle MeasureTheory
open scoped Manifold ContDiff Topology

namespace EllipticSobolev

/-- Real Euclidean model. Source: Demailly VI §1 (1.1)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
abbrev Model (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Coordinate multi-index derivative, in increasing coordinate order.
Source: Demailly VI §1 (1.1) (blueprint: def-sfb-elliptic-sobolev-realization-data). -/
def coordinateDerivative {m : ℕ} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : Fin m → ℕ) (f : Model m → F) : Model m → F :=
  (List.finRange m).foldr
    (fun j g ↦ (fun h x ↦ fderiv ℝ h x (EuclideanSpace.single j 1))^[α j] g) f

/-- Compact oriented smooth base, with its metric and metric volume. The finite oriented
charts cover the base; positivity of every transition determinant encodes orientation.
The volume is specified by its metric density, rather than by an arbitrary measure.
Source: Demailly VI §§1–2 (blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure Base (m : ℕ) (N : Type u) [TopologicalSpace N] [ChartedSpace (Model m) N]
    [IsManifold (𝓘(ℝ, Model m)) ∞ N] [MeasurableSpace N] where
  metric : ContMDiffRiemannianMetric (𝓘(ℝ, Model m)) ∞ (Model m)
    (fun x : N ↦ TangentSpace (𝓘(ℝ, Model m)) x)
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph N (Model m)
  chart_mem : ∀ i, chart i ∈ IsManifold.maximalAtlas (𝓘(ℝ, Model m)) ∞ N
  cover : ∀ x : N, ∃ i, x ∈ (chart i).source
  oriented : ∀ (i j : Fin count) (z : Model m),
    z ∈ (chart j).target → (chart j).symm z ∈ (chart i).source →
      0 < (fderiv ℝ ((chart i) ∘ (chart j).symm) z).det
  weight : N → ℝ
  weight_smooth : ContMDiff (𝓘(ℝ, Model m)) 𝓘(ℝ) ∞ weight
  weight_pos : ∀ x, 0 < weight x
  measure : Measure N
  density : ∀ (e : OpenPartialHomeomorph N (Model m)),
    e ∈ IsManifold.maximalAtlas (𝓘(ℝ, Model m)) ∞ N →
    Measure.map e (measure.restrict e.source) =
      ((volume : Measure (Model m)).withDensity (fun z ↦ ENNReal.ofReal
        (weight (e.symm z) * Real.sqrt (Matrix.det (fun i j : Fin m ↦
          metric.inner (e.symm z)
            (mfderiv (𝓘(ℝ, Model m)) (𝓘(ℝ, Model m)) e.symm z
              (EuclideanSpace.single i 1))
            (mfderiv (𝓘(ℝ, Model m)) (𝓘(ℝ, Model m)) e.symm z
              (EuclideanSpace.single j 1))))))).restrict e.target

/-- A smooth rank-`r` real bundle with a smooth positive metric, using Mathlib's bundle,
section and metric structures. Source: Demailly VI §1 (1.4)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure MetricBundle (m r : ℕ) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (Model m) N] where
  fiber : N → Type v
  [fiberTopology : ∀ x, TopologicalSpace (fiber x)]
  [fiberGroup : ∀ x, AddCommGroup (fiber x)]
  [fiberModule : ∀ x, Module ℝ (fiber x)]
  [fiberAdd : ∀ x, IsTopologicalAddGroup (fiber x)]
  [fiberSMul : ∀ x, ContinuousConstSMul ℝ (fiber x)]
  [totalTopology : TopologicalSpace (TotalSpace (Model r) fiber)]
  [fiberBundle : FiberBundle (Model r) fiber]
  [vectorBundle : VectorBundle ℝ (Model r) fiber]
  [smooth : ContMDiffVectorBundle ∞ (Model r) fiber (𝓘(ℝ, Model m))]
  metric : ContMDiffRiemannianMetric (𝓘(ℝ, Model m)) ∞ (Model r) fiber

attribute [instance] MetricBundle.fiberTopology MetricBundle.fiberGroup
  MetricBundle.fiberModule MetricBundle.fiberAdd MetricBundle.fiberSMul
  MetricBundle.totalTopology MetricBundle.fiberBundle MetricBundle.vectorBundle MetricBundle.smooth

variable {m r : ℕ} {N : Type u} [TopologicalSpace N] [ChartedSpace (Model m) N]

/-- A smooth section is exactly Mathlib's smooth section. Source: Demailly VI §1 (1.4)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
abbrev Sections (B : MetricBundle.{u, v} m r N) :=
  ContMDiffSection (𝓘(ℝ, Model m)) (Model r) ∞ B.fiber

/-- A compatible coordinate chart and smooth bundle frame on its whole domain.
Source: Demailly VI §1 (1.4) (blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure FrameChart (B : MetricBundle.{u, v} m r N) where
  chart : OpenPartialHomeomorph N (Model m)
  chart_mem : chart ∈ IsManifold.maximalAtlas (𝓘(ℝ, Model m)) ∞ N
  frame : Trivialization (Model r) (fun p : TotalSpace (Model r) B.fiber ↦ p.proj)
  [frame_mem : MemTrivializationAtlas frame]
  domain : chart.source ⊆ frame.baseSet

attribute [instance] FrameChart.frame_mem

/-- Frame coefficients, extended by zero off the chart. Source: Demailly VI §1 (1.4)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
def coefficients {B : MetricBundle.{u, v} m r N} (c : FrameChart B)
    (s : ∀ x, B.fiber x) (z : Model m) : Model r := by
  classical
  exact if z ∈ c.chart.target then
    (c.frame (TotalSpace.mk' (Model r) (c.chart.symm z) (s (c.chart.symm z)))).2 else 0

/-- The finite chart/frame/partition choice used in the Sobolev norm. Compact support lies
inside the chart, including when the base or the index family is empty.
Source: Demailly VI §2 before (2.1)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure Localization (B : MetricBundle.{u, v} m r N) where
  count : ℕ
  charts : Fin count → FrameChart B
  partition : SmoothPartitionOfUnity (Fin count) (𝓘(ℝ, Model m)) N
  compact : ∀ i, HasCompactSupport (partition i)
  subordinate : ∀ i, tsupport (partition i) ⊆ (charts i).chart.source

/-- The literal finite sum of localized Euclidean derivative energies.
Source: Demailly VI §2 before (2.1)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
def sobolevEnergy {B : MetricBundle.{u, v} m r N} (a : Localization B) (k : ℕ)
    (s : Sections B) : ℝ :=
  ∑ i : Fin a.count, ∑ α : Fin m → Fin (k + 1),
    if (∑ j, (α j).val) ≤ k then
      ∫ z, ‖coordinateDerivative (fun j ↦ (α j).val)
        (fun z ↦ a.partition i ((a.charts i).chart.symm z) •
          coefficients (a.charts i) s z) z‖ ^ 2 else 0

/-- The integrated metric pairing. Source: Demailly VI §1 (1.4)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
def l2Pair [IsManifold (𝓘(ℝ, Model m)) ∞ N] [MeasurableSpace N]
    (d : Base m N) (B : MetricBundle.{u, v} m r N)
    (s t : ∀ x, B.fiber x) : ℝ :=
  ∫ x, B.metric.inner x (s x) (t x) ∂d.measure

/-- Local coefficients specify an order-at-most-`k` differential operator; the top-degree
polynomial is invertible for every nonzero real covector, in every compatible chart/frame.
Source: Demailly VI §1 (1.1)–(1.3)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure EllipticOperator (G H : MetricBundle.{u, v} m r N) (k : ℕ) where
  op : Sections G →ₗ[ℝ] Sections H
  coeff : FrameChart G → FrameChart H → (Fin m → Fin (k + 1)) →
    Model m → Model r →L[ℝ] Model r
  coeff_smooth : ∀ (c : FrameChart G) (e : FrameChart H), c.chart = e.chart →
    ∀ α, ContDiffOn ℝ ∞ (coeff c e α) c.chart.target
  formula : ∀ (c : FrameChart G) (e : FrameChart H), c.chart = e.chart →
    ∀ (s : Sections G) (z : Model m), z ∈ c.chart.target →
      coefficients e (op s) z =
        ∑ α : Fin m → Fin (k + 1), if (∑ j, (α j).val) ≤ k then
          coeff c e α z (coordinateDerivative (fun j ↦ (α j).val) (coefficients c s) z) else 0
  elliptic : ∀ (c : FrameChart G) (e : FrameChart H), c.chart = e.chart →
    ∀ (z ξ : Model m), z ∈ c.chart.target → ξ ≠ 0 →
      Function.Bijective (∑ α : Fin m → Fin (k + 1),
        if (∑ j, (α j).val) = k then
          (∏ j, ξ j ^ (α j).val) • coeff c e α z else 0)


/-- Coordinatewise measurability of a section, without imposing a global trivialization.
Source: Demailly VI §1 (1.4) (blueprint: def-sfb-elliptic-sobolev-realization-data). -/
def MeasurableSection (B : MetricBundle.{u, v} m r N) (s : ∀ x, B.fiber x) : Prop :=
  ∀ c : FrameChart B, AEStronglyMeasurable (coefficients c s)
    ((volume : Measure (Model m)).restrict c.chart.target)

/-- A Hilbert completion of smooth sections in the integrated norm, together with its
canonical measurable realization and local regular distributions. The representative is
only used modulo almost-everywhere equality; `eq_iff_ae` and `exhaustive` give precisely
that quotient. Every local distribution has the actual regular-section integral formula.
Source: Demailly VI §1 (1.4), VI §2 before (2.1)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure L2Model [IsManifold (𝓘(ℝ, Model m)) ∞ N] [MeasurableSpace N]
    (d : Base m N) (B : MetricBundle.{u, v} m r N) where
  space : Type (max u v)
  [normed : NormedAddCommGroup space]
  [inner : InnerProductSpace ℝ space]
  [complete : CompleteSpace space]
  ofSmooth : Sections B →ₗ[ℝ] space
  dense : DenseRange ofSmooth
  pairing : ∀ s t : Sections B, Inner.inner ℝ (ofSmooth s) (ofSmooth t) = l2Pair d B s t
  representative : space → ∀ x, B.fiber x
  measurable : ∀ u, MeasurableSection B (representative u)
  integrable : ∀ u, Integrable
    (fun x ↦ B.metric.inner x (representative u x) (representative u x)) d.measure
  inner_representative : ∀ u v, Inner.inner ℝ u v = l2Pair d B (representative u) (representative v)
  smooth_representative : ∀ s : Sections B,
    ∀ᵐ x ∂d.measure, representative (ofSmooth s) x = s x
  eq_iff_ae : ∀ u v, u = v ↔ ∀ᵐ x ∂d.measure, representative u x = representative v x
  exhaustive : ∀ s : ∀ x, B.fiber x, MeasurableSection B s →
    Integrable (fun x ↦ B.metric.inner x (s x) (s x)) d.measure →
      ∃ u, ∀ᵐ x ∂d.measure, representative u x = s x
  distribution : ∀ c : FrameChart B,
    space →ₗ[ℝ] Distribution ⟨c.chart.target, c.chart.open_target⟩ (Model r) ⊤
  regular : ∀ (c : FrameChart B) (u : space)
    (φ : TestFunction ⟨c.chart.target, c.chart.open_target⟩ ℝ ⊤),
    distribution c u φ = ∫ z, φ z • coefficients c (representative u) z
  injective_distribution : Function.Injective (fun u ↦ fun c : FrameChart B ↦ distribution c u)

attribute [instance] L2Model.normed L2Model.inner L2Model.complete

/-- A Sobolev completion and its canonical inclusion in the integrated completion.
The exact dense-image norm formula fixes the completion for the chosen localization.
Source: Demailly VI §2 before (2.1)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
structure SobolevModel [IsManifold (𝓘(ℝ, Model m)) ∞ N] [MeasurableSpace N]
    {d : Base m N} {B : MetricBundle.{u, v} m r N} (a : Localization B) (k : ℕ)
    (L : L2Model d B) where
  space : Type (max u v)
  [normed : NormedAddCommGroup space]
  [inner : InnerProductSpace ℝ space]
  [complete : CompleteSpace space]
  ofSmooth : Sections B →ₗ[ℝ] space
  dense : DenseRange ofSmooth
  norm_ofSmooth : ∀ s : Sections B, ‖ofSmooth s‖ ^ 2 = sobolevEnergy a k s
  toL2 : space →L[ℝ] L.space
  injective : Function.Injective toL2
  smooth_image : ∀ s : Sections B, toL2 (ofSmooth s) = L.ofSmooth s

attribute [instance] SobolevModel.normed SobolevModel.inner SobolevModel.complete

/-- The distributional differential formula is tested componentwise on all compactly
supported smooth tests. The coefficient multiplies the test before differentiation:
this is precisely the transpose rule for variable-coefficient differential operators.
Source: Demailly VI §1 (1.1), VI §2 (2.3)
(blueprint: def-sfb-elliptic-sobolev-realization-data). -/
def DistributionalEquation [IsManifold (𝓘(ℝ, Model m)) ∞ N] [MeasurableSpace N]
    {d : Base m N} {G H : MetricBundle.{u, v} m r N} {k : ℕ}
    (Q : EllipticOperator G H k) (LG : L2Model d G) (LH : L2Model d H)
    (u : LG.space) (v : LH.space) : Prop :=
  ∀ (c : FrameChart G) (e : FrameChart H), c.chart = e.chart →
    ∀ (φ : TestFunction ⟨c.chart.target, c.chart.open_target⟩ ℝ ⊤) (j : Fin r),
    (∫ z, φ z * (coefficients e (LH.representative v) z) j) =
      ∑ α : Fin m → Fin (k + 1), if (∑ i, (α i).val) ≤ k then
        (-1 : ℝ) ^ (∑ i, (α i).val) *
          ∫ z, ∑ l : Fin r, (coefficients c (LG.representative u) z) l *
            coordinateDerivative (fun i ↦ (α i).val)
              (fun z ↦ φ z * (Q.coeff c e α z (EuclideanSpace.single l 1)) j) z
        else 0

end EllipticSobolev
