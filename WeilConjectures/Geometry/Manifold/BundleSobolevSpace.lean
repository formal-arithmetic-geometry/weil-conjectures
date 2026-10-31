/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Weak Sobolev spaces of real bundle sections

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, preceding (2.1), p.289.
(blueprint: def-sfb-bundle-sobolev-space)

These spaces consist of actual almost-everywhere classes of measurable sections. Local weak
partial derivatives are specified by their action on compactly supported smooth real tests.
The metric volume is characterized in coordinates by the square root of the Gram determinant.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace BundleSobolev

/-- The coordinate tangent model. Source: Demailly VI §2, p.289.
(blueprint: def-sfb-bundle-sobolev-space) -/
abbrev Model (m : ℕ) := EuclideanSpace ℝ (Fin m)

variable {m q : ℕ} {N : Type u} [TopologicalSpace N] [ChartedSpace (Model m) N]
  [IsManifold 𝓘(ℝ, Model m) ∞ N]

/-- A chart's coordinate Gram matrix for a smooth Riemannian metric on the tangent bundle.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def chartGram
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model m) ∞ (Model m)
      (TangentSpace 𝓘(ℝ, Model m) : N → Type _))
    (c : OpenPartialHomeomorph N (Model m)) (y : Model m) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ g.inner (c.symm y)
    (mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) c.symm y (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) c.symm y (EuclideanSpace.single j 1))

variable [MeasurableSpace N]

/-- Riemannian volume, specified on every smooth chart by its exact coordinate density.
This is a measure with a prescribed local formula, not an arbitrary positive measure.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
structure MetricVolume
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model m) ∞ (Model m)
      (TangentSpace 𝓘(ℝ, Model m) : N → Type _)) where
  measure : Measure N
  chart_density : ∀ c : OpenPartialHomeomorph N (Model m),
    c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N →
    Measure.map c (measure.restrict c.source) =
      ((volume : Measure (Model m)).withDensity
        (fun y ↦ ENNReal.ofReal (Real.sqrt (chartGram g c y).det))).restrict c.target

variable (B : N → Type v) [TopologicalSpace (TotalSpace (Model q) B)]
  [∀ x, NormedAddCommGroup (B x)] [∀ x, InnerProductSpace ℝ (B x)]
  [FiberBundle (Model q) B] [VectorBundle ℝ (Model q) B]

/-- A finite oriented coordinate trivializing cover and a subordinate smooth partition of unity.
Its positive transition determinants encode the chosen orientation. These are the choices used
in the localized Sobolev norms. Source: Demailly VI §2, p.289, with the localization convention
of lem-sfb-bundle-sobolev-embedding (blueprint: def-sfb-bundle-sobolev-space). -/
structure Localization where
  size : ℕ
  chart : Fin size → OpenPartialHomeomorph N (Model m)
  chart_smooth : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N
  frame : Fin size → Trivialization (Model q) (TotalSpace.proj : TotalSpace (Model q) B → N)
  frame_smooth : ∀ i, frame i ∈ trivializationAtlas (Model q) B
  chart_in_frame : ∀ i, (chart i).source ⊆ (frame i).baseSet
  covers : ∀ x : N, ∃ i, x ∈ (chart i).source
  positive_transition : ∀ i j, ∀ y ∈ ((chart i).symm ≫ₕ chart j).source,
    0 < LinearMap.det (fderiv ℝ (chart j ∘ (chart i).symm) y).toLinearMap
  partition : SmoothPartitionOfUnity (Fin size) 𝓘(ℝ, Model m) N Set.univ
  subordinate : partition.IsSubordinate (fun i ↦ (chart i).source)

/-- Measurable square-integrable sections modulo almost-everywhere equality, using Mathlib's
filter product for dependent functions. Measurability refers to the Borel total space.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def L2 (μ : Measure N) :=
  {v : Filter.Product (ae μ) B // ∃ s : ∀ x, B x,
    (s : Filter.Product (ae μ) B) = v ∧
    @AEMeasurable N (TotalSpace (Model q) B) (borel _) _ (fun x ↦ ⟨x, s x⟩) μ ∧
    Integrable (fun x ↦ ‖s x‖ ^ 2) μ}

/-- The integrated L² norm of the given class. `Quotient.out` selects a representative of an
existing quotient; its norm integral is invariant under the defining equivalence relation.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def l2Norm (μ : Measure N) (v : L2 (q := q) B μ) : ℝ :=
  Real.sqrt (∫ x, ‖Quotient.out v.val x‖ ^ 2 ∂μ)

/-- Ordered multi-index differentiation of scalar test functions, including order zero.
Source: Demailly VI §2, weak derivatives, p.289
(blueprint: def-sfb-bundle-sobolev-space). -/
def multiPartial (α : Fin m → ℕ) (f : Model m → ℝ) : Model m → ℝ :=
  (List.ofFn (fun i : Fin m ↦ List.replicate (α i) i)).flatten.foldr
    (fun i h ↦ fun y ↦ fderiv ℝ h y (EuclideanSpace.single i 1)) f

/-- The weak derivative identity on an open coordinate domain, with local square integrability.
Tests have closed support compactly contained in the domain; all integrations use Lebesgue
measure, without a Riemannian density in the distributional identity.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def IsWeakDerivative (U : TopologicalSpace.Opens (Model m)) (α : Fin m → ℕ)
    (f d : Model m → ℝ) : Prop :=
  AEStronglyMeasurable d (volume.restrict U) ∧
  LocallyIntegrableOn (fun y ↦ ‖d y‖ ^ 2) U volume ∧
  ∀ φ : TestFunction U ℝ ⊤,
    (∫ y in U, d y * φ y) = (-1 : ℝ) ^ (∑ i, α i) * ∫ y in U, f y * multiPartial α φ y

/-- Local weak square integrability through a prescribed integer order.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def HasWeakDerivatives (j : ℕ) (U : TopologicalSpace.Opens (Model m)) (f : Model m → ℝ) : Prop :=
  AEStronglyMeasurable f (volume.restrict U) ∧
  LocallyIntegrableOn (fun y ↦ ‖f y‖ ^ 2) U volume ∧
  ∀ α : Fin m → ℕ, (∑ i, α i) ≤ j → ∃ d, IsWeakDerivative U α f d

/-- Sobolev membership of an L² class, tested in every smooth chart and bundle frame.
Order zero is exactly L². At positive orders the representative's coefficients have all
specified local distributional derivatives; changing the representative changes no test integral.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def MemSobolev (μ : Measure N) (j : ℕ) (v : L2 (q := q) B μ) : Prop :=
  j = 0 ∨ ∀ c : OpenPartialHomeomorph N (Model m),
    c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N →
    ∀ e : Trivialization (Model q) (TotalSpace.proj : TotalSpace (Model q) B → N),
    e ∈ trivializationAtlas (Model q) B → ∀ k : Fin q,
      HasWeakDerivatives j
        ⟨c.target ∩ c.symm ⁻¹' e.baseSet, c.isOpen_inter_preimage_symm e.open_baseSet⟩
        (fun y ↦ (e ⟨c.symm y, Quotient.out v.val (c.symm y)⟩).2 k)

/-- The subspace Hʲ of L², represented as a subtype of the actual almost-everywhere classes.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def H (μ : Measure N) (j : ℕ) := {v : L2 (q := q) B μ // MemSobolev (m := m) (q := q) B μ j v}

open Classical in
/-- The zero extension of one localized frame coefficient.
Source: Demailly VI §2, p.289, finite-chart Sobolev norms
(blueprint: def-sfb-bundle-sobolev-space). -/
def localizedCoefficient (L : Localization (m := m) (q := q) B) (μ : Measure N)
    (v : L2 (q := q) B μ)
    (i : Fin L.size) (k : Fin q) (y : Model m) : ℝ :=
  if y ∈ (L.chart i).target then
    L.partition i ((L.chart i).symm y) *
      (L.frame i ⟨(L.chart i).symm y, Quotient.out v.val ((L.chart i).symm y)⟩).2 k
  else 0

/-- A chosen weak derivative of a localized coefficient. On a Sobolev section this is
uniquely determined almost everywhere; consequently all its L² integrals are canonical.
No existence theorem with postponed proof is used to choose data here.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def weakDerivative (α : Fin m → ℕ) (f : Model m → ℝ) : Model m → ℝ :=
  Classical.epsilon (fun d ↦ IsWeakDerivative ⊤ α f d)

/-- The stipulated finite-chart Sobolev norm: order zero uses the integrated bundle norm;
positive orders use the square root of the sum of squared Euclidean L² derivative norms.
Multi-indices are enumerated finitely by their components, each at most `j`.
Source: Demailly VI §2, p.289 (blueprint: def-sfb-bundle-sobolev-space). -/
def sobolevNorm (L : Localization (m := m) (q := q) B) (μ : Measure N) (j : ℕ)
    (v : H (m := m) (q := q) B μ j) : ℝ :=
  if j = 0 then l2Norm (q := q) B μ v.val else
    Real.sqrt (∑ i : Fin L.size, ∑ k : Fin q,
      ∑ α : Fin m → Fin (j + 1),
        if (∑ a, (α a : ℕ)) ≤ j then
          ∫ y, ‖weakDerivative (fun a ↦ (α a : ℕ))
            (localizedCoefficient (q := q) B L μ v.val i k) y‖ ^ 2
        else 0)

end BundleSobolev
