module

public import Sheaf.Geometry.Manifold.BundleSobolevSpace

/-! # Pairings and distributions for the shared metric bundle Sobolev spaces

Source: Demailly, Complex Analytic and Differential Geometry, VI §1 (1.4) and VI §2,
printed pp. 288--289 (blueprint: def-sfb-metric-bundle-sobolev-data).

The underlying a.e. sections, volume, localizations and weak derivatives are those of
`Sheaf.Geometry.Manifold.BundleSobolevSpace`. This module adds their integrated pairings,
local distributional testing, and the dense-isometric Hilbert completion interface.
-/

@[expose] public section

set_option autoImplicit false

open Bundle MeasureTheory Set Manifold
open scoped Bundle Manifold ContDiff

namespace BundleSobolev

universe u v

variable {m r : ℕ} {N : Type u} [TopologicalSpace N]
  [ChartedSpace (Model m) N] [IsManifold 𝓘(ℝ, Model m) ∞ N]
  {B : N → Type v} [∀ x, NormedAddCommGroup (B x)]
  [∀ x, InnerProductSpace ℝ (B x)]
  [TopologicalSpace (TotalSpace (Model r) B)]
  [FiberBundle (Model r) B] [VectorBundle ℝ (Model r) B]

/-- Integrated fibre inner product; its diagonal is the squared order-zero norm.
Source: Demailly VI §2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
noncomputable def l2Pairing [MeasurableSpace N] (μ : Measure N) (u v : ∀ x, B x) : ℝ :=
  ∫ x, inner ℝ (u x) (v x) ∂μ

/-- Sum of the scalar localized derivative pairings through order `s`. The coordinates,
cutoffs, frames and multi-partials are exactly those of the shared Sobolev-space node.
Source: Demailly VI §2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
noncomputable def sobolevPairing (P : Localization (m := m) (q := r) B) (s : ℕ)
    (u v : ∀ x, B x) : ℝ :=
  open Classical in
  ∑ i : Fin P.size, ∑ k : Fin r, ∑ α : Fin m → Fin (s + 1),
    if (∑ a, (α a : ℕ)) ≤ s then
      ∫ y, multiPartial (fun a ↦ (α a : ℕ))
          (fun y ↦ if y ∈ (P.chart i).target then
            P.partition i ((P.chart i).symm y) *
              (P.frame i ⟨(P.chart i).symm y, u ((P.chart i).symm y)⟩).2 k
            else 0) y *
        multiPartial (fun a ↦ (α a : ℕ))
          (fun y ↦ if y ∈ (P.chart i).target then
            P.partition i ((P.chart i).symm y) *
              (P.frame i ⟨(P.chart i).symm y, v ((P.chart i).symm y)⟩).2 k
            else 0) y
    else 0

/-- Integrated pairing on the shared dependent a.e. classes, using representatives.
The realization theorem asserts agreement with the Hilbert inner product.
Source: Demailly VI §2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
noncomputable def classPairing [MeasurableSpace N] (μ : Measure N)
    (u v : L2 (q := r) B μ) : ℝ :=
  l2Pairing μ (Quotient.out u.val) (Quotient.out v.val)

/-- Local coefficient tests on the overlap of a smooth chart and a smooth bundle frame.
Both charts and frames are the corresponding shared maximal/trivialization atlas members.
Source: Demailly VI §2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
abbrev Tests
    (c : {c : OpenPartialHomeomorph N (Model m) //
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N})
    (e : {e : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) B → N) //
      e ∈ trivializationAtlas (Model r) B}) :=
  TestFunction ⟨c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet,
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet⟩ (Model r) ⊤

/-- Pair the frame coefficients of the shared a.e. section with a local coefficient test.
Source: Demailly VI §2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
noncomputable def testPairing [MeasurableSpace N] (μ : Measure N)
    (u : L2 (q := r) B μ)
    (c : {c : OpenPartialHomeomorph N (Model m) //
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N})
    (e : {e : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) B → N) //
      e ∈ trivializationAtlas (Model r) B}) (φ : Tests c e) : ℝ :=
  ∫ y, inner ℝ
    (e.val ⟨c.val.symm y, Quotient.out u.val (c.val.symm y)⟩).2 (φ y)

/-- A coefficient test as an intrinsic dual-section density relative to metric volume.
The inverse square-root Gram determinant is the usual coordinate Jacobian factor.
Source: Demailly VI §1--2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
noncomputable def testDensity
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model m) ∞ (Model m)
      (fun x : N ↦ TangentSpace 𝓘(ℝ, Model m) x))
    (c : {c : OpenPartialHomeomorph N (Model m) //
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N})
    (e : {e : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) B → N) //
      e ∈ trivializationAtlas (Model r) B}) (φ : Tests c e) (x : N) (v : B x) : ℝ :=
  open Classical in
  if x ∈ c.val.source ∩ e.val.baseSet then
    inner ℝ (e.val ⟨x, v⟩).2 (φ (c.val x)) /
      Real.sqrt (chartGram g c.val (c.val x)).det
  else 0

/-- Continuous local functionals with the usual density and change-of-frame compatibility.
Every finite relation of intrinsic test densities must give the same relation of pairings.
This indexes actual smooth charts and frames without introducing another localization type.
Source: Demailly VI §1--2 (blueprint: def-sfb-metric-bundle-sobolev-data). -/
def IsDistribution
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model m) ∞ (Model m)
      (fun x : N ↦ TangentSpace 𝓘(ℝ, Model m) x))
    (T : ∀ c : {c : OpenPartialHomeomorph N (Model m) //
        c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N},
      ∀ e : {e : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) B → N) //
        e ∈ trivializationAtlas (Model r) B}, Tests c e → ℝ) : Prop :=
  (∀ c e, ∃ t : Tests c e →L[ℝ] ℝ, ∀ φ, t φ = T c e φ) ∧
  ∀ (n : ℕ)
    (cs : Fin n → {c : OpenPartialHomeomorph N (Model m) //
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ N})
    (es : Fin n → {e : Trivialization (Model r)
        (TotalSpace.proj : TotalSpace (Model r) B → N) //
      e ∈ trivializationAtlas (Model r) B})
    (φ : ∀ i : Fin n, Tests (cs i) (es i)),
    (∀ (x : N) (v : B x), ∑ i, testDensity g (cs i) (es i) (φ i) x v = 0) →
      ∑ i, T (cs i) (es i) (φ i) = 0

universe a

/-- A Hilbert completion of a real pairing: a complete real inner product space and a
linear dense map pulling its inner product back to the pairing. The dense-isometric
characterization specifies the completion up to its unique isometric linear equivalence.
Existence and injectivity are conclusions of the realization theorem. The scalar structure
is supplied only by `InnerProductSpace`, avoiding a second `NormedSpace`/`Module` instance.
Source: Demailly VI §2 completion setup (blueprint: def-sfb-metric-bundle-sobolev-data). -/
structure HilbertCompletion (S : Type a) [AddCommGroup S] [Module ℝ S]
    (pairing : S → S → ℝ) where
  Space : Type a
  group : NormedAddCommGroup Space
  hilbert : InnerProductSpace ℝ Space
  complete : CompleteSpace Space
  smooth : S →ₗ[ℝ] Space
  dense : DenseRange smooth
  inner_smooth : ∀ u v : S, inner ℝ (smooth u) (smooth v) = pairing u v

attribute [instance] HilbertCompletion.group HilbertCompletion.hilbert
  HilbertCompletion.complete

end BundleSobolev
