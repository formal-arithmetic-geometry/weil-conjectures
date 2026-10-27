module

public import Sheaf.Geometry.Manifold.EllipticWeakBundleEquation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Sheaf.Geometry.Manifold.BundleSobolevEmbedding

/-! # L² weak elliptic regularity for real bundle operators

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, Gårding inequality
(2.3) and Sobolev lemma (2.1), printed p.289
(blueprint: lem-sfb-elliptic-adjoint-regularity).

The distributional hypothesis is expanded using compact smooth coordinate tests. Its
conclusion concerns the original almost-everywhere class of the given L² section.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open MeasureTheory Bundle RealEllipticBundle
open BundleSobolev (Model)
open scoped Manifold ContDiff

/-- An L² section whose elliptic image is smooth has a smooth representative.
Source: Demailly VI §2, (2.1) and (2.3), printed p.289, with the two-bundle block reduction
(blueprint: lem-sfb-elliptic-adjoint-regularity).

Proof plan:
1. Apply lem-sfb-differential-formal-adjoint-symbol to construct Q*. On G ⊕ H set
   P(a,b) = (Q*b,Qa). If A is the degree-k symbol of Q, the symbol of P is
   ((a,b) ↦ ((-1)^k A*b,Aa)), with inverse
   ((c,e) ↦ (A⁻¹e,(-1)^k(A*)⁻¹c)). Thus P is elliptic and P(u,0) = (0,f).
2. Choose a finite common coordinate/frame cover and a subordinate smooth partition
   (lem-sfb-smooth-subordinate-partition). All derivatives of the localized smooth
   right-hand side are square integrable by compactness. For every s ≥ 0, apply
   lem-sfb-weak-garding-sobolev-estimate to get (u,0) in H^(s+k), without any
   prior assumption on its weak derivatives. A smooth positive volume different from
   the metric volume has bounded positive density ratio on the compact base, so the
   L² classes and local regularity do not change.
3. Given r ≥ 0, take s+k > r+m/2 and apply lem-sfb-bundle-sobolev-embedding to
   get a C^r representative of the same class, including a continuous one at r=0.
4. Uniqueness of continuous representatives identifies all these representatives
   pointwise. The common representative is C^r for every r, hence smooth. Project
   it to G to obtain the required smooth representative of the original class.
-/
theorem RealEllipticBundle.hasSmoothRepresentative_of_elliptic_weakEquation
    (m q k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (N : Type u) [TopologicalSpace N] [T2Space N] [CompactSpace N]
    [ChartedSpace (Model m) N] [IsManifold (𝓘(ℝ, Model m)) ∞ N]
    [MeasurableSpace N] [BorelSpace N]
    (orientation : OrientedAtlas m N)
    (g : ContMDiffRiemannianMetric (𝓘(ℝ, Model m)) ∞ (Model m)
      (fun x : N ↦ TangentSpace (𝓘(ℝ, Model m)) x))
    (μ : SmoothVolume m N)
    (G : MetricBundle.{u, v} m q N) (H : MetricBundle.{u, w} m q N)
    (Q : DifferentialOperator G H k) (hQ : Q.IsElliptic)
    (u : BundleSobolev.L2 (q := q) G.Fiber μ.measure)
    (hQu : ∃ f : Sections H, Q.WeakEquation μ.measure u f) :
    HasSmoothRepresentative G μ.measure u := by
  sorry
