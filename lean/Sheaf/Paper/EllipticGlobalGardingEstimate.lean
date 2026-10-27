module

public import Sheaf.Geometry.Manifold.BundleEllipticEstimateData
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Global smooth-section Gårding estimate

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, (2.3) at Sobolev
index zero, with the two-bundle convention of VI §1, printed pp.287–289
(blueprint: lem-sfb-elliptic-global-garding-estimate).
-/

@[expose] public section

universe u v w

open Bundle
open scoped Manifold ContDiff

namespace RealManifold

/-- A fixed elliptic real bundle operator on a compact manifold controls the localized
order-`k` Sobolev norm of each smooth section by its image and its own integrated L² norm.
Source: Demailly VI (2.3), p.289, and VI §1 for two bundles
(blueprint: lem-sfb-elliptic-global-garding-estimate).

Proof plan (the four steps of the node):
1. On the empty base or at rank zero take C = 1. Otherwise use
   lem-sfb-differential-formal-adjoint-symbol to form Q* and the operator
   P(a,b) = (Q*b,Qa) on G ⊕ H.
2. If A is the symbol of Q, the symbol of P is (a,b) ↦ ((-1)^k A*b,Aa).
   Its inverse is (c,e) ↦ (A⁻¹e,(-1)^k (A⁻¹)*c), so P is elliptic.
3. Refine to finitely many charts trivializing both bundles, with cutoffs supplied by
   lem-sfb-smooth-subordinate-partition. Use lem-sfb-bundle-sobolev-rellich to compare
   the prescribed G-norm to the refined norm. Apply lem-sfb-weak-garding-sobolev-estimate
   at Sobolev index zero to (u,0). Smoothness identifies its distributional image with
   (0,Qu), and compactness makes both sections square-integrable.
4. The localized derivative sums for (u,0) and u coincide. Orthogonal sum fibre metrics
   identify their L² norms, and likewise those of (0,Qu) and Qu. Write the specified
   positive volume as ρ times Riemannian volume and use its strictly positive minimum.
   Absorb the atlas comparison and density bounds into C, independently of u. -/
theorem elliptic_global_garding_estimate
    (m r : ℕ) (hm : 1 ≤ m) (N : Type u) [TopologicalSpace N]
    [ChartedSpace (CoordinateModel m) N] [IsManifold 𝓘(ℝ, CoordinateModel m) ∞ N]
    [T2Space N] [CompactSpace N] [MeasurableSpace N] [BorelSpace N]
    (orientation : OrientedAtlas m N)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, CoordinateModel m) ∞ (CoordinateModel m)
      (TangentSpace 𝓘(ℝ, CoordinateModel m) : N → Type))
    (μ : PositiveSmoothVolume m N)
    (G : N → Type v) [TopologicalSpace (TotalSpace (CoordinateModel r) G)]
    [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℝ (G x)]
    [FiberBundle (CoordinateModel r) G] [VectorBundle ℝ (CoordinateModel r) G]
    [ContMDiffVectorBundle ∞ (CoordinateModel r) G 𝓘(ℝ, CoordinateModel m)]
    (H : N → Type w) [TopologicalSpace (TotalSpace (CoordinateModel r) H)]
    [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℝ (H x)]
    [FiberBundle (CoordinateModel r) H] [VectorBundle ℝ (CoordinateModel r) H]
    [ContMDiffVectorBundle ∞ (CoordinateModel r) H 𝓘(ℝ, CoordinateModel m)]
    (gG : ContMDiffRiemannianMetric 𝓘(ℝ, CoordinateModel m) ∞ (CoordinateModel r) G)
    (gH : ContMDiffRiemannianMetric 𝓘(ℝ, CoordinateModel m) ∞ (CoordinateModel r) H)
    (k : ℕ) (hk : 1 ≤ k)
    (Q : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ G →ₗ[ℝ]
      ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ H)
    (D : BundleDifferentialOperator k Q) (hD : D.IsElliptic)
    (A : BundleLocalization m r N G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ContMDiffSection 𝓘(ℝ, CoordinateModel m) (CoordinateModel r) ∞ G,
        A.sobolevNorm k s ≤ C * (bundleL2Norm gH μ (Q s) + bundleL2Norm gG μ s) := by
  sorry

end RealManifold
