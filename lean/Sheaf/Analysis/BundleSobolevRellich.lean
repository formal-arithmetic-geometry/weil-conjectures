module

public import Sheaf.Analysis.MetricBundleSobolevData
public import Sheaf.Geometry.Manifold.BundleSobolevSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Sheaf.Analysis.EuclideanFixedSupportRellich

/-! # Sobolev realization and Rellich compactness for metric bundles

Source: Demailly, Complex Analytic and Differential Geometry, VI §1 (1.4) and VI §2,
Sobolev-space setup and Rellich lemma (2.2), printed pp. 288--289
(blueprint: lem-sfb-bundle-sobolev-rellich).

The Hilbert completions are characterized by their dense linear smooth-section maps
and the precise integrated pairings. No realization or compactness assertion is an input.
The measurable realization is specified on smooth sections, hence is canonical by density.
-/

@[expose] public section

set_option autoImplicit false

open Bundle MeasureTheory Set Manifold Filter
open scoped Bundle Manifold ContDiff Topology

namespace BundleSobolev

universe u v

/-- Hilbert completions of the integrated and localized Sobolev pairings, their canonical
measurable and distributional realizations, independence of localization choices, and Rellich
compactness, including its bounded-sequence form.

Source: Demailly VI §1 (1.4), VI §2 Sobolev setup and Rellich (2.2), pp. 288--289
(blueprint: lem-sfb-bundle-sobolev-rellich).

Proof plan:
1. Integrate the fibre pairing and sum the localized derivative pairings. Positivity follows
   from a nonzero section being nonzero on an open set of positive volume, and the partition
   summing to one. Extend the pairings to Cauchy sequences by Cauchy--Schwarz. These are Hilbert
   completions with dense injective smooth-section maps.
2. On each compact cutoff support the metric matrices and volume densities are bounded above
   and below by positive constants. The integrated order-zero norm is therefore equivalent to
   the sum of the Euclidean localized order-zero norms. By
   lem-sfb-euclidean-sobolev-graph-mollification at order zero, local measurable limits glue,
   and smoothing with controlled supports gives dense smooth sections. This identifies the
   order-zero completion with all a.e. square-integrable sections and its integrated pairing.
3. The order-zero estimate bounds the identity from the Sobolev norm to the integrated norm.
   Extend by completion. The closed derivative graph in
   lem-sfb-euclidean-sobolev-graph-mollification identifies every derivative limit with the
   distributional derivative of the order-zero limit. If the latter is zero all derivative
   limits vanish, proving injectivity and one image inclusion.
4. Conversely smooth each localized weak section within a fixed compact chart support, using
   lem-sfb-euclidean-sobolev-graph-mollification. Reconstruct the finite sum of smooth sections.
   By lem-sfb-sobolev-chart-overlap-bound the errors tend to zero in every target chart.
   This proves the reverse image inclusion.
5. Apply lem-sfb-sobolev-chart-overlap-bound to each pair of source and target cutoffs. Finite
   summation gives both norm bounds between any two choices, and equality of their weak
   subspaces. The same change-of-variables formula gives compatibility of coefficient test
   functionals with the inverse metric density. Local Cauchy--Schwarz makes these continuous.
   If all local test pairings vanish, Euclidean test separation from
   lem-sfb-euclidean-sobolev-graph-mollification kills every localized coefficient a.e.; their
   finite sum is the original section. This gives injectivity into distributional sections.
6. For a bounded sequence in H^s, each localization has fixed compact support and bounded
   W^{1,2} norm since s ≥ 1. Apply lem-sfb-euclidean-fixed-support-rellich successively over the
   finitely many charts. The final subsequence is Cauchy in the integrated norm by step 2,
   hence converges in L². This proves compactness and its asserted sequential form. -/
theorem bundle_sobolev_rellich
    (m r : ℕ) (hm : 1 ≤ m)
    (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [CompactSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
    (h_oriented : ∃ A : Set (OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))),
      (∀ c ∈ A, c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N) ∧
      (∀ x : N, ∃ c ∈ A, x ∈ c.source) ∧
      ∀ c ∈ A, ∀ d ∈ A, ∀ x ∈ c.source ∩ d.source,
        0 < (fderiv ℝ (d ∘ c.symm) (c x)).toLinearMap.det)
    (B : N → Type v) [∀ x, NormedAddCommGroup (B x)]
    [∀ x, InnerProductSpace ℝ (B x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) B)]
    [FiberBundle (EuclideanSpace ℝ (Fin r)) B]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) B]
    [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) B
      𝓘(ℝ, EuclideanSpace ℝ (Fin m))]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (EuclideanSpace ℝ (Fin r)) B]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (EuclideanSpace ℝ (Fin m)) (fun x : N ↦ TangentSpace
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x))
    [MeasurableSpace N] [BorelSpace N] (V : MetricVolume g)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ L : HilbertCompletion
        (ContMDiffSection 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin r)) ∞ B)
        (fun u v ↦ l2Pairing V.measure u v),
      Function.Injective L.smooth ∧
      ∃ e : L.Space ≃ L2 (q := r) B V.measure,
        (∀ u, (e (L.smooth u)).val =
          ((u : ∀ x, B x) : Filter.Product (ae V.measure) B)) ∧
        (∀ u v : L.Space, inner ℝ u v = classPairing V.measure (e u) (e v)) ∧
        (∀ u : L.Space, ‖u‖ = l2Norm (q := r) B V.measure (e u)) ∧
        (∀ u : L2 (q := r) B V.measure,
          IsDistribution g (testPairing (m := m) V.measure u)) ∧
        Function.Injective (fun u : L2 (q := r) B V.measure ↦
          testPairing (m := m) V.measure u) ∧
        ∀ P : Localization (m := m) (q := r) B,
          ∃ H : HilbertCompletion
              (ContMDiffSection 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
                (EuclideanSpace ℝ (Fin r)) ∞ B)
              (fun u v ↦ sobolevPairing P s u v),
            Function.Injective H.smooth ∧
            ∃ j : H.Space →L[ℝ] L.Space,
              (∀ u, j (H.smooth u) = L.smooth u) ∧
              Function.Injective j ∧
              (∀ u : L.Space, (∃ v : H.Space, j v = u) ↔
                MemSobolev (m := m) (q := r) B V.measure s (e u)) ∧
              (∀ Q : Localization (m := m) (q := r) B,
                (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
                  ∀ u : ContMDiffSection 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
                      (EuclideanSpace ℝ (Fin r)) ∞ B,
                    c * Real.sqrt (sobolevPairing P s u u) ≤
                        Real.sqrt (sobolevPairing Q s u u) ∧
                      Real.sqrt (sobolevPairing Q s u u) ≤
                        C * Real.sqrt (sobolevPairing P s u u)) ∧
                (∀ u : L2 (q := r) B V.measure,
                  MemSobolev (m := m) (q := r) B V.measure s u ↔
                    ∀ (i : Fin Q.size) (k : Fin r),
                      HasWeakDerivatives s ⊤
                        (localizedCoefficient (q := r) B Q V.measure u i k))) ∧
              IsCompactOperator j ∧
              (∀ u : ℕ → H.Space, (∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) →
                ∃ (a : ℕ → ℕ) (v : L.Space), StrictMono a ∧
                  Tendsto (fun n ↦ j (u (a n))) atTop (𝓝 v)) := by
  sorry

end BundleSobolev
