module

public import Sheaf.Geometry.Manifold.BundleSobolevSpace
import Sheaf.Analysis.WeakSobolevFourierMoments
import Sheaf.Analysis.FourierMomentRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Finite-order Sobolev representatives of bundle sections

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, Sobolev lemma (2.1),
printed p.289 (blueprint: lem-sfb-bundle-sobolev-embedding).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open MeasureTheory Bundle
open scoped Manifold ContDiff

namespace BundleSobolev

/-- Every Hᵗ section has a unique Cʳ representative of its given almost-everywhere class
when t > r + m/2. The localization specifies the finite oriented chart cover, bundle frames,
and smooth partition used for the Sobolev norms; no estimate depends on that choice here.

Source: Demailly VI §2, (2.1), printed p.289.
(blueprint: lem-sfb-bundle-sobolev-embedding)

Proof plan:
1. Use the finite coordinate trivializing cover and the smooth subordinate partition
(lem-sfb-smooth-subordinate-partition). Compactness makes each closed support compact,
with compact image inside the chart's open target.
2. Localize every coefficient by the partition and extend by zero to Rᵐ. The weak
Leibniz identity follows by testing the weak derivative against the product of the cutoff
and the test. Iterate this identity through order t. All multiplier derivatives are bounded
on the compact support, so every derivative is L². The supported test products stay inside
the chart, making zero extension introduce no boundary term. Complexify these real functions.
3. Apply lem-sfb-weak-sobolev-fourier-moments to obtain integrable Fourier moments through
order r, then lem-sfb-fourier-moment-representative to get a Cʳ inverse integral equal to
the localized L² class almost everywhere. Take its real part. On the complement of the
compact support, lem-sfb-continuous-ae-pointwise forces this representative to vanish.
4. Transfer each coefficient back to its bundle frame and extend by zero to N. The support
is closed inside the chart, so extension is Cʳ even near its boundary. Coordinate Lebesgue
and metric-volume null sets coincide because the smooth density sqrt(det g) is positive:
a zero density integral makes each intersection with {density ≥ 1/n} null, and these
intersections exhaust the set. Sum the finitely many localized sections; the partition
sums to one, so the resulting section has exactly the prescribed class v.
5. Two Cʳ representatives have continuous coefficients agreeing almost everywhere in every
chart. Apply lem-sfb-continuous-ae-pointwise to their complexifications coefficientwise,
then use the cover to conclude equality of sections. Empty N and rank zero give the unique
zero section and require no nonemptiness assumption.
-/
theorem existsUnique_contMDiff_representative
    {m q : ℕ} (hm : 1 ≤ m) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (Model m) N] [IsManifold 𝓘(ℝ, Model m) ∞ N]
    [T2Space N] [SecondCountableTopology N] [CompactSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, Model m) ∞ (Model m)
      (TangentSpace 𝓘(ℝ, Model m) : N → Type _))
    (μ : MetricVolume g)
    (B : N → Type v) [TopologicalSpace (TotalSpace (Model q) B)]
    [∀ x, NormedAddCommGroup (B x)] [∀ x, InnerProductSpace ℝ (B x)]
    [FiberBundle (Model q) B] [VectorBundle ℝ (Model q) B]
    [ContMDiffVectorBundle ∞ (Model q) B 𝓘(ℝ, Model m)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Model m) ∞ (Model q) B]
    (L : Localization (m := m) (q := q) B)
    (t r : ℕ) (htr : (r : ℝ) + (m : ℝ) / 2 < (t : ℝ))
    (v : H (m := m) (q := q) B μ.measure t) :
    ∃! s : ContMDiffSection 𝓘(ℝ, Model m) (Model q) r B,
      (s.toFun : Filter.Product (ae μ.measure) B) = v.val.val := by
  sorry

end BundleSobolev
