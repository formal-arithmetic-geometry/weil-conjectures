## Worker report

The delivery states `BundleSobolev.existsUnique_contMDiff_representative` in
`Sheaf.Geometry.Manifold.BundleSobolevEmbedding`. Its only proof is `sorry`.
The node's statement, proof, and proof dependencies are unchanged. Its statement dependencies
only gain the new definition node described below. No statement correction or disputed claim.

Source checked directly: downloaded the specified Demailly PDF into this sandbox and read PDF
pages 289–290 with pdftotext. VI §2 assumes a compact Riemannian manifold, defines W^k by L²
coefficient derivatives, and states (2.1) with the exact strict bound k > l + m/2. The node
specifies the representative interpretation and weak-derivative localization used here.

Hypothesis and clause correspondence:

- Real scalars: `ℝ` in the model, bundle vector spaces, fibre metrics, tests, and integrals.
  `def-weil-field` is Mathlib `Field`; its full class signature and docstring were read.
- Dimension m ≥ 1: `m : ℕ`, `hm : 1 ≤ m`.
- Smooth boundaryless manifold: `ChartedSpace (Model m) N` and
  `IsManifold 𝓘(ℝ, Model m) ∞ N`; the self model has no boundary or corners.
- Compact Hausdorff second-countable manifold: `CompactSpace`, `T2Space`, and
  `SecondCountableTopology`. The standard measurable structure is `BorelSpace`.
- Orientation: `L : Localization B` contains a covering finite family of smooth charts and
  `positive_transition`, positivity of every transition Jacobian determinant on its domain.
  This is an oriented atlas, without demanding positivity of every chart in the maximal atlas.
- Smooth Riemannian metric: `g : ContMDiffRiemannianMetric ...` on the actual tangent bundle.
  `MetricVolume g` fixes `μ.measure` by the coordinate sqrt(det Gram) formula. Its Gram matrix
  uses the derivative of the inverse chart applied to the standard Euclidean basis vectors.
  This specifies the given metric's positive volume, rather than merely any full-support measure.
- Smooth finite-rank metric bundle: model fibre `EuclideanSpace ℝ (Fin q)`,
  `FiberBundle`, `VectorBundle`, `ContMDiffVectorBundle ∞`, fibre `InnerProductSpace ℝ`,
  and `IsContMDiffRiemannianBundle ... ∞`. Independent universe `v` for the actual fibres.
- L² sections modulo almost-everywhere equality: `L2 B μ` is the subtype of the dependent
  quotient `Filter.Product (ae μ) B` admitting an almost-everywhere Borel measurable section
  with integrable squared fibre norm. This encodes measurable representatives modulo null sets.
- Hʲ local weak derivatives: `MemSobolev` tests coefficients on every maximal smooth chart
  and every frame of the bundle atlas, on their open intersection. `HasWeakDerivatives` asks
  for every multi-index with sum ≤ j, and `IsWeakDerivative` explicitly gives the signed
  integration-by-parts identity against `TestFunction U ℝ ⊤`. Both coefficients and weak
  derivatives are locally square integrable. `H B μ j` is the subset of the same L² classes.
- H⁰ = L²: the `j = 0` alternative in `MemSobolev` includes every L² class. The subtype
  carries just a redundant proof at order zero, not a different function space.
- The fixed finite coordinate-trivializing cover and smooth subordinate partition are the
  `Localization` fields `chart`, `frame`, `chart_in_frame`, `covers`, `partition`, `subordinate`.
  The finite-cover charts may be smaller than the corresponding frame domains, as usual.
- The prescribed norms: `l2Norm` integrates the squared fibre norm. `localizedCoefficient`
  multiplies by the partition and extends by zero. `sobolevNorm` is sqrt of the finite sum
  over charts, frame components and multi-indices of the Euclidean squared derivative integrals;
  its order-zero branch is exactly `l2Norm`. Enumerating α in Fin m → Fin (j+1), then filtering
  by total degree ≤ j, enumerates every required multi-index once.
- Nonnegative integers t,r: `t r : ℕ`. Strict real bound: `htr : (r : ℝ) + (m : ℝ)/2 < t`;
  the division is real, not truncated natural-number division.
- The prescribed v ∈ Hᵗ(B): `v : H B μ.measure t`.
- Existence, Cʳ regularity and uniqueness: `∃! s : ContMDiffSection ... r B`.
- Representative of the given class: `(s.toFun : Filter.Product (ae μ.measure) B) = v.val.val`.
  Equality is in the very quotient underlying v, not equality of abstract embeddings or norms.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field).
- Mathlib.Geometry.Manifold.IsManifold.Basic: `IsManifold`, `IsManifold.maximalAtlas`;
  Mathlib.Geometry.Manifold.ChartedSpace: `ChartedSpace` (def-sfb-smooth-real-manifold).
- Mathlib.Geometry.Manifold.VectorBundle.Basic: `ContMDiffVectorBundle`, full signature and
  smooth-transition clause (def-sfb-smooth-real-vector-bundle).
- Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection: `ContMDiffSection`, including its
  function and regularity fields (def-sfb-smooth-bundle-sections).
- Mathlib.Analysis.Distribution.TestFunction: `TestFunction`, smoothness, compact support and
  support-containment fields (def-sfb-local-coefficient-tests).
- Mathlib.Geometry.Manifold.PartitionOfUnity: `SmoothPartitionOfUnity` and
  `SmoothPartitionOfUnity.exists_isSubordinate`, full structure and signature
  (lem-sfb-smooth-subordinate-partition). The theorem module also imports this proof dependency.
- Sheaf.Analysis.WeakSobolevFourierMoments:
  `Real.integrable_fourier_moments_of_weak_derivatives`.
- Sheaf.Analysis.FourierMomentRepresentative:
  `MeasureTheory.Lp.fourier_moments_inverse_representative`.
- Mathlib.MeasureTheory.Measure.OpenPos: `MeasureTheory.Measure.eqOn_open_of_ae_eq`
  (lem-sfb-continuous-ae-pointwise).

The last three signatures/docstrings were read in full. They are plain proof imports.
The theorem docstring follows every recorded localization, Fourier, gluing and uniqueness step.

Searches actually run through msearch.py (recorded in searches.jsonl):

- LeanSearch: “Sobolev spaces of square integrable sections of a smooth vector bundle on a compact
  Riemannian manifold and unique finite differentiability representatives”: 8 smooth-section/
  Riemannian-bundle hits, none the required weak Sobolev space or embedding.
- LeanFinder: “Sobolev embedding for weak derivatives of finite rank bundle sections on compact
  manifolds”: 8 Euclidean derivative estimates and fixed-support derivative-map hits, no match.
- Loogle: `"Sobolev"`: 12 hits in Mathlib.Analysis.Distribution.Sobolev, Euclidean Bessel-potential
  spaces and their calculus, no bundle sections or Cʳ representative theorem.
- Mathlib grep Geometry: `Sobolev|sobolev|VolumeForm|volumeForm`: no hits.
- Mathlib grep Analysis/Distribution: `Sobolev|MetricVolume|IsWeakDerivative|Filter.Product`:
  only Euclidean Sobolev declarations and the derivative-notation documentation.
- Direct rg of lean/WeilConjectures and lean/Sheaf for Sobolev, sobolev, the item ID,
  BundleSobolev, IsWeakDerivative and MetricVolume found only the recorded Fourier prerequisites
  and ComplexManifold.MetricVolume, whose holomorphic Hermitian base does not cover arbitrary
  real bundles/manifolds. No duplicate was written.
- DAG definition searches and blueprint_refs.py search Sobolev / Sobolev section found no
  Sobolev definition. Other searches located the existing real-manifold, real-bundle,
  section and coefficient-test nodes, which the new node cites rather than restating.
  `blueprint_refs.py ancestor` reports None for the item's inherited lineage, recorded as null.

Edge cases checked before drafting:

- Empty N: no Nonempty instance; size zero is permitted for the cover. The quotient has a unique
  section and ∃! has the required empty-domain meaning. All integrated norms are zero.
- Rank q = 0: no positivity or nontriviality assumption on the fibre. Fin q is empty, the local
  derivative tests and sums have no components, and the unique section represents the zero class.
- r = 0: ContMDiffSection at order zero is continuous, so uniqueness still follows from open-set
  almost-everywhere equality. The strict bound excludes t = 0 when m ≥ 1.
- Order j = 0 is defined exactly as L²; the multi-index zero differentiates the test zero times.
- Critical t = r + m/2 is excluded by strict inequality. Odd m uses genuine real division.
- Disconnected N is allowed; no connectedness is imposed. Independent fibre universe is retained.
- Coordinate-frame overlap is open and derivative tests have support compactly inside it.
  Zero extension is only used after multiplication by a cutoff supported inside the chart.

Validation: both modules compiled through scompile.py, separately in dependency order,
with no errors or warnings in the clean pass. All variables/universes are explicitly bound;
autoImplicit is false in both files. Final delivery preflight/compiles are run below.

## New nodes

`def-sfb-bundle-sobolev-space`, in the item's chapter, owns
`Sheaf.Geometry.Manifold.BundleSobolevSpace` and its concrete data/helper declarations:
Model, chartGram, MetricVolume, Localization, L2, l2Norm, multiPartial, IsWeakDerivative,
HasWeakDerivatives, MemSobolev, H, localizedCoefficient, weakDerivative, sobolevNorm.
Its statement cites the existing manifold, bundle, smooth section, partition and test notions.
No theorem is postponed in this definition module. Metric and localization structures carry
actual data and exact formulas. Quotient.out selects from a quotient of genuine sections.
The weakDerivative selector is Classical.epsilon on the full test identity, not a selection
from a sorry existence theorem; on Sobolev inputs that identity fixes the result modulo the
same equality used by the derivative norm integral. The definitions use no sorry or axiom.

## Second reading by NO

No second reading by a worker: as instructed, this worker delivers directly and the maintainer's
independent review reads the delivery. No subagent was started.
