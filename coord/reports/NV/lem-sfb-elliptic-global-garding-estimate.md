## Worker report

The module `Sheaf.Paper.EllipticGlobalGardingEstimate` states
`RealManifold.elliptic_global_garding_estimate`. Its only proof is `sorry`.
The item's statement, accepted split and proof dependencies are unchanged. The statement dependency
list gains `def-sfb-bundle-elliptic-estimate-data`, whose module supplies explicit coordinate data
and actual norm formulas. Nothing is assumed about a Sobolev completion or weak regularity.

Source read: Demailly, *Complex Analytic and Differential Geometry*, VI §1 (1.1)–(1.8),
printed pp.287–289, and VI §2 (2.1)–(2.4), pp.289–290. I retrieved the PDF from the URL in
the node and read those pages. The web reader timed out; direct retrieval succeeded. In particular,
(1.1) gives the local matrix differential expression, (1.2) its symbol, (1.4) the integrated norm,
and (2.3) the estimate with the lower norm remainder. The node's two-bundle version is supported
by its accepted block-operator reduction, which the theorem docstring preserves step by step.
This delivery makes no change to the blueprint unit or to that proof route.

Clause-by-clause reading of the theorem:

- Real scalars: all smoothness, fibre linear maps and `Q` use `ℝ`, Mathlib's field.
- Dimension `m ≥ 1`: `(m : ℕ)` and `hm : 1 ≤ m`. The model is
  `CoordinateModel m = EuclideanSpace ℝ (Fin m)`.
- Smooth manifold without boundary: `ChartedSpace (CoordinateModel m) N` and
  `IsManifold 𝓘(ℝ, CoordinateModel m) ∞ N`, using the self model without corners.
  `T2Space N` is the usual Hausdorff manifold convention. `CompactSpace N` is compactness.
  No nonemptiness or connectedness is assumed. `MeasurableSpace` and `BorelSpace` specify the
  ordinary Borel measurable structure for integration, rather than a restriction on manifolds.
- Orientation: `orientation : OrientedAtlas m N` supplies a covering smooth atlas with positive
  transition determinants. It does not require the atlas used for the norm to be oriented.
- Smooth Riemannian metric: `g : Bundle.ContMDiffRiemannianMetric ... (TangentSpace ...)`.
  The tangent model lives in `Type`, independently of the base's universe `u`.
- Positive smooth volume form: `μ : PositiveSmoothVolume m N` specifies exactly its associated
  positive measure, with positive smooth densities in every smooth chart. It is independent of
  `g`, as allowed by the item's proof (density-ratio step). There is no arbitrary measure.
- Smooth real bundles of the same finite rank: `G : N → Type v` and `H : N → Type w` share
  the finite-dimensional model `CoordinateModel r`, with `FiberBundle`, `VectorBundle` and
  `ContMDiffVectorBundle ∞` instances. Fibre universes `v,w` are independent.
- Smooth positive definite fibre metrics: `gG` and `gH` are Mathlib's smooth Riemannian metrics
  on the respective bundles, not arbitrary norm functions.
- Integer order `k ≥ 1`: `k : ℕ`, `hk : 1 ≤ k`.
- Real-linear operator on actual smooth sections: `Q` is a `→ₗ[ℝ]` between the two
  `ContMDiffSection ... ∞` spaces. Their pointwise real vector-space structures are Mathlib's.
- Local formula with smooth coefficients and order at most `k`: `D : BundleDifferentialOperator
  k Q` has a local expression near every point; each expression uses actual smooth coordinate
  charts and smooth linear frames, smooth continuous-linear-map coefficients, and an equality
  on every smooth section with the finite sum of coordinate partials. Matrices and continuous
  linear maps between these finite-dimensional coordinate spaces are the same data.
- Principal-symbol invertibility at all nonzero covectors: `hD : D.IsElliptic` asserts
  `Function.Bijective` for the sum of top-order coefficients times `ξ^α`, for every coordinate
  covector `ξ ≠ 0` in every chosen local expression. Coordinate and fibre frames are linear
  isomorphisms, so this is precisely the fibrewise condition in the node. The cover ensures no
  base point is omitted.
- Fixed finite trivializing atlas and smooth compactly supported subordinate partition:
  `A : BundleLocalization m r N G` includes a finite chart cover, a smooth frame on each
  chart, `SmoothPartitionOfUnity`, its `IsSubordinate` property and compact supports. It
  trivializes G only, exactly as the item permits; it imposes no common-frame requirement on H.
- Specified H^k norm: `A.sobolevNorm k s` is literally the square root of the finite sum of
  Euclidean integrals of squared norms of coordinate partial derivatives of the localized frame
  coefficients extended by zero. Each multi-index with total order at most k occurs once.
- Specified L² norms: `bundleL2Norm gH μ (Q s)` and `bundleL2Norm gG μ s` are square roots
  of the integrated fibre metric on the actual sections, for the specified volume.
- A positive constant independent of the section: `∃ C : ℝ, 0 < C ∧ ∀ s, ...` puts `C`
  after all fixed data and before the smooth section. The inequality is exactly the unsquared
  bound, with the sum of the two integrated norms on the right.

Dependency declarations read and used:

- `def-weil-field` is a Mathlib leaf for `Field`,
  `Mathlib.Algebra.Field.Defs`, line 180; its full signature extends `CommRing` and
  `DivisionRing`. Here the existing instance on `ℝ` supplies it.
- `def-sfb-smooth-real-manifold` is a Mathlib leaf for `ChartedSpace` and `IsManifold`;
  `def-sfb-smooth-real-vector-bundle` for `ContMDiffVectorBundle`; and
  `def-sfb-smooth-bundle-sections` for `ContMDiffSection` and its pointwise group/module
  instances. I read their node records and the full structures and comments in
  `Mathlib.Geometry.Manifold.ChartedSpace`, `...IsManifold.Basic`,
  `...VectorBundle.Basic` and `...VectorBundle.ContMDiffSection`.
- `Bundle.ContMDiffRiemannianMetric` from `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`
  supplies symmetric, positive definite smooth fibre pairings. I read the structure and its
  surrounding assumptions; no replacement metric definition is introduced.
- `lem-sfb-smooth-subordinate-partition` is the Mathlib leaf
  `SmoothPartitionOfUnity.exists_isSubordinate` in
  `Mathlib.Geometry.Manifold.PartitionOfUnity`; I read its signature and the partition and
  subordination structures. The new localization reuses those structures, and the theorem
  includes this module as a plain proof import.
- The other three proof nodes (`lem-sfb-differential-formal-adjoint-symbol`,
  `lem-sfb-bundle-sobolev-rellich`, `lem-sfb-weak-garding-sobolev-estimate`) have no Lean
  records in the read clone. Their natural-language statements were read. The statement uses
  none of their conclusions as assumptions. Their proof-import wiring remains for the maintainer
  when those modules land; no unstated dependency theorem is silently replaced.

Edge cases checked before and after writing:

- Empty N is allowed. The orientation cover, operator expressions and ellipticity have no
  base points to check; a localization with `count = 0` has the zero norm and the integral is
  zero. C = 1 works.
- Rank r = 0 is allowed even on a nonempty base. The model fibre is the zero space, its unique
  endomorphism is bijective, and both integrated and localized norms vanish.
- k = 1 is included, while k = 0 and m = 0 are excluded exactly by the node's hypotheses.
  The helper definitions themselves allow those values without an invalid finite sum.
- A nontrivial kernel is permitted: the `‖s‖L²` remainder is retained. On a circle, the
  derivative annihilates constants, so omitting this term would make the claim false.
- Arbitrary smooth frames, nonisomorphic G and H, and a volume different from Riemannian
  volume are all permitted. A chart/frame is required to be smooth in both directions,
  rather than belonging to a preselected atlas, so no permissible norm choice is excluded.
- The finite multi-index set bounds each entry by k and then filters by its sum; it neither
  duplicates mixed partials nor omits the zeroth derivative. `coordinatePartial` repeats
  the coordinate directions in increasing coordinate order, as Demailly's D^α does.
- No norm, differential action or symbol is an unconstrained parameter. Every one has an
  explicit formula or its defining coordinate identity; every definition has real data.

Searches performed (all msearch calls used the assigned group and item):

- LeanFinder: `global Garding inequality for a smooth elliptic differential operator between
  real metric bundles on a compact manifold` returned Euclidean Sobolev inequalities,
  compact-support seminorm bounds and Schwartz Laplacian integration identities, no estimate.
- Loogle: `"ContMDiffSection"` found the existing bundled sections and their instances, reused.
  `"Garding"` returned zero hits.
- msearch grep `Garding|Sobolev|DifferentialOperator`, `Analysis/`: returned the Euclidean
  Gagliardo–Nirenberg inequalities and distributional Bessel-potential Sobolev spaces, not this
  bundle operator estimate.
- LeanSearch: `smooth local differential operator principal symbol metric vector bundle
  localized integer Sobolev norm` returned smooth Riemannian metrics and smooth sections,
  reused here; it gave no coordinate operator or localization norm.
- LeanSearch: `A finite chart localization of smooth vector bundle sections defines the
  Sobolev norm by sums of coordinate partial derivative squared integrals` returned section
  summation and bundled-section declarations; no such norm construction.
- LeanFinder: `smooth positive volume measure in manifold charts and principal symbol of
  local differential operator` returned integral separation results using a preexisting measure
  and bounds on chart derivatives, not the requested data.
- msearch grep `partialDerivative|iteratedPDeriv|DifferentialOperator|Garding|positive.*volume`,
  `Geometry/`: zero hits. Direct rg of Mathlib found no manifold orientation API; its bundle
  metrics, frames, smooth sections and finite-dimensional coordinate calculus were inspected.
- An additional whole-Mathlib msearch grep for the proposed names timed out and was reported
  UNAVAILABLE, not a mathematical no-match. The successful scoped grep and semantic searches
  above are the absence evidence.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for `Garding|Gårding|elliptic.*estimate`
  and the item id found no statement. The upstream-name table has none of the proposed names.
  `HermitianDolbeaultData` was read: its complex alternating tensors, complex metric volume and
  type-form L² pairing do not define any of the arbitrary real-bundle data needed here.
- DAG and blueprint searches found the existing Mathlib-leaf manifold, vector-bundle and
  section definitions, reused; no separate node defining this localization/operator packaging.
  `tools/blueprint_refs.py search 'Garding'`, `'Sobolev'`, `'bundle localization'`, and
  `'differential operator'` each found zero blueprint nodes. `ancestor` reports None for this
  inherited supporting chain, retained in the new node with the item's complete `via` chain.

The data module and theorem module have both compiled individually in dependency order through
`scompile.py`, against the live project, with no errors or warnings. No local build was run.
No statement correction or disputed mathematical assertion was needed.

## New nodes

`def-sfb-bundle-elliptic-estimate-data` defines the coordinate data used in the estimate:
smooth charts and frames, a positive smooth volume, local differential expressions and their
symbols, ellipticity, finite localization, and the literal Sobolev and integrated L² norms.
It reuses the Mathlib-leaf manifold, bundle and smooth-section nodes, smooth fibre metrics,
and the existing partition-of-unity node. Its source is Demailly VI (1.1)–(1.4), (1.8), and
the Sobolev setup on pp.287–289, read as described above. Its Lean record lists every helper
declaration with source and blueprint docstrings. Its three logged search kinds are the actual
LeanSearch, LeanFinder and Geometry grep calls described above. Existing nodes about distributions,
tensor bundles and the chart-sum density integral were inspected; none supplies the concrete
coordinate differential expressions or integer localization norm. No distribution theory or
completion is introduced here, so those substantial separate nodes are not duplicated.

The first delivery dry run requested the current schema field `import_flags` on the new node;
an empty list was added. This is the schema enforced by `tools/stage2_delivery.py`
`NEW_NODE_KEYS` (updated 2026-10-23), although the standing brief does not yet list that key.
No Lean or mathematical statement changed for that repair.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
