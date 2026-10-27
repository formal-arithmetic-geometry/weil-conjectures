## Worker report

The item is stated by
`RealEllipticBundle.hasSmoothRepresentative_of_elliptic_weakEquation` in
`Sheaf.Analysis.EllipticAdjointRegularity`. Its only proof is `sorry`.
The item statement is unchanged. One new definition node supplies the missing finite-order
real operator and coordinate weak-equation interface; no analytic theorem is assumed in
that interface. Every variable and universe is bound explicitly, with `autoImplicit false`.

Clause-by-clause correspondence:

- All vector spaces are real: the base and fibre models are
  `BundleSobolev.Model`, namely `EuclideanSpace ℝ (Fin m)` and
  `EuclideanSpace ℝ (Fin q)`; the operator and all matrices are over `ℝ`.
  The field dependency is Mathlib `Field`, read in `Algebra/Field/Defs.lean:180`.
- Dimension at least one is `m` and `hm : 1 ≤ m`. `N : Type u`, `TopologicalSpace`,
  `ChartedSpace (Model m)`, `IsManifold 𝓘(ℝ, Model m) ∞ N`, `T2Space` and
  `CompactSpace` specify the compact Hausdorff smooth manifold. The self model is
  boundaryless. No connectedness, inhabitedness, or independent size bound is imposed.
  A compact Hausdorff locally Euclidean manifold has a finite coordinate subcover and
  is second countable; that consequence is not added as a hypothesis here.
- The orientation is `orientation : OrientedAtlas m N`. Its charts belong to the
  **maximal** smooth atlas, cover `N`, and have positive real transition determinants.
  It does not require the arbitrarily supplied initial atlas to be oriented.
- The smooth tangent Riemannian metric is exactly Mathlib
  `ContMDiffRiemannianMetric … (fun x ↦ TangentSpace … x)`, argument `g`.
  The volume form is `μ : SmoothVolume m N`: positive smooth local densities and
  the chartwise measure equality specify the actual integrated volume. The item says
  “metric and volume form”, not “its metric volume”; arbitrary smooth positive volume
  is therefore retained. On compact `N` its density ratio to metric volume is bounded
  above and below, so the proof route using metric Sobolev norms still applies.
  `MeasurableSpace` with `BorelSpace` is the measurable structure of this same topology.
- `G : MetricBundle.{u,v} m q N`, `H : MetricBundle.{u,w} m q N` use one shared finite
  rank `q`, but independent fibre universes. `FiberBundle` and `VectorBundle` are
  Mathlib's, `ContMDiffVectorBundle ∞` gives the smooth transition functions, and
  `InnerProductSpace ℝ` with `IsContMDiffRiemannianBundle … ∞` supplies the smooth
  positive definite fibre metrics. These structures are packaged, not redefined.
- `Q : DifferentialOperator G H k`, `hk : 1 ≤ k`, gives the specified real-linear map
  on actual `ContMDiffSection … ∞` spaces. Its `coefficient`, `smooth`, and `expression`
  fields give the displayed local matrix differential expression through degree `k`.
  The finite bounded-index enumeration includes every multi-index of total degree at
  most `k` once. The common chart/frame domains contain their indexing point, so cover
  the whole base; no global trivialization of either bundle is required.
- `hQ : Q.IsElliptic` requires `IsUnit` of the degree-`k` symbol matrix for every point
  and every nonzero real cotangent coordinate vector. Its formula is exactly the
  degree-`k` coefficient sum, with no factor of `i`. Matrix invertibility is equivalent
  to invertibility of the finite-dimensional fibre map in these two frames.
- `u : BundleSobolev.L2 (q := q) G.Fiber μ.measure` is the **published** dependent
  almost-everywhere quotient with an almost-everywhere measurable square-integrable
  representative. The integrated norm is the norm from the specified fibre inner product.
- `hQu : ∃ f : Sections H, Q.WeakEquation μ.measure u f` says that the local coefficient
  distribution of `Qu` equals that of a smooth section. Explicitly, every output
  component and every compact smooth real coordinate test satisfy
  `∫ f_a φ = Σα,b (-1)^|α| ∫ u_b ∂^α(b_α,ab φ)`.
  The coefficient is **inside** the derivative on the test. This is the distributional
  action of the given variable-coefficient expression; it is not an arbitrary extension
  map. The pairings are with coordinate Lebesgue measure, appropriate to coefficient
  distributions, not with an extra volume density. Smooth positive densities have the
  same local null sets as Lebesgue measure, so use of `Quotient.out` loses no class and
  changes none of these integrals.
- The conclusion `HasSmoothRepresentative G μ.measure u` expands to existence of a
  `ContMDiffSection … ∞` equal almost everywhere to the representative of the **same**
  dependent quotient. This is precisely the requested equivalent conclusion. It imposes
  no additional uniqueness or norm estimate.

Dependency declarations read and used:

- Mathlib `IsManifold`, `IsManifold.maximalAtlas`, `ChartedSpace`,
  `ContMDiffVectorBundle`, `FiberBundle`, `VectorBundle`, `ContMDiffSection`,
  `ContMDiffRiemannianMetric`, and `IsContMDiffRiemannianBundle`, in their
  `Geometry/Manifold/…` source modules. The full section and metric signatures and
  docstrings were read, including the pointwise module operations and metric positivity.
- `Sheaf.Geometry.Manifold.BundleSobolevSpace`: `BundleSobolev.Model`,
  `BundleSobolev.L2`, and `BundleSobolev.multiPartial`. The definition node
  `def-sfb-bundle-sobolev-space` landed while this worker was running; its module was
  absent locally, so I read the full live source with `scompile.py --source` and removed
  the draft duplicate quotient and derivative before delivery.
- `SmoothPartitionOfUnity.exists_isSubordinate` in
  `Mathlib.Geometry.Manifold.PartitionOfUnity`, proof dependency
  `lem-sfb-smooth-subordinate-partition`: full hypotheses and conclusion read at lines
  550–555. It is imported without `public` for the proof plan.
- `BundleSobolev.existsUnique_contMDiff_representative` in
  `Sheaf.Geometry.Manifold.BundleSobolevEmbedding`: full live source read using
  `scompile.py --source`, including metric-volume, finite localization and strict
  `r + m/2 < t` hypotheses and equality in the original dependent quotient. This newly
  landed proof-dependency module is imported without `public`.
- The formal-adjoint-symbol and weak-Gårding proof dependencies have no Lean record
  at the final dependency check. Their steps are preserved in the complete proof
  docstring, but no fictitious import or assumption replaces them.

Edge cases inspected: empty `N` is permitted and gives the empty section; `q=0` is
permitted and gives the unique zero section (the empty square matrix is a unit);
`m=1`, `k=1`, and odd `k` retain the correct weak sign; the `α=0` summand differentiates
zero times; nontrivial kernels and zero right-hand side are allowed; disconnected bases
and nontrivial/nonisomorphic equal-rank bundles are allowed. No degree-zero operator
case is silently substituted for `k≥1`. Coordinate/frame intersections remain open
neighborhoods of the indexing point, so the test condition is not vacuous.

The source PDF was downloaded only into this sandbox's `scratch/`. I read Demailly
printed pp.288–290: (1.5)–(1.7) give the formal adjoint and its sign; (1.8) defines
ellipticity; §2 explicitly assumes the compact Riemannian base; (2.1) is Sobolev
embedding and (2.3) explicitly starts with only an L² distributional solution. The
node's two-bundle block argument reduces exactly to that single-bundle estimate.
No statement correction or STATEMENT-DISPUTED flag is needed.

Searches performed through the prescribed `msearch.py` wrapper:

- LeanFinder: “An L2 distributional section satisfying a smooth elliptic differential
  equation on a compact manifold has a smooth representative”: eight hits, smooth
  section existence/approximation and complex differentiable constancy, no regularity.
- Loogle: `ContMDiffSection, Bundle.ContinuousLinearMap, Distribution, RiemannianMetric`:
  no hits; unknown `Bundle.ContinuousLinearMap`.
- Mathlib grep `elliptic|hypoellipt|Garding|Gårding` in `Analysis/`: elliptic functions,
  upper-half-plane fixed points, and the bibliography of the Euclidean Sobolev module;
  no elliptic-regularity theorem.
- LeanSearch: “smooth differential operator between real vector bundles local coefficients
  distributional equation”: smooth local frames, hom-bundle maps, and section operations;
  no finite-order weak-operator interface.
- Additional new-interface LeanSearch, LeanFinder, and Mathlib grep queries and their
  **verbatim** outputs are recorded in the new node's `mathlib_searches`.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for elliptic, principal-symbol,
  weak-equation, Riemannian and L² interfaces found the analytic Fourier prerequisites,
  complex Hermitian-specific geometry, and the first-order complex weighted-adjoint
  formula; no matching theorem or arbitrary-order real interface. The prescribed
  `grep -rn 'lem-sfb-elliptic-adjoint-regularity' lean/WeilConjectures` found nothing.
- DAG definition grep and `tools/blueprint_refs.py search` for “weak elliptic”,
  “L2 sections” and “elliptic differential operator”: no blueprint hits. Existing
  `def-sfb-smooth-bundle-test-distributions` is a global strong-dual construction and
  does not give a finite-order operator or its weak equation. It is not copied here.

Validation: both files are compiled separately by `scompile.py`, against the live
published build and its private source overlay. No local or global build was run.

## New nodes

`def-sfb-elliptic-weak-bundle-equation` owns
`Sheaf.Geometry.Manifold.EllipticWeakBundleEquation`. It packages existing Mathlib
smooth metric-bundle structures and specifies the missing orientation/positive volume,
local finite-order real operator, exact principal symbol, and coordinate distributional
weak equation. It refers to the existing manifold, real bundle and smooth-section DAG
nodes and the newly published bundle Sobolev node. Source: Demailly VI §§1–2,
printed pp.287–289. Its three search kinds, direct project/DAG checks, and negative
results for the missing interface are recorded verbatim in `mathlib_searches`. Neither
a global distribution dual nor an L² quotient is redefined. The only quotient
representative selected is `Quotient.out` of an already defined class, never a choice
from a postponed existence theorem. Every definition has real data and there is no
helper theorem or hidden `sorry` in the definition module.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
