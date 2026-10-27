## Worker report

The delivery states `EllipticSobolev.exists_elliptic_sobolev_closed_range` in
`Sheaf.Analysis.EllipticSobolevClosedRange`. Its proof is `sorry`; nothing is proved.
The item's natural-language statement and accepted proof are unchanged. Its only extra
statement dependency is `def-sfb-elliptic-sobolev-realization-data`.

I read Demailly's online agbook.pdf, printed pp.288–290: VI (1.4) and (1.4'), the
Sobolev setup, (2.2), (2.3), and the first part of (2.4)(ii), including (2.5) and
(2.6). The source explicitly proves closed range of the Sobolev extension, before
passing to smooth sections. I also read the current latest blueprint direct-images
proof (3). The long analytic prerequisite chain is inherited from the DAG; this
statement does not replace the blueprint unit's route.

Hypotheses and clauses, in order:

- The scalar field is exactly `ℝ`, in the bundles, smooth sections, metrics, linear
  maps, Hilbert structures, coefficients, integrals and distributions. `Field` is
  the exact Mathlib match of `def-weil-field`.
- Dimension and positive order are `m k : ℕ`, `hm : 1 ≤ m`, `hk : 1 ≤ k`.
- `N : Type u`, `ChartedSpace (Model m) N` and
  `IsManifold (𝓘(ℝ, Model m)) ∞ N` give a smooth real manifold with the full
  Euclidean model, hence without boundary. `T2Space` is the usual Hausdorff
  convention for a manifold; `CompactSpace` is precisely compactness. No
  connectedness or nonemptiness is assumed. Second countability follows from
  compactness and the Euclidean chart structure. Borel measurability is recorded
  explicitly by `MeasurableSpace` and `BorelSpace`, not an additional restriction
  on the smooth manifold.
- `d : Base m N` packages the given smooth Riemannian tangent metric, a finite
  oriented chart cover with strictly positive transition determinants, and the
  given positive smooth volume. The volume measure is characterized in every
  smooth chart by a positive smooth multiple of the metric Gram-determinant
  density. The weight is included so that the statement permits a smooth volume
  form independently of the chosen Riemannian metric, as its wording and VI (1.4)
  allow; the metric volume is the case weight one.
- `G H : MetricBundle m r N` use the same `r : ℕ`; all ranks including zero are
  allowed. They contain the Mathlib real vector-bundle and smooth-transition
  structures, and `Bundle.ContMDiffRiemannianMetric` supplies the smooth positive
  fibre metric. `Sections` is an abbreviation for `ContMDiffSection`, not a
  new definition of smoothness.
- `Q : EllipticOperator G H k` contains `op : Sections G →ₗ[ℝ] Sections H`.
  Its `coeff_smooth` and `formula` give exactly the smooth-coefficient local
  differential formula through order `k`. `elliptic` is bijectivity of the
  degree-`k` coefficient polynomial on every nonzero real coordinate covector.
  Equal finite ranks turn this into the required invertibility. Coordinate charts
  range over the maximal smooth atlas; frames come from the smooth bundle atlas.
  Restricting to a common smaller chart is permitted, so the local formula is
  available when both bundles are trivialized.
- `aG : Localization G`, `aH : Localization H` are the chosen finite chart/frame
  families with subordinate smooth partitions of unity and compact support inside
  each chart. They are inputs just as the statement fixes a choice. The energy
  `sobolevEnergy` is the literal finite sum of Euclidean integrals of the squared
  norms of `coordinateDerivative α` of each zero-extended localized section, with
  `∑ j, α j ≤ k`. The finite type `Fin m → Fin (k+1)` lists every such multi-index
  exactly once; the other terms contribute zero.
- The existential `LG : L2Model d G`, `LH : L2Model d H` asserts the Hilbert
  completions exist. Each has a complete real inner product space, a dense linear
  smooth image and exactly the integrated pairing (`pairing`). This is the
  intrinsic specification of the completion of that pre-Hilbert space, up to its
  unique isometry preserving the dense smooth image. A completion is not assumed
  in a hypothesis or chosen from an unspecified existence theorem.
- `representative`, `measurable`, `integrable`, `eq_iff_ae`, `exhaustive` and
  `inner_representative` assert precisely the identification with square-integrable
  measurable sections modulo almost-everywhere equality, preserving the integrated
  pairing. Chartwise almost-everywhere strongly measurable representatives are
  equivalent to measurable representatives modulo null sets in the finite model
  fibre. The representative function itself is used only modulo almost-everywhere
  equality; it is not claimed to be a canonical pointwise representative.
- The existential `SG : SobolevModel aG k LG` and the corresponding realization for
  `H` have complete real inner product structures and dense linear smooth images.
  `norm_ofSmooth` fixes their squared norms to exactly the specified finite-chart
  energies, thus specifying their Hilbert completions, not arbitrary Hilbert spaces.
- `SG.toL2`, `SG.injective`, `SG.smooth_image` give the canonical bounded injective
  inclusion agreeing with the smooth-section identity. Each `L2Model.distribution`
  takes values in Mathlib's genuine continuous local distributions. `regular`
  prescribes the coefficient-distribution integral on every scalar test;
  `injective_distribution` gives injectivity of the assembled local map. These are
  exactly the local-frame meaning of distributional bundle sections used by the
  item. Their usual frame transformation follows from the formula for coefficients
  of the same representative, not from an unconstrained family of distribution
  maps. Composing with `SG.toL2` gives the asserted Sobolev injection. The regular
  formula and smooth representative agreement give the usual smooth images.
- `∃ T : SG.space →L[ℝ] LH.space` is existence of a bounded real-linear extension.
  The first conjunct is its value on every smooth section. The second quantifies
  over every bounded extension with only that agreement, hence uniqueness does not
  depend on additionally assuming closed range or a distributional equation.
- `DistributionalEquation Q LG LH (SG.toL2 u) (T u)` is the local distributional
  equation for every Sobolev section. Its componentwise test formula is
  `∫ φ (Tu)_j = ∑α,l (-1)^|α| ∫ u_l ∂α(φ b_{α,jl})`. The coefficient is inside
  the derivative on tests, which is essential for variable coefficients.
- The final `IsClosed (Set.range T)` is exactly closedness in the target `L²` norm
  topology, with no finite-codimension claim added.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, class signature and docstring.
- `def-sfb-smooth-real-manifold`: `ChartedSpace` and `IsManifold`,
  Mathlib.Geometry.Manifold.ChartedSpace and IsManifold.Basic; exact real Euclidean
  specialization with infinity smoothness, as its Mathlib match records.
- `def-sfb-smooth-real-vector-bundle`: `ContMDiffVectorBundle`,
  Mathlib.Geometry.Manifold.VectorBundle.Basic, together with `FiberBundle` and
  `VectorBundle` assumptions in its full signature.
- `def-sfb-smooth-bundle-sections`: `ContMDiffSection`, its pointwise additive-group
  and module instances, Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection.
- The definition module additionally uses the existing `ContMDiffRiemannianMetric`,
  `SmoothPartitionOfUnity`, `TestFunction` and `Distribution`; it does not introduce
  private replacements for those notions.
- The stated proof dependency `lem-sfb-compact-remainder-coercivity` is imported from
  Sheaf.Analysis.CompactRemainderCoercivity. I read its full theorem and proof-plan
  docstring, including its sequential compactness hypothesis and kernel-complement
  estimate.
- The Mathlib proof leaves are imported via Analysis.Normed.Operator.Extend
  (`LinearMap.extendOfNorm`, agreement, bound and uniqueness) and
  Analysis.InnerProductSpace.Projection.Basic
  (`Submodule.exists_add_mem_mem_orthogonal`). Their recorded signatures were read.
- The Sobolev-Rellich and global Gårding nodes currently have no Lean modules; their
  mathematical steps remain explicitly in the proof-plan docstring. No fictitious
  imports or new theorem restatements were added for these proof-only prerequisites.

Edge cases checked before and after writing: empty `N` admits empty chart/partition
families and zero completion spaces; `r = 0` has zero fibres, and the unique linear
map on the zero fibre is bijective, so ellipticity remains meaningful; `k = 1` is
included without changing multi-index bounds; disconnected bases have no extra
restriction; a nontrivial elliptic kernel is allowed (no coercivity or injectivity
hypothesis on `Q`). The derivatives of order zero are included once. Only covector
zero is excluded. The two universes `u v` for the base and fibres are explicit; the
completion carrier uses `Type (max u v)`, sufficient for the original section space
and its metric completion. No auto-implicit variables or file-local notation occurs.

Searches actually run:

1. msearch LeanFinder: “An elliptic differential operator on smooth real vector
   bundles over a compact manifold extends uniquely from Sobolev Hk to L2 with
   closed range”. Eight hits, including IsCoercive.isClosed_range and
   LinearMap.extendOfNorm_unique; no geometric Sobolev result.
2. msearch Loogle: `ContMDiffSection, UniformSpace.Completion`: zero hits.
3. msearch grep: `Sobolev|[Ee]lliptic|[Rr]ellich`, Analysis/: seventeen hits about
   Euclidean Bessel potential spaces, Sobolev inequalities and unrelated elliptic
   matrices/functions; no bundle completion or closed-range theorem.
4. msearch LeanSearch: “Completion of smooth sections of a real vector bundle in an
   integrated L2 inner product and local derivative Sobolev norm”: smooth section
   and Riemannian pairing hits, no completion.
5. The new node records the full outputs of its further LeanSearch, LeanFinder and
   grep queries, exactly as returned. LeanSearch found local smooth-frame and
   section declarations; LeanFinder found smooth metric and partition lemmas.
6. `rg` in WeilConjectures and Sheaf for Sobolev/elliptic/Rellich, for the item id,
   and for the chosen names. Existing analytic modules provide Euclidean weak
   derivative and Rellich results, not this notion or statement; there was no
   declaration with any chosen fully qualified name. The upstream name map had
   no elliptic/Sobolev attachment for this item.
7. DAG searches found the existing smooth manifold, bundle and section definition
   nodes and the more elaborate global test-density framework. The latter is not
   copied here: the item's explicitly local-frame distribution language is rendered
   with Mathlib's local `Distribution` and its actual regular integral formula.
   The Sobolev-Rellich and Gårding nodes are theorems, not existing definitions of
   this completion interface. `blueprint_refs.py search Sobolev` returned zero;
   `search elliptic` returned six unrelated substring matches. None states this
   notion. `ancestor` returns `None`, so the new node preserves that inherited null
   ancestor and the complete inherited via chain with the item prepended.

Validation: both modules compiled separately in dependency order with scompile.py on
the server against the published live library, with no errors or non-sorry warnings.
The first deliver2.py dry run passed compilation and required the current server schema
field `import_flags` on the new node. I added the empty list and reran the dry run.
There is no statement dispute, statement correction or unusable recorded dependency.

## New nodes

`def-sfb-elliptic-sobolev-realization-data` owns
`Sheaf.Analysis.EllipticSobolevData`. It defines the localized energy and the precise
Hilbert-completion/measurable/distributional realization specifications, and packages
the elliptic local differential formula. These are the missing interface for the
item, sourced at Demailly VI §§1–2, pp.287–290. It uses the existing manifold, bundle,
section, metric, partition and local-distribution definitions. All its fields and
functions are real data or explicit formulas, with no sorry or arbitrary existence
choice. In particular the definitions contain no existence theorem and assert no
existence of the specified realizations; their existence is part of the item's
conclusion. The exact dense-image pairing/energy formulas determine each completion
up to its unique canonical isometry. The local integral formula and dense smooth
agreement determine the canonical maps, so no arbitrary-map hypothesis replaces a
construction. Three kinds of search and the DAG/blueprint searches above found no
existing node for this combined realization interface. The new node's `lean` record
lists every helper declaration, all documented with this node's source and id.

## Second reading by Q01

This is an independent clause-by-clause reading of the unchanged node statement against
`EllipticSobolev.exists_elliptic_sobolev_closed_range` and the helper module
`Sheaf.Analysis.EllipticSobolevData`. The maintainer review wrote it. The delivered
section was the author's own re-reading, with no separate reader, and this section
replaces it.

Node clauses and their Lean rendering:

1. Over ℝ [def-weil-field]: all scalars are `ℝ`. This is exact.
2. N is a compact oriented smooth m-manifold without boundary, m ≥ 1. The Lean has
   `ChartedSpace (Model m) N` and `IsManifold 𝓘(ℝ, Model m) ∞ N`, with the full Euclidean
   model and so no boundary. It has `T2Space` and `CompactSpace`, and `hm : 1 ≤ m`.
   Orientation is `Base.oriented`: a finite cover by maximal-atlas charts whose transition
   derivatives have positive determinants. `MeasurableSpace`/`BorelSpace` only fix the
   Borel σ-algebra. This is exact.
3. A smooth Riemannian metric and a volume form give `Base.metric`
   (`ContMDiffRiemannianMetric` on the tangent bundle) and `Base.measure`. The measure is
   pinned in every maximal-atlas chart to `weight · √det(g_ij) · Lebesgue` on the target,
   with `weight` smooth and positive. This is a positive smooth volume and is not an
   arbitrary measure. With the Borel hypothesis the chart map is AEMeasurable on the
   restricted measure, so the `Measure.map` is not degenerate. This is exact, and it covers
   a volume form that differs from the metric volume.
4. G and H have the same finite rank r and smooth positive fibre metrics. They are
   `MetricBundle m r N` with a common `r`, built on Mathlib's
   `FiberBundle`/`VectorBundle`/`ContMDiffVectorBundle` and `ContMDiffRiemannianMetric`.
   r = 0 is allowed. Fibre universe v and base universe u are free. This is exact.
5. Q is real-linear of order ≤ k (k ≥ 1) with smooth coefficients, and its degree-k
   principal symbol is invertible at every nonzero real covector. This is
   `EllipticOperator.op : Sections G →ₗ[ℝ] Sections H` with `coeff`, `coeff_smooth`
   (`ContDiffOn` on the chart target) and `formula`. `formula` is
   `Qs = Σ_{|α|≤k} b_α ∂^α s` in every chart carrying frames of both bundles. Each
   multi-index with |α| ≤ k occurs once through `Fin m → Fin (k+1)`. `elliptic` is
   bijectivity of `Σ_{|α|=k} ξ^α b_α(z)` for ξ ≠ 0. The coefficients are determined on each
   chart by `op` through `formula`, so the symbol condition cannot be faked. With equal
   ranks, bijectivity is invertibility. `hk : 1 ≤ k`. This is exact.
6. L²(B) is the Hilbert completion of the smooth sections in ∫|u|²dV, identified with
   measurable square-integrable sections modulo a.e. equality, and it is complete for the
   integrated pairing. This is `L2Model d B`: a complete real inner-product space, a dense
   linear image of smooth sections, and `pairing` = `l2Pair`, the integrated fibre metric.
   `representative`, `measurable`, `integrable`, `inner_representative`,
   `smooth_representative`, `eq_iff_ae` and `exhaustive` give exactly the identification
   with measurable L² sections modulo a.e. equality. Dense image plus the pairing determine
   the model up to a unique isometry fixing smooth sections. The structure is satisfiable
   (by the honest L² space), and all its fields are true properties of it. This is exact.
7. H^k(B) is the completion in the finite-chart, partition-of-unity norm (squared Euclidean
   L² norms of all localized derivatives through order k, summed). This is
   `SobolevModel a k L`, whose dense image has squared norm exactly `sobolevEnergy a k`.
   `sobolevEnergy` is the literal sum over charts and over |α| ≤ k of
   `∫ ‖∂^α(χ_i∘φ_i⁻¹ · frame coefficients)‖²` over ℝ^m, with zero extension off the chart.
   The localized function is compactly supported inside the chart target, hence globally
   smooth, so the `fderiv` iterates are the classical derivatives. The norm is definite
   because Σχ_i = 1. This is exact.
8. The canonical injections H^k ↪ L² ↪ D' fix the usual images of smooth sections.
   `SobolevModel.toL2` is continuous, injective and identity on smooth sections.
   `L2Model.distribution` lands in Mathlib's `Distribution` on each chart target, is pinned
   by `regular` (∫ φ · frame coefficients of the representative, Lebesgue measure) and is
   jointly injective. Coefficients of an L² section are L²_loc for Lebesgue (positive
   continuous chart density), so the pairing is defined on compactly supported tests.
   This is exact.
9. The conclusion has three parts: Q extends uniquely to a bounded T_Q : H^k(G) → L²(H),
   T_Q u agrees with the distributional Qu, and the range is closed. The Lean gives
   `∃ T : SG.space →L[ℝ] LH.space` with agreement on smooth sections. Uniqueness is over
   all continuous T' with that agreement only. `DistributionalEquation` holds for every u.
   Its test formula `∫ φ (Tu)_j = Σ_α (-1)^{|α|} ∫ Σ_l u_l ∂^α(φ b_{α,jl})` is the transpose
   rule with the variable coefficient inside the derivative; the sign and placement are
   correct. The φ·b product vanishes near every point outside tsupport φ ⊆ target, so it is
   smooth even though b is only smooth on the target. The final part is
   `IsClosed (Set.range T)`.
   The models are existentially quantified in the conclusion, not assumed. They are unique
   up to isometries fixing smooth sections, and T is determined on a dense image, so the
   statement is model-independent and not weaker than the node. The extra existence of the
   H^k(H) model is true and harmless.

Edge cases:
- N empty: the charts, partition and models are zero.
- r = 0: the symbol on the zero fibre is bijective and the sum over j is empty.
- k = 1, and α = 0 included once.
- A disconnected N, a nontrivial kernel, a non-metric volume weight.
- Universes u and v are independent, and the carriers are in `Type (max u v)`, where the
  section space lives. There is no silent restriction.

Records: the item differs from live only in `lean` and the added stmt_dep. Both
`lean.statement` fields are verbatim in their files. The proof is `sorry` only, and the
docstrings carry Demailly VI §§1–2 and the blueprint ids, with the five proof steps. The
new node `def-sfb-elliptic-sobolev-realization-data` lists 15 declarations, all real data
or formulas, none hollow.

H4 search: NO's `def-sfb-bundle-sobolev-space` (`BundleSobolev.L2`/`H`, weak-derivative
spaces with no Hilbert structure) landed at 13:18 CST. That is after this delivery's base
(blueprint index 05:08 UTC = 13:08 CST). It uses a different namespace and has no name
clash. Mathlib has only Euclidean/Bessel Sobolev spaces. Consolidation is a maintainer
note, not a fault of this delivery.
