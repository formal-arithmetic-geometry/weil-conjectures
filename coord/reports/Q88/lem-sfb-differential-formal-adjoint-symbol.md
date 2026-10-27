## Worker report

The delivery states `SmoothDifferentialOperator.exists_unique_formalAdjoint_symbol` in
`Sheaf.Analysis.Calculus.DifferentialFormalAdjointSymbol`. Its only postponed theorem is
that declaration; its proof is `sorry`. The two auxiliary definition modules contain
concrete definitions only. No theorem is proved and no object is chosen from a postponed
existence statement.

Source read: Demailly, Complex Analytic and Differential Geometry, June 21, 2012,
I §1.A (printed p.7) and VI §1 (printed pp.287–289), from the exact online PDF named
in the node. The PDF was downloaded into the worker sandbox for inspection; it is not
part of the delivery. I also read the current blueprint unit and its direct-images proof,
including part (3), in literature/blueprint/latest. This analytic supporting node is not
the unit's own statement. The inherited null blueprint ancestor is preserved, and the
new nodes use the ancestor returned by blueprint_refs (null), with the full inherited via.

Hypothesis and clause correspondence:

* Real scalars: all section spaces and all coefficient and operator linear maps use ℝ.
  The existing dependency `def-weil-field` is Mathlib `Field`, read at
  Mathlib/Algebra/Field/Defs.lean:180; the standard field here is ℝ.
* The dimension is `m : ℕ` with `hm : 1 ≤ m`. The base has
  `ChartedSpace (Fin m → ℝ) M` and `IsManifold (𝓘(ℝ, Fin m → ℝ)) ∞ M`,
  the identity model without boundary or corners. `T2Space M` and
  `SecondCountableTopology M` spell out Demailly's standing manifold convention.
  `MeasurableSpace M` with `BorelSpace M` specifies the Borel structure used for integration,
  without restricting the possible underlying topological manifolds.
* Orientation and positive smooth volume: `dV : Manifold.OrientedSmoothVolume (m := m) M`.
  Its covering charts are in `IsManifold.maximalAtlas`; positive transition determinants
  give orientation. Its densities are `ContDiffOn ℝ ∞` and strictly positive. The
  `map_measure` field is precisely the chart formula for integrating against that volume
  form. Its measure is the concrete measure argument of both Bochner integrals.
* Bundles G and H: `FiberBundle`, `VectorBundle ℝ`, `ContMDiffVectorBundle ∞`, and
  `FiniteDimensional ℝ F/K`. These use Mathlib's bundle notion, not a duplicate.
  The model fibres and actual fibres have independent explicit universes `v,w,v₁,w₁`;
  the base has universe `u`. No equality of these universes is imposed.
* Smooth positive definite fibre metrics: `InnerProductSpace ℝ (G x)/(H x)` on the
  normed fibres, and `IsContMDiffRiemannianBundle ... ∞ F G` / `... K H`.
  I read that class's full signature and docstring in
  Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:64–69. It says that the actual
  inner products vary smoothly, rather than postulating arbitrary pairings.
* Smooth global sections: the existing Mathlib `ContMDiffSection I F ∞ G` and its
  pointwise module structure, read in VectorBundle/ContMDiffSection.lean:290–398.
* `d : ℕ` includes d=0. Q is a genuine `→ₗ[ℝ]` between these smooth section spaces;
  `hQ : IsSmoothDifferentialOperator d Q` is the local finite differential expression.
  The definition uses exactly multi-indices of total degree at most d and smooth
  continuous-linear-map-valued coefficients on an open neighborhood of every point.
  Finite dimensionality makes this the usual smooth matrix coefficient condition.
  The operator predicate uses the bundle's existing preferred smooth frames and charts;
  existence of such expressions is invariant under replacing these by other smooth
  charts or frames, by the ordinary finite chain and product rules.
* The existential R is another real-linear map in the reverse direction, with
  `IsSmoothDifferentialOperator d R`. Thus its values really are smooth sections and
  its coefficients really have the required order bound.
* `IsFormalAdjointFor (m := m) dV.measure Q R` quantifies over both smooth sections.
  Its premise is the disjunction that the closure of the nonzero locus of either
  section is compact. For dependent sections this is the direct definition of compact
  topological support. Its conclusion is exactly the displayed equality of real
  integrals of the two fibre inner products. There is no L² assumption on either
  individual section. Demailly allows the more general compact intersection of supports;
  this node explicitly asks only for the two cases in that disjunction, which are retained.
* `coordinateSymbol b y ξ` is the actual finite sum `∑ b_α(y) ξ^α` for `|α|=d`.
  `presentationSymbol` composes it with the actual frame and inverse-frame maps.
  The theorem quantifies over EVERY local presentation b of Q and c of R at p,
  and over all coordinate covectors ξ and fibre vectors a,z. Its equation is
  `⟪a, σ_R ξ z⟫ = (-1)^d * ⟪σ_Q ξ a,z⟫`. Nondegeneracy of the positive definite
  real fibre metric makes this exactly `σ_R = (-1)^d σ_Q^*`. This is a coordinate
  rendering of the fibre map identity, not a chosen or unconstrained symbol map.
  In orthonormal frames the defining equality is ordinary matrix transpose.
* The last quantified S is any real-linear smooth differential operator of order at
  most d satisfying the integration identity; it concludes S=R, without assuming
  the symbol formula for S. Thus uniqueness is not conditional on the extra conclusion.
* No `CompactSpace`, finite measure, completeness, Riemannian metric on the base,
  or positive rank hypothesis is present. Only the source's standing Hausdorff and
  countable-basis assumptions are made explicit (see the correction below).

Dependencies used: `Mathlib.Geometry.Manifold.IsManifold.Basic` (`ChartedSpace`,
`IsManifold`, `IsManifold.maximalAtlas`), `Mathlib.Geometry.Manifold.VectorBundle.Basic`
(`ContMDiffVectorBundle`), `Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`
(`ContMDiffSection` and its module structure), and the Riemannian class above. These are
the declarations of the existing manifold, bundle, and section DAG nodes. The new
volume and differential-operator declarations are imported publicly. Proof dependencies
are imported without `public`: CoordinateWeightedAdjoint (its full statement and
proof docstring read), Measure/OpenPos (`Measure.eqOn_open_of_ae_eq`), LocallyIntegrable
(`ContinuousOn.locallyIntegrableOn`, `Continuous.integrable_of_hasCompactSupport`),
Jacobian (`integral_target_eq_integral_abs_det_fderiv_smul`), BumpFunction/InnerProduct
(the Euclidean smooth bump and support API), ContDiff/Operations (`ContDiffOn.inv`),
PartitionOfUnity (`SmoothPartitionOfUnity.exists_isSubordinate`), and
AEEqOfIntegralContDiff (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). I read
the recorded signatures in their source files. The theorem docstring contains all nine
DAG proof steps, including local construction, integration by parts, test separation,
cutoff uniqueness, overlap transformation, gluing, partition assembly, top coefficients,
and global uniqueness.

Edge cases checked before writing: d=0 gives only the zero multi-index, no derivatives,
and sign 1. If the actual order is smaller than d, all degree-d coefficients vanish.
If either rank is zero, all the relevant fibre maps and section operators are zero;
there is no nonempty-index hypothesis or inverse matrix in the definitions. Empty M is
allowed: the local and symbol quantifiers are vacuous, and the section spaces have a
single element. ξ=0 is included (in particular the order-zero symbol need not vanish).
For the scalar ∂/∂x at d=1 the pairing gives the negative derivative symbol, confirming
the sign and the absence of a factor of i. Noncompact examples such as ℝᵐ are included;
only the support of one input is compact. No statement dispute remains.

Searches actually run: msearch LeanFinder for the formal-adjoint/signed-transpose
statement returned metric and abstract LinearPMap adjoint hits, none an exact match;
Loogle `ContMDiffSection, Bundle.Trivialization` returned no hits; grep
`DifferentialOperator|principalSymbol|VolumeForm` in Geometry/Manifold returned no hits.
LeanSearch for smooth differential operators and volume densities returned the existing
smooth-section/metric APIs used here. The two new nodes carry the exact search-log
records of their own three search kinds. Additional direct rg searches in Mathlib,
WeilConjectures and Sheaf found only CoordinateWeightedAdjoint's complex first-order
expressions and abstract Hilbert-space adjoints. The exact item-id search in
WeilConjectures had no hit. I searched dag/nodes by the concepts and read the existing
smooth bundle/section and density-line/integral nodes; none defines a positive smooth
volume form with its associated measure or a differential operator on smooth sections.
The pseudodifferential-operator node was also read: it defines a different notion, acting
on distributions. blueprint_refs searches `differential operator`, `principal symbol`,
`volume`, `volume form`, and `smooth bundle` returned no match.

Validation: every delivered file was compiled with scompile.py, separately in dependency
order. The two definition modules and the main theorem compile cleanly under the normal
60-second limit (about 2 seconds per file); only a sorry proof is postponed.

## New nodes

`def-sfb-oriented-smooth-volume` defines an oriented covering smooth atlas, its positive
smooth volume densities and their coordinate-compatible Borel measure. Source: Demailly
VI §1 before (1.4), printed p.288. LeanSearch and LeanFinder found the volume form of a
single oriented inner product space, not a manifold volume form; the source of
`Orientation.volumeForm` was read. Mathlib `Measure.withDensity` is reused. Grep of the
manifold library and direct project searches found no match. Existing density-line and
compact chart-sum-integral nodes give neither this orientation nor this positive volume
measure, and are not duplicated. The node cites the existing manifold and field nodes.

`def-sfb-smooth-differential-operator` defines coordinate mixed partials and differential
expressions, the local-presentation predicate and smooth differential-operator predicate,
and the degree-d coordinate/fibre symbol. Source: Demailly VI §1 (1.1)–(1.2), printed
pp.287–288. LeanSearch, LeanFinder and grep found section operations or manifold-map
differentials, not this notion. The complex first-order coordinate helper cannot express
an arbitrary-order operator on a nontrivial real bundle. Existing manifold, bundle and
section nodes are cited and their Mathlib declarations reused. There is no choice of
coefficients from an existence theorem: the symbol helper takes the actual coefficients
as arguments, and the main theorem quantifies over all valid presentations.

## Statement corrected

The old statement was the same formal-adjoint and symbol assertion with “oriented smooth
manifold” left unexpanded. The verbatim old statement is preserved in
`statement_change.old_statement`. The precise correction adds “Hausdorff second-countable”
and references to the already existing smooth manifold/bundle notions and the two new
notions. Demailly I §1.A, printed p.7, explicitly assumes both Hausdorffness and a
countable basis for every manifold; this applies to VI §1. Mathlib's `IsManifold` itself
contains neither, so leaving these unrecorded would silently add hypotheses in Lean.
Compactness is still not assumed. No mathematical conclusion or proof step was changed,
and the blueprint unit statement was not altered.

The complete citer audit, from all DAG files whose stmt_deps or proof_deps contain this
item, is:

* `lem-sfb-elliptic-adjoint-regularity`: holds. Its compact smooth base is under the same
  standing Demailly manifold convention; it uses precisely the reverse operator, order
  bound and signed symbol for the block operator. The clarification preserves that use.
* `lem-sfb-elliptic-global-garding-estimate`: holds. Its compact smooth base and local
  finite-atlas use are under the same convention. It uses the same formal adjoint and
  signed symbol, including empty and zero-rank cases; those remain present.

Neither citer is edited. The original proof and proof_deps are unchanged.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
