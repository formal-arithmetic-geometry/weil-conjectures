## Worker report

The delivery states `WeilConjectures.IntegralStratumCharts.integral_stratum_chart_restrictions`
in `Sheaf.Paper.IntegralStratumChartRestrictions`. Its proof is the sole `sorry`.
The supporting structures spell out all the chart assertions; their fields are conclusions,
not hypotheses of the theorem. The node changes only in `lean`.

The coefficient presentation is important. `pbcIntegralDatum l E` has coefficient ring
`PbcIntegralRing l E`, the canonical universe lift of the recorded valuation ring.
Its completed ring is the actual limit of its finite coefficient sheaves.
`ImmersionCompletedPullback.completedRingIso` identifies it with the node's completed
integral ring, with every quotient projection specified. `transport` is restriction along
the inverse of that ring isomorphism. Thus `constructible` is literally the recorded
`sfIntegralConstructible` predicate after this exact coefficient transport, not a new
constructibility condition. Quantifying over its full subcategory quantifies over the same
integral objects and all their morphisms. The coefficient transport is an equivalence;
it imposes no condition on those objects.

Hypotheses and clauses, in the order of the node:

- Prime and coefficient field: `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The coefficient datum uses the
  recorded integer ring, chosen uniformizer, positive quotient system and transitions.
  A level `n : ℕ` is exponent `n+1`; no positive exponent is omitted.
- Schemes and morphism: `{X W : Scheme.{u}} (h : W ⟶ X)`.
  `[IsNoetherian X] [IsNoetherian W]` are the Mathlib scheme conditions, equivalent
  to finite affine covers by Noetherian rings (`isNoetherian_iff_of_finite_affine_openCover`).
  `_hXdim` and `_hWdim` are finite bounds on `topologicalKrullDim`.
  `_hXl` and `_hWl` assert that l is a unit in the global section rings; this is
  invertibility of l on the schemes, including their local and residue rings.
- The completed coefficients and ambient derived categories are `pbcAdicCompletion` and
  `PbcCompletedDerived`. Their small site remains `Scheme.ProEt`: objects have universe
  u+1 and morphisms universe u. Modules have coefficient size u+1. No site universe
  equality or size collapse is introduced.
- For every integral constructible K: the first conjunct quantifies over
  `(constructible l E X).FullSubcategory` and asserts `Nonempty (Charts l E h K.obj)`.
- The finite locally closed scheme partition is `Charts.strata`, using the dependency's
  `Scheme.FiniteLocallyClosedStratification`. `constructibleStrata` supplies the
  constructibility that the dependency's general partition does not itself require.
  Its fields give finite indexing, actual immersion domains, image equality, pairwise
  disjointness and covering of X.
- On each stratum the family is `index`, `object`, and `covering`. Its objects lie in
  that stratum's actual `ProEt`; the sieve of their arrows to the terminal object is
  covering in `ProEt.topology`. Thus these are pro-etale covering families.
- `Model.complex` is an actual cochain complex of modules over the lifted valuation
  ring. `lower`, `upper`, `boundedBelow`, `boundedAbove`, `projective` and `finite`
  give a bounded finite-projective representative. These are the witness data of
  the recorded `DerivedCategory.IsPerfectRingComplex`, rather than another definition
  of perfectness or an unspecified perfect object.
- `Model.comparison` identifies the iterated ordinary inverse images along i and v
  with `integralConstantDerived` of that actual complex on the chart scheme. This
  published functor is the ordinary completed-constant realization. On the bounded
  finite-projective representative it is termwise `B_V ⊗_underline(R) underline(P)`;
  no arbitrary scalar-extension functor or constant/completed-ring identification
  has been substituted.
- `ExactRestriction` gives ordinary exact module inverse image with the canonical
  completed-ring transport. `finiteLimits` and `finiteColimits` give exactness;
  `limits` gives countable products as well as the relevant small limits.
  `ringProducts`, `coefficientLimit`, and `coefficients` give the ring-sheaf product
  and coefficient-limit preservation and the actual finite projection identities.
- Its `roos` field gives a uniquely coordinate-normalized isomorphism on every strict
  tower of complexes: the existing canonical product comparison appears on both
  coordinates of the actual shifted cone. Uniqueness of these coordinates makes
  these isomorphisms natural in strict tower maps; applying product projections
  intertwines the actual transitions. `derivedLimit` concerns the actual
  constant-tower/derived-limit adjunction mate, not a separately chosen endpoint iso.
- `ExactRestriction.completed` is the published `IntegralCompletedComparison.Comparison`,
  retaining all finite-generator, projection, representative and shift normalization
  clauses. `comparison`, `naturality`, and `normalization` identify ordinary
  restriction with the specified integral pullback: the comparison followed by the
  actual completion unit equals gamma. In particular it is compatible with the
  same finite reductions, because gamma's `projections` clause fixes those quotient
  projections, and the ordinary-to-completed arrow is the actual completion unit.
  There is no freely chosen finite comparison. `preserves` records constructibility.
- `ExactRestriction.cohomology` is a natural isomorphism of functors in every integer
  degree, using `DerivedCategory.homologyFunctor`. `Model.bounds` says precisely that
  every vanishing cohomology outside any interval of K also vanishes for the scalar
  chart model. It does not impose that interval on the terms of P.
- The actual pulled-back stratification is the declaration `Charts.pulledStrata`:
  convert the chosen partition with its constructibility proofs to the existing
  `Scheme.Stratification` interface, then use its published `.pullback h` construction.
  Its domains are `pullback (strata.immersion a) h`, its immersions are the second
  projections, and its strata are the inverse images of the original strata.
  Its finite partition and constructibility proofs are inherited from that construction.
- For a chart composite q=v≫i the chart scheme is exactly `pullback q h`, with
  g=`pullback.fst q h` and q'=`pullback.snd q h`. `chartMap` is the universal-property
  map from this scheme to `pullback i h`, induced by g≫v and q'. These are the actual
  projections in the question (up to the standard interchange of fibre-product factors).
  `pulledWeaklyEtale` and `pulledCovering` assert that precisely these maps form the
  base-changed pro-etale family on the pulled-back stratum.
- `pulledStratumRestriction`, `pulledObjectRestriction`, and
  `pulledChartRestriction` give all the same exact restriction assertions on W.
  The unprimed `chartRestriction` also records the composite exact restriction.
- `PullbackSquare.comparison` is a natural iso between q'^(-1)Lh* and Lg*q^(-1),
  on the entire constructible input category. Here completed pullback is the actual
  strict reduction-tower functor `completedPullbackFunctor`, not a new operation.
  The `completed` comparison of the theorem, and `Charts.chartPullback` for g,
  identify these strict pullbacks with the specified integral pullbacks via the
  published unit-normalized tower/reflector comparison. Ordinary inverse image of q
  is canonically the iterated inverse image v^(-1)i^(-1), and likewise for q': the
  coefficient-compatible derived composition comparisons use these actual arrows.
- `PullbackSquare.reductions` is an equality of maps for every input and every positive
  level. `leftReduction` and `rightReduction` use the actual
  `completedPullbackReductionArrow` (adjoint of the derived-limit projection) and
  the published coefficient-retaining `chi`. `finiteSquare` is the existing canonical
  derived comparison around `chartSquare`, formed from the two finite-coefficient
  composition comparisons and the equality of the composites. Thus the square's
  finite normalization is specified as a map, not merely existence of an iso.
- Empty strata may be retained by both finite partition interfaces, and can be
  discarded without changing the covering partition. No field asserts a stratum,
  chart scheme, or cover index is nonempty; the empty covering family is allowed
  on an empty stratum. There is no condition on a nonexistent chart index.
- The second main conjunct asserts integral constructibility of the specified Lh*K.
  The last conjunct supplies the same normalized completed comparison c, gives the
  additivity and the R-linear action formula using `integralScalarDerivedAction`, and states preservation
  of distinguished triangles with precisely `c.derivedShift`. That comparison's
  `shifts` field fixes this shift as the transport of the completed shift through gamma.
  The formula for scalar multiples followed by an arbitrary morphism is linearity
  on every Hom group. There is no assertion of global t-exactness.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the recorded coefficient extension.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its actual quotient cone;
  the normalized completed coefficient comparison is reexported by the comparison module.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`, `ProEt.mk`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the integral operation is the existing
  `integralDerivedPullback`, whose restriction is `constructibleIntegralPullback`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: reexports the same ambient integral
  operation and the actual global/slice completion interface; no slice-local copy is made.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage` and
  the same module inverse image used by `ImmersionCompletedPullback.modulePull`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`; `WeilConjectures.ConstructibleSheaf.Pullback`:
  `Scheme.Stratification.pullback` for the actual constructible pullback partition.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, read to extract its actual bounded
  finite-projective representative data.
- For the cohomology node its usable `mathlib_match` is
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`. The node's most recent main `lean` declaration
  concerns a specialized Weil-cohomology object; that specialization is unnecessary
  here because the recorded Mathlib match explicitly supplies the general notion.
- Proof interfaces used in helper signatures: `IntegralCompletedComparison.Comparison`,
  `integral`, `Complete`, `ImmersionCompletedPullback.transport`, `derivedIso`,
  `modulePull`, `productComparison`, `rlimComparison`, `integralConstantDerived`,
  `completedPullbackFunctor`, `completedPullbackReductionArrow`,
  `AdicCoefficientDatum.chi`, `proEtaleAmbientRingedPullbackComparison`, and
  `integralScalarDerivedAction`, from the imported published modules. The stated
  proof-dependency modules are imported, including the exact site-restriction,
  strict-Roos and slice strict-derived-limit interfaces. The local-derived-restriction
  proof node has no recorded module and therefore contributes no import. The local
  AdicStratumCompletionUnit source was read, but its proof-only import was omitted
  after the live server reported its olean missing and `scompile.py --source
  Sheaf.Paper.AdicStratumCompletionUnit` reported "Module source unavailable". No
  declaration from that module occurs in our statement. Its DAG proof step is retained;
  unavailable proof prerequisites do not prevent stating this node.

Edge cases checked: empty X or W; empty pulled-back strata; empty covering index
on the empty scheme; K=0; zero perfect model; all integer cohomology degrees;
intervals including negative degrees and an empty interval; level n=0 meaning exponent
1; arbitrary finite coefficient extension and its recorded uniformizer; chart schemes
which are not Noetherian. Only X and W have Noetherianity and dimension hypotheses.
There is no added regularity, finite-Tor-dimension, boundedness of P in the cohomological
interval, nonempty family, or equality of site object and morphism universes.

Searches for an existing statement:

- `msearch.py ... leanfinder "Exact restriction charts for integral constructible pro etale
  complexes and pullback stratifications"`: 8 unrelated hits (scheme gluing/transition
  limits and Nobeling exactness); no integral chart statement.
- `msearch.py ... loogle "Scheme.Stratification, DerivedCategory.homologyFunctor"`:
  0 hits; Loogle does not index the project's `Scheme.Stratification` identifier.
- `msearch.py ... grep "integralStratum|IntegralChart|stratumChart"`: 0 Mathlib hits.
- `msearch.py ... leansearch "integral constructible complexes exact stratum chart
  restrictions pro etale pullback"`: 8 generic geometric/sheaf pullback hits; no match.
- `rg -n 'integralStratumChart|integral_stratum_chart|IntegralStratumCharts'` in
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration. Searching the item
  id in the upstream tree likewise found none. Broader stratum/chart and completion
  searches identified the published interfaces reused above, rather than an existing
  statement combining these clauses.

Source checked directly: the local Bhatt--Scholze PDF, pp.50--51, Lemmas 6.5.8--6.5.9
and Remark 6.5.10, and p.54, Proposition 6.6.11 including its perfect-values convention.
The node's nine proof steps are carried in the theorem docstring. There is no statement
correction, disputed statement, new DAG node or dependency-record repair.

Validation: the complete statement module compiled cleanly in the prescribed scompile.py
sandbox and library passes. The final minor interface/readability changes are checked
again before delivery. No live source, tool, compiled library, or git checkout was edited.

## Second reading by Q102

The dispatcher explicitly assigns self-delivery and forbids starting another agent;
this section records a second in-thread reading. The maintainer supplies the independent
review. I re-opened the node statement and the entire module, checking each clause
against the mapping above. This caught an initially objectwise-only cohomology assertion:
it was replaced by a natural isomorphism of cohomology functors. I also made ring-sheaf
countable products explicit, added exactness for both composite chart restrictions,
and included the completed/specifed comparison for the arbitrary chart projection g.
The pulled stratification is the existing actual pullback construction, not an
unrelated existential partition. I checked the reduction equation's direction:
reduce the natural comparison and then the right path, or reduce the left path and
then apply the canonical finite comparison. Both end at g_n* q_n* K_n. The scalar
model's terms are bounded independently of the interval asserted for its cohomology.
All auxiliary data are real definitions or existential conclusions of the sole theorem.
Additivity is explicit alongside the scalar action formula. Standard constructor bookkeeping
generation is disabled, as in the published operation module, to reduce elaboration cost;
the fixed 60-second per-file limit is unchanged.
