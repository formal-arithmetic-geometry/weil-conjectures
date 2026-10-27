## Worker report

Item: lem-sf-package-base-change-domain-realization. Stage 2, Q03.
Module: Sheaf.Paper.SfPackageBaseChangeDomainRealization.
Main declaration: WeilConjectures.sfPackageBaseChangeDomainRealization.

This is a statement-only delivery: five transparent Prop-valued clause aggregations
and one theorem with `sorry`. The aggregations contain real expressions in the
published categories and canonical maps. No exchange, coefficient category, lattice,
comparison isomorphism, or operation datum is privately reconstructed or selected.
The theorem's docstring records all seven steps of the DAG assembly proof.

Source read: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/prop-functor-package.md and prop-functor-package.proof.md,
particularly clause (4). The local current blueprint is used, not the dated
snapshot named in the node's inherited source field.

Hypotheses and clause audit:

* The algebraic closure k, finite field, characteristic p, prime ell different from p,
  and chosen coefficient closure are `D : FiniteFieldDatum` and
  `C : D.CoefficientDatum`. The finite extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`.
  The positive quotient exponent is `n : ℕ`, `hn : 1 ≤ n`.
  `FiniteMateDomain.Coefficient C E n` is the existing ULift of the canonical
  valuation-ring quotient; `pbcIntegralDatum C.l E` and its existing uniformizer
  give the specified completed integral model. There is no new arbitrary ring,
  uniformizer, or choice of completion in the statement.
* `S : SixFunctorOperationDatum D C E n hn` is the operation datum. Its finite
  categories are the existing bounded constructible finite-Tor categories.
  `PbcIntegralConstructible`, `PbcRationalConstructible`, and `pbcQbarCategory`
  are the recorded uniformly bounded complete, raw rationalized, and common-stage
  categories. The finite ordinary assertions also state the larger bounded-below
  torsion domain explicitly, as the node requests.
* `X X' Y Y' : SixFunctorSpace D` means finite-type k-schemes; the four
  `IsSeparated _.obj.hom` instances impose separation over k. The four bundled
  arrows are over k, and each has explicit separated, locally-finite-type and
  quasi-compact instances, together exactly separated finite type.
* `sq : ChosenCartesianSquare g'.hom.left f'.hom.left f.hom.left g.hom.left`
  retains the commuting equality and the specified pullback isomorphism.
  `exchangeTransposeSquare sq` changes only the smooth theorem's label convention.
* `sfPackageBaseChangeGeometry`: all four corners are Noetherian, compact, quasi-
  separated, finite-dimensional, and have ell invertible in their stalks. All four
  arrows are qcqs. Its `∃ e : ℕ, ∀ Ω ... y` bounds every geometric fibre, including
  empty fibres whose dimension is explicitly bottom. `IsProper f → IsProper f'`
  is the proper base-change clause. For every separated finite-type arrow into
  a corner it supplies `∃ c : Compactification h, QuasiCompact c.i`.
* `sfPackageBaseChangeFinite`: the outer hypothesis is exactly proper f OR smooth g.
  Every small-etale input is `DerivedCategory.Plus` of finite coefficient modules;
  torsion is automatic for this finite quotient. The `IsIso etaleMate.app` is
  followed by the coefficient-forgetting equality and etale/pro-etale comparison
  equality. For a pro-etale input the binder is `FixedEtaleOriginWitness ... K`.
  Its additional disjunction retains bounded constructibility of the witness only
  in the smooth case. The explicit five-factor conjugation equation identifies
  the actual ambient mate with the witnessed etale mate.
* `sfPackageBaseChangeCompleted`: proper f gives invertibility on intrinsically
  complete objects with `PbcHasCompatibleEtaleOrigins`; the next equations retain
  the finite-reduction exchange and the strict derived-limit comparison and identify
  the same map with `AdicCoefficientDatum.completedExchange`. Constructible inputs
  give constructible endpoints and an isomorphism in that full subcategory.
  Smooth g starts from `PbcIntegralConstructible`, concludes bounded constructible
  etale origins for every reduction and the ambient isomorphism. Its final implication
  has one common integer interval for the four finite families (push, pulled push,
  pull, pushed pull). Only under this hypothesis are constructible endpoints asserted.
* `sfPackageBaseChangeFields`: the Noetherian, dimension and invertible-prime binders
  are supplied by the geometry clause; their explicit universal quantification
  permits precisely the existing recorded category interfaces. Proper f gives the
  raw rational exchange isomorphism and `SbcConstructibleExchangeRepresentation`
  on each specified lattice. Its qbar clause retains an actual
  `PbcQbarExchangePresentation`, component invertibility, finite-stage invertibility,
  and the formula at every dominating coefficient field.
  The smooth E clause is the complete conclusion of `eCoefficientSmoothBaseChange`:
  finite-level admissibility, actual ambient map, transported-map equality, lattice
  independence, and square-constructible admissibility before landing.
  `exchangeCommonStageSmoothAtSquare` retains the exact published qbar presentation,
  representatives with admissible integral lattices stable under every finite
  overfield, the ambient invertibility domain, every-overfield formula, and lattice
  independence. The following quantified clause states conditional constructible
  landing at every finite coefficient stage using that same square-admissibility
  predicate. There is no unconditional constructible smooth assertion.
* `sfPackageBaseChangeCompactSupport`: g has no smoothness hypothesis. Every finite
  etale bounded-below input has invertible canonical compactification exchange;
  every finite pro-etale input with a fixed etale-origin witness has invertible
  `canonicalFiniteCoefficientCompactSupportExchange`. The integral assertion uses
  the existing `cbcCompleteProperty` full subcategory and compatible origins, with
  the exact `completedCompactSupportExchange`. The rational-support predicate
  retains constructible endpoint proofs, the localized natural isomorphism and
  its normalization to the completed component, as well as identity/pasting.
  The common-stage clause retains actual models, component and natural-transformation
  invertibility, finite-stage invertibility and the recorded overfield and
  representative-independence equations. No Karoubi replacement of the raw input
  category is made.
* The final conjunction uses the published exchange-coherence predicates:
  `exchangeDatumFiniteIdentification`, `exchangeFiniteStageLaws`,
  `exchangeFiniteCompactIdentification`, `CompletedOrdinaryExchangeLaws`,
  `CompletedSupportExchangeLaws`, `exchangeCompletedSupportNaturality`,
  `exchangeIntegralModelIdentification`, `exchangeCompletedMateLaws`,
  `exchangeCompletedSquareNaturality`, and `exchangeIntegralNormalization`.
  These retain the identity, horizontal/vertical pasting, refinement, composition,
  actual operation-datum comparisons and strict-limit normalization of the named
  maps on their recorded domains. The field helper includes the corresponding
  rational/common-stage normalization predicates. No map is an arbitrary witness.
* No coefficient category of discrete non-torsion small-etale sheaves occurs.

Dependency declarations read and used (namespace qualifications are retained):

* Sheaf.Paper.SixFunctorOperationDatum: `WeilConjectures.SixFunctorOperationDatum`,
  `SixFunctorSpace` and its over-k interfaces.
* Sheaf.AlgebraicGeometry.ChosenCartesianSquare:
  `AlgebraicGeometry.ChosenCartesianSquare`.
* Sheaf.Paper.ExchangeProjectionSuppliedDomains:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and its
  mate-defined `exchange` and compactification-defined `compactExchange`.
* Sheaf.Paper.PbcQbarCompletedPullback:
  `AlgebraicGeometry.Scheme.pbcQbarCompletedPull` and its canonical stage transport.
* Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
* Sheaf.Paper.ECoefficientSmoothBaseChange:
  `WeilConjectures.eCoefficientSmoothBaseChange` and its admissibility and
  constructible-representation predicates.
* Sheaf.Paper.QbarCoefficientSmoothBaseChange:
  `AlgebraicGeometry.Scheme.qbarCoefficientSmoothBaseChange` and its `Presentation`.
* Sheaf.Paper.CompleteCompactSupportProetale:
  `AlgebraicGeometry.Scheme.completeCompactSupportProetale_isIso`.
* Sheaf.Paper.FiniteExtensionCompactSupportBaseChange:
  `AlgebraicGeometry.Scheme.finiteExtension_compactSupportBaseChange`.
  The existing same-universe `LiftedCbc` normalization in ExchangeFunctoriality
  is used for the package's E : Type u; no coefficient universe equality is imposed.
* Sheaf.Paper.QbarCompactSupportBaseChange:
  `AlgebraicGeometry.Scheme.qbarCompactSupportBaseChange`, `CbcQbarExchangeModel`.
* Sheaf.Paper.FiniteMateDomain:
  `WeilConjectures.FiniteMateDomain.finiteMateDomain`, `Coefficient`, `etaleMate`,
  `ambientMate`, `comparison`, `sourceIso`, `targetIso`.
* Sheaf.Paper.SfBcCompletedMateDomain:
  `WeilConjectures.sfCompletedMateDomain`, `sfCompletedFiniteProfile`,
  `sfCompletedMatePushComparison`.
* Sheaf.Paper.ExchangeFunctoriality: `WeilConjectures.exchangeFunctoriality`,
  `exchangeTransposeSquare` and the named Prop-valued clauses above.
* Sheaf.Paper.QbarProperBaseChange:
  `AlgebraicGeometry.Scheme.qbar_properBaseChange`, `PbcQbarExchangePresentation`.
* Proof imports: Sheaf.AlgebraicGeometry.SfBaseChangeGeometryHypotheses,
  `AlgebraicGeometry.sf_baseChange_geometry_hypotheses`; Sheaf.Paper.SfBcAdicRingDomain,
  `AlgebraicGeometry.Scheme.sf_bc_adic_ring_domain`.
  The field-mate and compact-support-domain proof nodes have no recorded module in
  the read state; the owning theorem's proof plan cites them as the DAG does.
  They introduce no missing object required to type this statement.

The H2 repair replaces the former four theorem statement dependencies by four
existing:true definition owners listed under New nodes below. It also cites the
already-landed chosen-square-transpose, completed-pullback-presentation-transport,
and adic-finite-cohomology owners. The original mathematical statement, Lean module,
proof and proof_deps are unchanged; no source correction is required.

Edge cases read against the definitions: empty corners and fibres (no nonempty
assumption; fibre bound includes dimension bottom), zero complexes, n=1 (positive
rather than n=0), identity squares, proper f with arbitrary g, smooth g with
nonproper f, arbitrary nonsmooth g in compact support, absent smooth landing bounds
(ambient only), an identical finite coefficient field and a proper finite overfield,
and several admissible lattices of the same rational object. The canonical
normalizations retain identity transitions and representative independence.
The `letI` selections in field clauses select inherited Category.{u+2} instances;
they add no category data or assumptions. No file-local instance or notation is used.

Searches actually run through msearch.py:

* LeanFinder: "Proper smooth and compact support base change realization of completed
  adic coefficient domains and canonical exchange maps" — eight generic adic/algebra
  hits, no exact statement.
* Loogle: "CategoryTheory.IsPullback, AlgebraicGeometry.IsProper" — zero hits.
* Mathlib grep: "baseChange.*[Dd]omain|[Dd]omain.*[Bb]ase[Cc]hange" — one unrelated
  transvection hit, no match.
* LeanSearch: "Proper smooth and compact support base change realization with completed
  coefficients and admissible lattices" — eight hits about algebraic base change and
  smoothness stability, no sheaf exchange-domain realization statement.
* rg/grep of lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  the item ID, proposed declaration name and base-change/domain patterns found
  component statements, but no existing aggregate theorem of this statement.
  The existing component declarations are reused above.

No STATEMENT-DISPUTED finding.

## Second reading by Q03

A second pass by this dispatched worker compared the node, current blueprint,
recorded dependency signatures and the module clause by clause. This is not an
independent second-agent review: the dispatcher expressly forbids starting other
agents and assigns the maintainer the independent delivery review.

The pass retained the completed four-family interval implication; the finite
pro-etale smooth witness's bounded constructibility; the actual finite and completed
comparison equations; the raw rational category; and the common-stage overfield
qualifications. It added the explicit conditional landing clause at every finite
qbar stage and reused the existing common-stage formula predicate instead of
re-elaborating its expression. The latter change is definitional reuse only.
No statement was weakened to resolve the compilation universe issues. All universes
and variables are bound explicitly. Only the theorem proof is postponed.


## Returned delivery repair: H2

Returned head: 5396dbfbf579 (the delivered short hash was 5396dbfbf57).
The retained Lean file SHA256 is
c449b1f0700855be2da6c7a348f6f090af0a6c89310653e59e44a962e07aba2b.
The current main item still has no Lean record and its original ten statement
dependencies. The repaired item copy was rebuilt from that current main node,
retaining only this packet's lean record and revised stmt_deps; every other field
matches main. The delivery wrapper rebases the packet onto current main.

1. Removed lem-sf-bc-finite-mate-domain, lem-sf-bc-completed-mate-domain,
   fix-lem-exchanges and thm-weil-pbc-qbar from the proposed stmt_deps. The first
   three remain proof_deps exactly as on main: proving their conclusions will be
   part of stage 3, whereas no theorem conclusion is needed merely to state this item.
   The proper-Qbar theorem remains an on-route source for the proof's field step.
2. Added the four definition owners below, each existing:true, naming the exact
   published definitions in its existing module. This is the established definition
   ownership pattern of def-sf-chosen-cartesian-square-transpose and
   def-sf-adic-finite-cohomology, including when a definition currently resides in a
   theorem module. No published file was edited and no definition was copied or
   replaced. Each new node's statement defines data or a proposition, never asserts
   that its preservation, invertibility or coherence conditions hold.
3. Added all three owners explicitly requested by the return:
   def-sf-chosen-cartesian-square-transpose for exchangeTransposeSquare;
   def-sf-completed-pullback-presentation-transport for cbcDatumCompletedTransport
   and cbcDatumCoefficient_eq; def-sf-adic-finite-cohomology for sbcAdicFiniteCohomology
   used inside sfCompletedFiniteProfile. Their existing signatures and docstrings
   were read, including the full finite-cohomology restriction-of-scalars body and
   the Rlim-whiskered universal-counit transport body.
4. The mathematical Lean file and theorem signature are byte-identical to the
   returned version whose mathematics the maintainer accepted. The existing module
   imports therefore still supply exactly the same declarations; their definition
   ownership is now distinct from the theorem conclusions in the DAG. Only lean
   metadata, stmt_deps, the four definition nodes and this report change.

## New nodes

* def-sf-finite-exchange-comparison-coordinates owns Coefficient, etaleMate,
  ambientMate, comparison, sourceIso and targetIso in Sheaf.Paper.FiniteMateDomain
  (source lines 42--86). Its statement gives the lifted finite ring, the two actual
  mates, the exact derived site comparison, and both endpoint comparisons with
  their qcqs hypotheses. It adds no properness, smoothness or invertibility claim.
  The n=0 definition is also allowed, although the package fixes n>=1. Source:
  current blueprint prop-functor-package proof clause (4), finite witnessed exchange.
* def-sf-completed-mate-comparison-profile owns sfCompletedMatePushComparison and
  sfCompletedFiniteProfile in Sheaf.Paper.SfBcCompletedMateDomain (lines 52--82).
  Its comparison is eqToIso of the derived direct-image functor applied to the
  specified coefficient-map equality. Its profile is exactly forall i, constructible
  finite cohomology and vanishing outside [a,b], with no assumed a<=b. It cites the
  existing transport and finite-cohomology owners. A reversed interval requires
  zero cohomology everywhere, and the zero complex satisfies every interval profile.
* def-sf-exchange-domain-coherence-predicates owns the exchange*/Completed*Laws
  predicates and their definitional helpers in Sheaf.Paper.ExchangeFunctoriality
  (lines 604--1730). The node defines the domain-qualified propositions, not their
  truth. Its primary declaration is exchangeDatumFiniteIdentification; declarations
  lists every owned predicate, including all nested finite-stage predicates,
  the common-stage at-square/global versions, and the adjunction-conjugate completed
  push compositor used in the mate pasting expressions. The source is the same
  current blueprint clause (4) and fix-lem-exchanges clauses (1)--(4). This ownership
  excludes exchangeTransposeSquare because that already has an accepted owner.
  Identity transitions and the repeated field cases remain in the quantified laws;
  witnessed, complete, admissible-lattice and conditional landing domains are retained.
* def-sf-qbar-ordinary-exchange-presentation owns PbcQbarExchangePresentation,
  its exchange and atStage, and the two generic stage-system formulas used to define
  them, in Sheaf.Paper.QbarProperBaseChange (lines 74--196). The structure retains
  all four integral preservation fields, four exact coherent families, four exact
  stage-functor specifications, all scalar beta normalizations, and the HEq equation
  fixing the stage exchange to the localized actual completed exchange. Its two
  formulas retain the compositor conjugations and the representative at every
  finite overfield, including the original field. No existence or IsIso assertion
  is hidden in the definition node.

For EACH new node, LeanSearch, LeanFinder, Mathlib grep, project grep, DAG search
and current-blueprint search were run before writing the record. The exact queries
and returned tool output are in each node's mathlib_searches (including the eight
actual hit records of each semantic search). Mathlib grep found zero hits for the
exact helper patterns. Semantic search found generic algebraic etale base change,
sheaf presentation/cohomology facts, generic categorical coherence, or coefficient
presentation algebra, respectively; none replaces these fixed project definitions.
Source grep found exactly the existing modules above; no matching definition owner
was present in dag/nodes. The theorem-node records list helpers but are not their
notion owners. The blueprint exact-name searches returned zero matches. The broad
exchange-coherence search found the completed coherence theorem, whose conclusion
is not a definition of these predicates. Each new node therefore uses existing:true,
introduces no new Lean implementation, and has empty proof and proof_deps. The item's
ancestor is prop-functor-package, and each via begins with this item.

The dependent completed-operation theorem remains cited in the new definitions
where its uniqueness conclusions actually construct the completed functors and
adjunction, rather than merely supplying a name. None of the four rejected theorem
stmt_deps is reintroduced as a definition dependency.

## Repair second reading by Q03

Reopened the H2 return, current main item, all four source definition groups, and
all three pre-existing requested owners. Every named definition in the return now
has a cited definition owner. Verified that the new nodes' lean.statement fields are
verbatim signatures from the existing modules, that their lists contain only
existing definitions, that every bracket citation equals stmt_deps as a set, and
that none of the four forbidden theorem IDs occurs in the item's stmt_deps or in
any new node's stmt_deps. Rechecked the main Lean signature against lean.statement;
no mathematical clause, binder, category, map or universe changed. Independent
mathematical review remains with the maintainer, as the dispatcher directs.
