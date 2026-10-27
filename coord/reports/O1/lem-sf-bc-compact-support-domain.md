## Worker report

The module `Sheaf.Paper.CompactSupportExchangeDomains` states all five coefficient-stage
clauses of `lem-sf-bc-compact-support-domain`. The node's single `lean.declaration` is the
common-stage theorem; `lean.declarations` records every constituent statement and canonical
specialization. The definitions contain real constructions and all new theorem proofs are
`sorry`, with source and step-by-step proof docstrings. No node statement or dependency is
changed. No new nodes or dependency repairs are needed.

Hypotheses and clauses, in node order:

* `D : FiniteFieldDatum` is the fixed algebraic closure of the finite field, and
  `C : D.CoefficientDatum` supplies the prime `C.l`, its primality and its difference from
  the characteristic, together with `C.Qbar`. A finite coefficient field is `E` with
  `Field`, `Algebra (Padic C.l)` and `FiniteDimensional` instances. Its valuation ring,
  uniformizer and positive quotients are the existing `Padic` constructions. The finite
  level is `n` with `hn : 1 ≤ n`; the coefficient ring is its `ULift` into the site size.
* `Q : SixFunctorCompactifiedSquare D` retains the four finite-type spaces, the four
  morphisms, Cartesian identification, compactification, base-changed compactification
  and proper/open squares. The main finite and higher-stage theorems explicitly retain
  separatedness of all four structure maps and separated finite type of the four arrows
  (`IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`). Integral and rational sections
  also bind the separated finite-type hypotheses on `f`. There is no smoothness binder.
  `sfDomainSquare`, `sfDomainProperSquare`, `sfDomainOpenSquare` convert the retained
  Cartesian identifications into the dependency interfaces, without replacing the maps.
* `sfDomainEtaleExchange` is exactly
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, the ordered proper
  mate at open extension followed by the image of the open comparison. The input of
  `sfCompactSupportDomain_finite` lies in `DerivedCategory.Plus` and has the specified
  upper bound `(b : ℤ) [K.obj.IsLE b]`, hence is bounded. Its first conjunct is `IsIso`.
  Its second conjunct is the exchange square for every compactification `d`, using the
  actual canonical `derivedPlusFormalism.shriekIso` at the two ends. These are the
  proper/open comparison maps by `compactSupportFiniteTorsion`; the comparison cocycle
  removes the common refinement. Its last conjuncts preserve each given lower bound
  `IsGE a` and every annihilating scalar `r • 𝟙 K.obj = 0` under exact open extension.
* The finite pro-etale input is a plus object with `FixedEtaleOriginWitness`.
  `sfDomainWitnessExchange` reuses `ProEtale.compactExchangeTransportAtWitness`: this is
  the canonical site-compared etale exchange conjugated by the retained witness, not an
  arbitrary isomorphism. `sfCompactSupportDomain_witness` states invertibility and equality
  for any two witnesses. `sfCompactSupportDomain_witness_identification` identifies this
  conjugate with `canonicalFiniteCoefficientCompactSupportExchange`, whose invertibility
  is also stated by `sfCompactSupportDomain_finiteProetale`.
* Integral inputs are `PbcBoundedConstructibleComplete` for `pbcIntegralDatum C.l E`.
  This is the existing intrinsic completeness, compatible etale-origin reduction,
  constructibility and common finite-interval predicate. `sfDomainIntegralComplete`
  exposes its `cbcCompleteProperty` for a generating tuple `r,a,ha` (including an empty
  tuple when it generates the ideal). `sfDomainIntegralExchange` uses
  `completedCompactSupportExchange` at the retained proper/open squares. This definition
  contains the completed proper exchange and the completed open comparison, using the
  existing `completedPull`, never an ordinary uncompleted pullback.
  `sfCompactSupportDomain_integral` states invertibility. Its refinement companion is
  the actual commuting equation for `cbcRefinementMap`, with the square compatibility
  of the two refinement morphisms explicitly retained. The comparison cocycle and a
  common refinement give compactification independence.
* Rational coefficients use the actual ring `pbcPadicCoefficientDatum C.l E`, with
  `E : Type (u+1)` as in the recorded finite-extension theorem. The existential source
  and target witnesses in `sfCompactSupportDomain_rational` assert the uniform bounded
  constructible landing of both completed composite functors. They are conclusions,
  not extra assumptions on the lattice. The resulting natural isomorphism is between
  `cbcCompactSupportSourceTransport` and `cbcCompactSupportTargetTransport`. Its component
  equation is exactly `finiteExtensionCompactSupportExchangeComponent` at each integral
  lattice, followed by the explicit equality for two lattice presentations. Thus
  naturality is for all raw rational morphisms, not just integral ones. The rational
  refinement statement applies `finiteExtensionRationalArrow` to the two actual completed
  paths and asserts equality. Landing witnesses here are precisely the endpoint proofs
  needed to interpret the ambient arrows in the bounded constructible subcategory.
* `sfDomainNoetherian`, `sfDomainGeometry`, `sfDomainDimension` and `sfDomainInvertible`
  state the geometric consequences of finite type over the fixed field. They supply
  the existing common-stage API's size and geometric facts, not extra input hypotheses.
  `sfDomainScalarSystem` and `sfDomainQbarModel` specialize the existing `pbcScalarSystem`
  and `CbcQbarExchangeModel`. The model retains finite-stage landing, the normalized
  rational exchange and the coherent scalar comparison, including identity extensions.
* `sfDomainQbarConclusion` states existence of the normalized model, invertibility at
  every finite coefficient stage, and invertibility of its descended transformation.
  The `mkHom` equation gives the representative after every finite overfield `M` of the
  chosen stage, with source beta, finite-stage exchange, and inverse target beta in that
  order. The last equation proves independence of two isomorphic presentations. Coherence
  of the existing stage system includes further overfields and equal-field cases;
  nonnested overfields are compared in a common finite compositum. The refinement
  conclusion supplies coherent source/target comparisons, normalized on integral
  representatives by the actual rationalizations of `cbcRefinementMap`, asserts their
  invertibility, and states the descended commuting square. Hence it retains
  compactification independence after descent.

Dependency declarations used (all read in their recorded modules):

* `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum` and the underlying `SixFunctorSpace` and
  `SixFunctorCompactifiedSquare` interfaces.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and
  `compactificationExchangeFromData`, whose proper-mate/open order is the order used here.
* `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
* `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete` and
  `pbcPadicCoefficientDatum`; its underlying `PbcBoundedConstructibleComplete` predicate
  is reused unchanged.
* `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarCompletedPull`, with the existing
  integral completed-pullback constructions retained through its imports.
* `Sheaf.Paper.CompleteCompactSupportProetale`:
  `completeCompactSupportProetale_isIso`, `completedCompactSupportExchange`,
  `cbcExchange` and `cbcRefinementMap`.
* `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange`:
  `finiteExtension_compactSupportBaseChange`, the two transport functors,
  `finiteExtensionCompactSupportExchangeComponent`, and `finiteExtensionRationalArrow`.
* `Sheaf.Paper.QbarCompactSupportBaseChange`: `qbarCompactSupportBaseChange` and
  `CbcQbarExchangeModel`.
* Proof-plan inputs are imported: finite-setting hypotheses, exact open extension,
  proper bounded-below exchange, coefficient forgetting, derived open base change,
  finite compact-support refinement, finite-level pro-etale exchange, rational transport
  and common-stage descent. `Sheaf.Paper.CompactSupportExchangeTransport` supplies the
  existing `ProEtale.compactExchangeTransportAtWitness` and its canonical identification
  `compactSupport_exchange_transport`; no duplicate witness-transport construction is made.

Edge cases checked against the definitions and source: zero complexes; the empty scheme;
identity open immersion; identity base change; level `n=1`; empty generating tuples when
permitted by `ha`; equal coefficient fields, identity scalar extension, further finite
extensions, and two nonnested overfields via their compositum. The finite input is bounded,
the pro-etale witness is bounded below exactly as its dependency specifies, and none of
the statements requires smoothness of `g`.

Searches for an existing exact statement:

* `msearch.py ... leanfinder` queried compact-support base change through finite,
  complete, rational and common-stage coefficient domains: no joint statement found.
* `msearch.py ... loogle` queried expected compact-support/base-change names: no exact
  match. `msearch.py ... grep` queried compact-support and exchange names in Mathlib:
  no statement of this derived etale/pro-etale assertion.
* `msearch.py ... leansearch` queried compact-support derived etale base change: generic
  topological `HasCompactSupport` and unrelated scheme hits, not this statement.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf`, and the exact item-id search, found the
  finite and higher coefficient building blocks but no joint theorem. In particular the
  existing witness-conjugation definition was found and reused.
* Source checks: current `literature/blueprint/latest` clause (4), Stacks
  `more-etale.tex` lemma-base-change-shriek (0F7L), and `sites-modules.tex`
  lemma-extension-by-zero-exact (03DJ). The displayed composite and canonical
  compactification comparisons agree with the interfaces used above.

No statement dispute or node fault was found. Compilation uses only `scompile.py`.

## Second reading by O1

Dispatcher mode supplies no second worker and explicitly prohibits starting agents.
This section records my separate second pass; the maintainer's independent delivery
review remains required. I reread the node beside all declarations, checking the above
hypothesis/clause correspondence, the directions of refinement maps and lattice
conjugations, the finite-overfield beta order, and the actual completed and raw rational
maps. The final pass added explicit separated finite-type hypotheses at each applicable
stage and the bounded upper-degree hypothesis on the finite etale input. It also reused
the already published witness-conjugation map and added its equality to the actual
pro-etale compact-support map. No mathematical node field changed. The Prop definitions
only package concrete propositions; no data is chosen from a nonunique sorry theorem.
