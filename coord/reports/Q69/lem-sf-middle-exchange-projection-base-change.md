## Worker report

The module `Sheaf.Paper.MiddleExchangeProjectionBaseChange` states
`WeilConjectures.MiddleExchangeProjection.middle_exchange_projection_base_change`.
It has one postponed theorem, with the complete four-step proof from the DAG in its
docstring. All helper definitions have real data. They expand this node's displayed
cube, maps and equation; they do not introduce another six-functor theory.

Source checked: `literature/blueprint/latest/blueprint/sec-six-functors/`
`sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`, clause (iii),
and the item's explicit four proof steps. This is the middle square before the
outer projection formula and compact-support composition.

Hypotheses and clauses, in the namespace
`WeilConjectures.MiddleExchangeProjection` unless qualified otherwise:

- The distinct primes, finite base field, algebraic closure and coefficient closure
  are the existing `D : FiniteFieldDatum` and `C : D.CoefficientDatum`.
  The finite extension is `E`, with `Field`, `Algebra (Padic C.l)` and
  `FiniteDimensional` instances. Its valuation-ring quotients are exactly
  `Padic.coefficientExtensionRing C.l E n`. `n` and `hn : 1 ≤ n` keep the
  positive-level restriction. No alternative coefficient ring is constructed.
- The given six-functor datum is `S : SixFunctorDatum D C E n hn`.
  The conclusion is a conjunction for the four choices of Lambda, so every
  coefficient choice in the node is covered for every positive n.
- `Cube D` names X, Y, B, X', Y', B', T and T' as `SixFunctorSpace D`, hence
  finite-type schemes over the fixed geometric field. Its twelve arrows are
  morphisms over that field. Its separatedness, local finite-type and
  quasi-compact fields express the node's separated finite-type hypotheses.
  Finite type is local finite type plus quasi-compactness, as in Mathlib.
- `Cube.fg`, `fb`, `gb`, `fg'`, `qb`, `pb` are the six Cartesian faces.
  They express T=X times_B Y, X'=X times_B B', Y'=Y times_B B',
  T'=X' times_B' Y', and the induced p/q base changes. Arbitrary representatives
  of these fibre products are allowed; all comparisons are canonical ones.
- In the finite clause `Fixed.law`, K and L are `DerivedCategory.Plus`
  objects with their actual `FixedEtaleOriginWitness` parameters `_WK`, `_WL`.
  `finiteLaw` imposes the existing `finiteTorConstructible` predicate through
  `sfIntrinsicDerivedEquivalence`. Thus the inputs are the node's bounded
  constructible finite-Tor inputs in their canonical fixed-module realization,
  with the small pro-etale site and its coefficient sizes unchanged.
- The finite comparison maps also retain the prescribed origin propositions
  `WP`, `WK'`, `WP'`, `WD'` on p*K, bX*K, p'*bX*K and bT*D respectively.
  These are origin proofs on those very objects, not arbitrary maps or
  substitute complexes. They are universally quantified, so all presentations
  are covered. Their existence is the pullback/tensor stability of the
  supplied witnessed finite domains. The comparison is independent of a
  proof by proof irrelevance. No exchange map is inverted.
- In the integral clause, `higherLaw` uses the existing integral category and
  `S.toSixFunctorOperationDatum.integralFiniteTorDomain` for both K and L.
  These are the completed operations specified by S. The rational category
  and the common-field category already consist of the bounded constructible
  field objects, so their input property is top; this does not enlarge their
  ambient categories to arbitrary derived objects. Their operations and
  exchanges are S's rationalization and common-finite-stage operations.
- F and F' are `S.support f cf` on K and `S.support f' cf'` on bX*K;
  at finite level they are the actual
  `ProEtale.rightDerivedLowerShriekOfCompactification` functors.
  K' and L' are the displayed pullbacks. D and D' are the two tensor products
  appearing explicitly in `equation`, or `Fixed.external` in finite coordinates.
- `beta` is precisely tensor of `exchange` with identity, followed by
  `compactSupportProjectionComponent`. `Fixed.beta` uses the actual
  `ProEtale.projectionMapOfCompactification` after the actual finite exchange.
  The primed beta is this same construction on `Cube.fg'`, K' and L'.
- `exchange` uses `sixFunctorCompactExchange`, followed only by the
  recorded comparison from the base-changed compactification to the requested
  one. `Fixed.exchange` uses the canonical compact-support base-change map,
  followed by `rightDerivedLowerShriekOfCompactificationEtaleOriginIso`.
  Thus all four compactifications may be chosen independently, with the
  specified canonical comparisons inserted. No properness of f or b is assumed.
- `chi` is `mu` for bT followed by the p- and q-square comparisons.
  `integralMu`, `rationalMu`, `commonMu` transport the existing canonical
  monoidal pullback comparisons through S's functor normalization equalities.
  `Fixed.chi` uses `leftDerivedUpperStarTensorIso` and the canonical square
  comparisons. Neither chi nor mu is an extra theorem hypothesis.
- `delta` first applies bY monoidality, then `squarePull S G.gb`, then
  g' pullback of `exchange` for `G.fb`, tensored with identity. `Fixed.delta`
  spells out the same three operations using the canonical finite maps.
  This gives exactly the initial isomorphism for gbY=bg', followed by
  g'*(Ex(f,b)) tensor identity, in the stated direction.
- `equation` and `Fixed.equation` read, in Lean composition order,
  `bY*.map beta ≫ Ex(q,bY)(D) ≫ q'!.map chi.hom = delta ≫ beta'`.
  The typed source is bY*(g*F tensor L) and the target is q'!D'.
  This is equality of those morphisms, before any g! or outer PF/compositor.
- The integral, rational and common-field clauses retain their actual supplied
  comparisons; the statement does not infer integral equality from reductions.
  The docstring explains the strict-reduction, completed-realization and
  coefficient-passage steps of the eventual proof.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`,
  including its operation and coefficient-stage normalization data.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`,
  the specified exchange/projection construction underlying the supplied data.
- `Sheaf.Paper.SixFunctorDualNotation`: the recorded def-sf-pf interface;
  its compact-support projection is the operation datum projection, not a
  newly chosen natural transformation.
- `Sheaf.Paper.DerivedPullbackTensorIso`:
  `WeilConjectures.derivedPullbackTensorIso` and the canonical finite,
  integral, rational and common-stage tensor pullback comparisons in its
  statement. The helper normalization transports use
  `canonicalIntegralPullbackTensor`, `canonicalRationalPullbackTensor`,
  `canonicalCommonStagePullbackTensor` directly.
- `Sheaf.Paper.ExchangeFunctoriality`:
  `WeilConjectures.exchangeFunctoriality`, with the witnessed finite and
  higher-stage exchange-pasting domains and comparison conventions.
- `Sheaf.Paper.ConstructibleProjectionMates`:
  `WeilConjectures.compactSupportProjectionComponent`.
- `Sheaf.Paper.CompactExchangeOperationCoordinates`:
  `WeilConjectures.sixFunctorCompactExchange`, now owned by the new definition
  node `def-sf-compact-exchange-operation-coordinates` in this delivery.
- `Sheaf.Paper.DirectImagesConstructible`:
  `WeilConjectures.finiteFieldDatumPrimeUnit`. `residueUnits` simply maps
  this existing unit along the structure map to each residue field, so the
  canonical higher-stage comparison has its required derived instance.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate`:
  `ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`,
  `rightDerivedLowerShriekOfCompactificationEtaleOriginIso`, and the canonical
  tensor/square/projection maps used by the fixed finite realization.

The already landed owning nodes for the projection helper and prime-unit helper
are in stmt_deps. Their statement and proof dependency closures were checked not
to reach this item. The H2 repair adds the definition node
`def-sf-compact-exchange-operation-coordinates` instead of the theorem node
`thm-sf-dual-base-change`; the new module is imported instead of
`Sheaf.Paper.DualBaseChange`. No dependency replacement or statement correction
is needed. The proof-only node
`prop-sf-pf-coherence` has no recorded Lean declaration; no invented import is
used for it. It remains a proof prerequisite for stage 3, named in the theorem's
proof docstring, and is not assumed as a new theorem hypothesis.

Edge checks: b=id has all canonical identity comparisons and leaves the same
middle square; f=id and g=id use the genuine compact-support exchange and
projection maps. Empty schemes and zero K or L are admitted. n=1 is admitted,
while n=0 is excluded exactly as in the node. No properness, smoothness,
flatness or invertibility of a projection map is imposed. Noncanonical choices
of fibre-product representatives and compactifications are admitted with the
canonical comparisons. The finite site keeps object universe u+1 and the
coefficient ULift realization; no site-universe equality has been added.

Searches actually run (the msearch wrapper records the remote search results):

- LeanFinder: `Compatibility of compact support exchange with the projection
  formula under base change on a fiber product`. Eight hits, mainly scheme
  pullback coordinate lemmas; none states the middle square.
- Loogle: `"projectionFormula", "baseChange"`. Zero hits.
- Mathlib grep through msearch: `projectionFormula|beckChevalley|BeckChevalley`
  in `CategoryTheory`. Zero hits.
- LeanSearch: `Canonical exchange and projection on a Cartesian cube commute
  with base change of the base`. Eight hits about tensor/ring scalar base
  change, none about this derived compact-support square.
- Source repository grep for this node id in `lean/WeilConjectures`: no exact
  statement. Searches for `middleExchange`, exchange/projection, square and
  base-change terms in `lean/Sheaf` found the component constructions listed
  above, and ordinary projection-formula compatibility, not this entire
  four-coefficient middle square. Those constructions are reused.

Validation: scompile.py compiled the sandbox and library-module forms cleanly.
The only postponed proof is the named main theorem. No `STATEMENT-DISPUTED`
finding or node fault was found.

## Second reading by Q69

The dispatcher requires this worker to deliver directly and forbids starting
other agents. This section records a second self-reading, not an independent
worker review; the maintainer's independent delivery review remains pending.
I reopened the node and the complete Lean file, checking each hypothesis and
clause against the correspondence above. In particular I checked the directions
of both pullback square comparisons in chi, the order monoidality/composition/
exchange in delta, the primed inputs, and the exact two composites in equation.
I checked all four coefficient clauses and the finite origin parameters rather
than replacing them by an abstract arbitrary exchange. Earlier elaboration
repairs introduced `Fixed.pull` to keep the finite statement readable. In this
repair I also read the new definition against all four equality fields of
`SixFunctorExchangeData`: source inverse equality, actual stage compact exchange,
then target forward equality. The new module owns that map without importing
the dual-base-change theorem module. The main signature is unchanged, and the
new helper expands to precisely the same formula as the previous helper. The
final reading found no mathematical mismatch.

## New nodes

`def-sf-compact-exchange-operation-coordinates` owns
`Sheaf.Paper.CompactExchangeOperationCoordinates` and the fully defined natural
transformation `WeilConjectures.sixFunctorCompactExchange`. For arbitrary
`SixFunctorExchangeData S T Q`, it transports `A.stage.compactExchange` through
`compactSupport`, `horizontal`, `horizontal'`, `compactSupport'`. This matches
alpha inverse, then e, then beta in the new node's conventional mathematical
notation. Its source is clause (iii) of the current coherence proof together
with the operation-stage and exchange definitions; its dependencies are exactly
`def-sf-operation-stages` and `def-exchange-projection`. No canonical map or
comparison is an extra hypothesis, no invertibility is asserted, and there is
no postponed proof in this module. If all equality fields are reflexive the
definition reduces to the original stage map; it also applies to empty and zero
categories whenever the supplied stage is given. Universes u, v and w are
explicit and independent.

The new searches were run through msearch: LeanSearch for compact support
exchange re-expressed using equality comparisons returned eight irrelevant
compactly-supported-function hits; LeanFinder for transport of compact support
base change through functor equalities returned eight pushforward-congruence
hits, not this map; Mathlib CategoryTheory grep for
`compactExchange|dualBaseChangeHigherExchange` returned zero hits. The node
records the wrapper's actual result records, including digests and hit names.
Source grep found the three helpers identified by the reviewer, in
`DualBaseChange`, `RelativeProductBaseChangeFactorSquares` and
`SemilinearExchangeCubeCoherence`; none has a definition-node owner. The
existing finite witness-transport definition is a different construction.
Blueprint search for `compact exchange` returned no nodes; the broader exchange
search includes the defining supplied stage, but no separate operation-coordinate
transport definition. The maintainer explicitly requested a new owning module
rather than using those theorem/lemma helper modules; this is the reason for
introducing the definition node despite the existing unowned helper copies.

## Repair of return f0f249da78b4

H2: replaced the stmt_dep `thm-sf-dual-base-change` by the new definition node
`def-sf-compact-exchange-operation-coordinates`, imported its module instead of
`Sheaf.Paper.DualBaseChange`, and changed the one call from
`dualBaseChangeHigherExchange` to the definition-node-owned
`sixFunctorCompactExchange`. The new definition's body is the exact equality
transport formula of the old helper, with the full signature and source recorded
in its own node. No shared source file or legacy helper was edited. The genuine
prime-unit theorem dependency is retained, as approved in the return.

Compared the retained returned sandbox node with current main: before this
repair, only lean and the previously authorized stmt_deps additions differed.
The theorem signature and all of its mathematical constructions are retained;
the repair changes ownership of the one coordinate map. Delivery/rebase
bookkeeping is performed only by the prescribed wrappers.
