## Worker report

The module `Sheaf.Paper.WeilBaseChangeSemilinearPasting` states
`WeilConjectures.MixedSemilinear.weilBaseChangeSemilinearPasting`, with one
postponed proof. Every auxiliary definition supplies actual data. Its docstring
contains the six-step DAG proof, including finite evaluation normalization,
coherent strict reduction normalization, limit realization, and scalar descent.
The node statement and proof are unchanged. The H2 repair records the canonical
maps under a new definition owner and
cites the existing semilinear, completed and field definition owners.

Clause-by-clause rendering:

- `P : PurityFiniteSetting` fixes the finite field, its algebraic closure,
  inverse arithmetic Frobenius, coefficient prime distinct from the
  characteristic, finite coefficient extension and positive quotient level.
- `S : Square P.field` retains the four schemes over the finite field, their
  separated finite-type structure maps, the four separated finite-type arrows,
  and `ChosenCartesianSquare`. Finite type is expressed by locally finite type
  and quasi-compactness. `geometricFiber` and `fiberMap` are the existing chosen
  geometric base changes. The compatible compactifications, middle model map,
  proper and open pullback witnesses are retained as data of `Square`.
- Each `galois P.field T₀` is the existing geometric-Frobenius scheme map,
  rather than a morphism over the geometric base field. The canonical
  commutativity witnesses come from `frobenius_square_cartesian`.
- `finitePaths` uses `ordinaryJ ⋙ ordinaryR` for compact support, `ordinaryG`
  for both geometric and semilinear pullbacks, and exactly three `ordinaryH`
  exchanges: geometric base change and the two Frobenius self-squares.
  `ordinaryH` is the proper adjunction mate followed by open base change.
- `pathPair` inserts the canonical `sourceSquare` comparisons at the source
  and target. Its first arrow is `QY.map e` followed by `B` and the target
  pullback comparison; its second is the source comparison followed by
  `GY'.map B` and `e'`. Equality of its components is precisely the displayed
  mixed equation, with a common source and target.
- The first conjunct quantifies over `finiteTorConstructible` objects. The
  bounded-below etale complex `L` and the isomorphism from its recorded
  `origin` retain the supplied finite-domain witnesses used by normalization.
- The second conjunct uses `finiteTorConstructibleIntegralCategory` and the
  actual `reduction` functor. `strictPaths` acts on whole derived categories
  of coherent quotient diagrams, using published `SemilinearProperOpen.P`,
  `R`, `J`, `exchange`, `beta`, and `squareP`. Thus it asserts equality
  before derived inverse limit, including coefficient transitions; it is
  not an assertion merely after separate finite evaluations.
- `fixedQuotientRings` and `fixedQuotientMaps` are aliases for the existing
  quotient data with the canonical spectral norm explicitly supplied.
  They add no norm hypothesis to the finite algebraic extension.
- `CompletedAndFieldClaim` states the actual completed equation. Its `K`,
  finite ideal-generating family and completeness witnesses are precisely
  the inputs of `cbcExchange`. Bounded constructibility, compatible etale
  origins and the complete input are retained by
  `PbcIsBoundedConstructibleComplete`; the integral DVR convention gives
  finite Tor dimension on this domain. `hG` and `hQ` retain the intermediate
  complete inputs required by the recorded exchange API.
- `completedH` is exactly `cbcExchange`; `completedSquare` is the recorded
  completed pullback compositor with its equality transport. `completedLeft`
  and `completedRight` insert these comparisons at the same endpoints as
  the finite paths. No exchange arrow is quantified as arbitrary data.
- The remaining clauses of `CompletedAndFieldClaim` apply the existing
  `LiftedCbc.finiteExtensionRationalArrow` to both completed composites,
  retaining the source and target bounded-constructibility witnesses.
  Their images under `commonStageInclusion` give the algebraically closed
  field clause. This functor uses the canonical `Shrink.algEquiv`, actual
  `pbcRationalScalarExtension`, and the inclusion into `pbcScalarSystem`.
  Dimension and coefficient-unit witnesses are the supplied common-stage
  domain, not extra geometric restrictions. Objects and paths represented
  over any common finite stage are covered by the quantifier over `P`.
- `EarlyRefinementClaim` states both refinement squares (`b : Bool` selects
  each of the two paths) on the same finite and integral strict domains.
  `finiteRefinement` is an alias of the newly landed `ordinaryC`;
  `strictRefinement` uses the published clopen gamma
  comparison, the identity normalization and direct-image compositor.
  They require no Cartesian refinement square. `RefinementClaim` states
  both completed refinement squares using the recorded `cbcRefinementMap`.
  Rationalization and common-stage inclusion carry these same equalities
  by functoriality. `recompactify` changes only compactification data.
  The witnesses `hc`, `hγ`, `hγ'` express compatibility of simultaneous
  refinements with the geometric and Frobenius middle maps.
- All choices of compatible compactification are quantified, as are all
  separated finite-type model base changes. No smoothness, properness of
  the original vertical arrows, or geometric-field linearity is imposed.

Dependency declarations read and used (module; declaration/interface):

- `Sheaf.Paper.PurityFiniteSetting`; `WeilConjectures.PurityFiniteSetting`
  and its `Ring`, `Coefficient`, finite extension and coefficient conventions.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`;
  `FiniteFieldDatum.geometricFrobenius`, `galoisMap` and projection formulas.
- `Sheaf.Paper.ExchangeFunctoriality`; `exchangeFunctoriality`,
  `LiftedCbc.finiteExtensionRationalArrow` and its actual completed-support API.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`;
  `SuppliedExchangeProjection.ExchangeProjectionStage`, specifying the
  proper mate followed by the open comparison on supplied domains.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`;
  `AlgebraicGeometry.ChosenCartesianSquare` and `OpenImmersionSquare`.
- `Sheaf.Paper.RelativeCompactSupportPasting`; `ordinaryG`, `ordinaryJ`,
  `ordinaryR`, `ordinaryH`, `sourceSquare`, now owned by the new definition
  node through its public re-export.
- `Sheaf.Paper.FrobeniusGeometricExchange`; `geometricCompactification`,
  `zlCompactificationMiddle`, `zlCompactificationOpen`,
  `zlCompactificationProper`, `fiber_finiteType` and `galois`.
- `Sheaf.Paper.SystemOperationExchangeRealization`; `reduction` and
  `coefficientSequenceDerived`, with the actual quotient-system categories.
- `Sheaf.Paper.FiniteTorAmplitudeSites`; `finiteTorConstructible` and
  `finiteTorConstructibleIntegralCategory` at the prescribed site sizes.
- `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport`;
  `CompactSupportCondensedRealization.quotientRings`, `quotientMaps`.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`;
  `AlgebraicGeometry.ProEtale.SemilinearProperOpen.P`, `R`, `J`, `squareP`,
  `exchange`, `beta`, `gamma`, `sId`, `sComp`.
- `Sheaf.Paper.FiniteCompactSupportEvaluationRefinement`;
  `StrictTower.FiniteCompactSupport.ordinaryC`, the exact finite refinement.
- `Sheaf.Paper.MixedCompactSupportExchangeData`;
  `MixedCompactSupportData.ordinaryExchange` and its nine public re-exports.
- `Sheaf.Paper.PbcRationalCategory`; `PbcRationalDerivedCategory`.
- `Sheaf.Paper.FiniteStagePairCategory`; `PbcFiniteStagePairCategory`,
  `pbcScalarSystem`.
- `Sheaf.Paper.PbcFiniteCompletedCoefficientMap`; `pbcFiniteField`,
  `pbcFiniteFieldFinite`.
- `Sheaf.Paper.PbcScalarExtension`; `pbcRationalScalarExtension`, re-exported
  and owned as definition data by the new node.
- `Sheaf.Paper.CompleteCompactSupportProetale`; `cbcSupport`, `cbcExchange`
  under their existing definition owner and `cbcRefinementMap` under the new
  definition owner.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`;
  `FiniteFieldDatum.frobenius_square_cartesian`, whose conclusion is used.

`PbcDescentFunctors`, `RelativeCompactSupportPasting` and
`FiniteCompactSupportEvaluationRefinement` remain ordinary imports of the
unchanged proof plan. The tower-mate module has no direct import.

Edge cases checked: empty schemes and zero complexes are not excluded;
identity geometric maps and identity refinements use the recorded unit
comparisons; finite quotient level zero is correctly excluded by the fixed
positive-level convention; the coefficient prime is distinct from the finite
field characteristic. No dimension bound is fixed globally, and the unit and
dimension witnesses occur only in the published field-category domain.
The scheme/site universes are the prescribed `u`/`u+1` sizes; no equality of
independent site universes is imposed. Finite and strict comparisons are
constructed from adjunctions and compositors, never chosen from mere existence.

Searches performed via the prescribed `msearch.py` wrapper, logged in
`searches.jsonl`: LeanFinder query “Compact support base change commutes with
semilinear geometric Frobenius exchange in a Cartesian cube” returned eight
ordinary algebraic `IsBaseChange` hits, none this equation; Loogle query
“CategoryTheory.mateEquiv_hcomp, CategoryTheory.mateEquiv_vcomp” returned no
hits; Mathlib grep `mateEquiv_hcomp|mateEquiv_vcomp` in
`CategoryTheory/Adjunction` found the generic mate laws in `Mates.lean`.
LeanSearch “Compact support exchange base change semilinear Frobenius pasting”
returned eight generic base-change/compact-support hits, none this statement.
The required project `rg` searches and literal node-id grep in
`WeilConjectures` found no existing declaration of this mixed equation.
Searches in `Sheaf` located the existing relative-pasting, strict proper/open,
normalization and coefficient-domain interfaces reused above. Thus no exact
existing theorem statement was found. The repair search below identifies the
missing definition ownership of already published constructions.

No mathematical statement correction, disputed statement or dependency
replacement is delivered. One definition-ownership node is added as requested.
Supporting aliases and path constructions belong to
this node and are listed in `lean.declarations`. Only the main theorem uses
`sorry`. Scratchpad probes and the superseded dependency-interface experiment
are outside the delivered `lean/` and `dag/` trees.

The main construction remains in one owning theorem module. The new definition
module owns its re-exports separately. Explicit result types and
irreducible helper bodies prevent unnecessary expansion during elaboration.
The finite refinement aliases the newly landed exact `ordinaryC` declaration.

Validation of returned head: the original single module compiled in sandbox
(55.2 s) and library (47.2 s) contexts. Both repaired modules passed `scompile.py` with no errors or unexpected
warnings. The repaired delivery also passed `deliver2.py --no-push`
(commit a81f1d6e966); both node records and both modules passed preflight.


## Repair of returned delivery 3d868cb320cc

The independent return has one numbered fault, H2. It accepted the mathematics
clause by clause; this repair changes definition ownership, imports and DAG
citations while preserving the exact main theorem signature and its hypotheses.
The sandbox item was compared with the current read-only main node: only
`stmt_deps` differed before repair, and the returned Lean module has not landed
on main. The delivery wrapper rebases the resulting repair onto current main.

- `ordinaryG`, `ordinaryJ`, `ordinaryR`, `ordinaryH`, `sourceSquare` and
  `ordinaryC` now have the definition owner
  `def-sf-mixed-compact-support-exchange-data`. The original theorem modules
  stay proof imports, while their plain definitions are publicly re-exported
  through the new owning module. `finitePaths` now names the definition owner's
  exact `ordinaryExchange` abbreviation of `ordinaryH`.
- The same new node owns `SemilinearProperOpen.exchange`,
  `pbcRationalScalarExtension`, and `cbcRefinementMap`, by public re-export of
  their existing canonical definitions. No new pasting or invertibility law
  is introduced, and no arbitrary map replaces any construction.
- The old statement citation `lem-sf-semilinear-proper-open-mate-pasting` is
  replaced by `def-sp-semilinear-constant-ring-operations` for `P/R/J`,
  `def-sf-semilinear-proper-open-comparisons` for `squareP/beta/sId/sComp`,
  and `def-coef-semilinear-proper-open-mate` for `gamma`.
- The unused statement citation `lem-cbc-tower-mate-evaluation-scalars` and
  its direct public import are removed. Its underlying declarations remain
  available transitively where existing constructions use them.
- `prop-weil-pbc-descent-functors` is removed from `stmt_deps`. It remains an
  ordinary proof import because it is still a proof dependency of the unchanged
  DAG proof. The field clause now explicitly cites
  `def-weil-pbc-rational-category`, `def-weil-pbc-finite-stage-pair-category`,
  and `def-weil-pbc-finite-completed-coefficient-map`. Their recorded modules
  are public imports. The scalar functor is owned by the new definition node.
- `def-sf-completed-compact-support-calculus-data` is explicitly cited for
  `cbcSupport/cbcExchange`, and its recorded module is publicly imported.
- `lem-weil-frobenius-square-cartesian` is explicitly a statement dependency,
  with a public import: its conclusion supplies the actual commutativity and
  Cartesian witnesses used throughout the Lean statement.

## New nodes

`def-sf-mixed-compact-support-exchange-data` owns the nine published plain
constructions requested by H2 and re-exports them from
`Sheaf.Paper.MixedCompactSupportExchangeData`. Its primary declaration
`WeilConjectures.MixedCompactSupportData.ordinaryExchange` is a fully typed
abbreviation of the actual `ordinaryH`; its record lists all nine unchanged
public imported declarations. Its self-contained statement specifies the
ordinary operations, pullback-square comparison, proper/open exchange,
ordinary refinement, whole-system proper mate, raw rational scalar extension,
and completed refinement. It asserts no theorem laws. All data are real and
there is no `sorry` in this new module. The original item still has one `sorry`.

Searches for this node: `blueprint_refs.py search` found zero matching blueprint
nodes; project/DAG searches located the requested declarations only in their
existing theorem modules (and unrelated definition-node mentions), consistent
with the maintainer's precise ownership audit. Prescribed LeanFinder and
LeanSearch queries returned generic test-function, compact-support and module
scalar-adjunction hits, not this data. Mathlib grep returned generic
`EnrichedOrdinaryCategory` hits from the `ordinaryC` substring, not these
scheme constructions. The new node's `mathlib_searches` retains the wrapper's
JSON results verbatim as recorded in `searches.jsonl`, plus the project and DAG
search results. Existing semilinear and completed definition owners were
read and reused, not replaced or duplicated.

Edge cases from the original report remain unchanged. The new data node is
also valid for unbounded ordinary and simultaneous-system complexes,
nonflat coefficient transitions, non-Cartesian refinement squares, identities
and zero complexes; its field functor retains its original Noetherian,
dimension and coefficient-unit domain. There is no new restriction on the
semilinear maps, coefficient stages or site universes.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
