## Worker report

The module states scalar transport and canonical compactification descent for the
specified semilinear compact-support exchange. This is stage 2: each theorem has
`sorry`, and the delivery introduces no replacement exchange map or hollow data.
The primary declaration concludes the six existing output propositions together;
the other declarations expose their components and an explicit refinement equation
in the intrinsic raw rational and common-stage categories.

The additional `isomorphismExchangeFiniteCommonRefinement` writes the finite
common-refinement square literally with `shriekIso` and the specified
`shriekBaseChangeOfIsPullback`. It allows arbitrary refinements, without imposing
a Cartesian condition on a refinement.

Hypothesis and clause correspondence:

- `P : PurityFiniteSetting` retains the algebraic closure of a finite field,
  coefficient prime different from its characteristic, finite extension, valuation
  ring, uniformizer, and positive finite coefficient level.
- `_finite`, `_finiteIdentity`, `_finiteHorizontal`, `_finiteVertical`,
  `_finiteReduction` are the predicates on the specified finite proper mate,
  proper counit, open unit, ordered composite, its unit, successive-isomorphism,
  compatible-triangle and quotient-coefficient equations. They are assumptions,
  as in the item, not an assertion that arbitrary exchange isomorphisms suffice.
- `_integral`, `_strict`, `_strictHorizontal`, `_strictVertical`,
  `_strictReduction`, `_completed` retain the actual strict reduction diagrams,
  normalization before Rlim and reconstructed integral identity/pasting equations.
  Their adic datum is `pbcIntegralDatum P.coefficients.l P.extension`.
- The six output propositions quantify over separated finite-type maps of
  separated finite-type schemes over `Spec P.field.k`. Their `IsOver` binders
  concern f only. The base-change arrows have `IsIso`; no `IsOver` condition
  is imposed on g, g' or the compactifying arrow. `ChosenCartesianSquare`
  and `OpenImmersionSquare` retain the actual square projections.
- `PurSemilinearRational` states the localized ordered identity for the actual
  `finiteExtensionCompactSupportExchangeComponent`. Its comparison e has inverse
  exactly `ordinaryToCompleted`, and the middle arrow is the existing
  `PurReindexing.purIntegralReindexingExchange`. The target completion unit is
  retained. Completeness is tested for every generating tuple, including an empty
  tuple if it generates the ideal. Source/target preservation are conclusions.
- `PurSemilinearScalar` is the actual completed-exchange square with
  `cbcScalarSourceInverse` and `cbcScalarTargetInverse`, for all E<=F. Those
  comparisons are fixed by the proper counit, open unit and completed-pullback
  unit in `CbcQbarExchangeModel`. Its scalar families and coherent beta maps retain
  the identity and finite-field-tower cocycles; equal stages are included.
- `PurSemilinearCommonStage` gives a normalized model and its exact integral
  representative at every stage. Its last equation represents the descended
  component at every larger common field using the actual beta maps, rather
  than selecting new representatives. Together with `PurSemilinearRationalCoherence`
  these identify the identity, horizontal and vertical paths at one common stage.
- `PurSemilinearRefinement` states the displayed exchange/refinement square for
  `cbcRefinementMap` and `cbcExchange`, its naturality, identity, composition,
  independence and cocycle of `cbcCompactificationComparison`, and the actual
  `cbcTowerCompositionMap` equation under compatible tower refinements.
- `PurSemilinearRationalCoherence` explicitly localizes the integral identity,
  horizontal and vertical paths, including the completed pullback compositors and
  tower compositor. Endpoint predicates are retained, not inferred by an
  unconstrained existence assertion.
- `PurSemilinearFiniteCompactComparison` identifies the finite independent map
  with its chosen-compactification map conjugated by exactly `shriekIso`.
- `isomorphismExchangeRefinementScalarImages` adds the literal refinement equation
  at every finite field stage after localization, after the inverse normalized
  rational coefficient identity, and after common-stage inclusion and the inverse
  normalized pair equivalence. `J : FdCoefficientComparison` is supplied comparison
  data fixed on integral objects, pure tensors, scalar maps and the chi comparison;
  it is not an arbitrary equivalence. `hM`/`hN` are conclusions retaining the full
  endpoint lattice/constructibility/completeness domain. This is the explicit
  transport to `sfRationalConstructibleCategory` and
  `generalAlgebraicallyClosedConstructibleCategory`, without adjoining retracts.

The input domain predicates retain witnesses, compatible etale origins,
constructibility, common finite amplitude bounds and completeness. No reduction
operation is introduced at E or at the algebraic closure.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, its
  `compactExchange`, coefficient-preservation and scalar-cocycle predicates.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `AlgebraicGeometry.Scheme.completedCompactSupportExchange`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory` (raw localization).
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: Stage, stageSystem,
  inclusion and `generalAlgebraicallyClosedConstructibleCategory`.
- `Sheaf.Paper.ExchangeFunctoriality`: `exchangeFunctoriality` was read;
  the statements use its canonical `LiftedCbc.finiteExtensionRationalArrow`,
  `finiteExtensionCompactSupportExchangeComponent` and completeness interface,
  and the same canonical completed maps and restricted domains.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus`.
- `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting`:
  `AlgebraicGeometry.ProEtale.StrictTower.compositionPastingCoherence`.
- `Sheaf.Paper.SemilinearExchangeReindexingData`: the existing finite and
  strict-integral normalization predicates and canonical reindexing exports.
- `Sheaf.Paper.FdCoefficientComparison`: `FdCoefficientComparison` and
  `FdRationalStageComparison`, normalized coefficient identity transports.
- `Sheaf.Paper.SemilinearExchangeReindexing`: the six exact existing output
  proposition definitions, recorded in the new definition node. The theorem
  `semilinearExchangeReindexing` is never used or assumed.

Edge cases checked by reading the definitions: identity base change and refinement;
identity field inclusion E=F; repeated stages in a field tower; zero complexes;
empty schemes; arbitrary finite generating tuples (including the empty tuple when
its span is the ideal); positive level one and exclusion of level zero by P;
arbitrary underlying isomorphisms without k-linearity; different common refinements;
refined compatible composition towers. In each case the same canonical unit,
comparison or functorial equation remains defined. Rational morphisms can have
uniformizer denominators: only integral paths are reduced, and rationalization is
functorial on all localized arrows.

Searches: msearch LeanFinder, query “Scalar transport and refinement descent of
normalized semilinear compact support exchange”, returned 8 unrelated analysis
hits. Loogle query `Functor.map_comp, NatTrans.naturality,
Localization.liftNatTrans` returned no hit (unknown first identifier). Mathlib
CategoryTheory grep `refinement.*[Ee]xchange|[Ee]xchange.*refinement|
[Ss]calar.*[Ll]ocalization` returned 0 hits. LeanSearch query “normalized rational
scalar comparison and compactification refinement exchange equations” returned
8 unrelated normalization/scalar facts. A further Mathlib grep
`PurSemilinear|Compactification.*refinement|refinement.*exchange` returned 0.
`rg` of WeilConjectures found no same statement. `rg` of Sheaf found the canonical
scalar localization interface and the six predicates in the downstream assembly
module. DAG grep found the theorem node but no definition owner for those six;
`tools/blueprint_refs.py search PurSemilinearCommonStage` returned 0. Existing
predicate definitions are reused, not copied. Logged results are in searches.jsonl
and copied into the new node's mathlib_searches.

No source statement correction and no disputed mathematical statement. The
latest blueprint constituent compatibility paragraph and the item's nine-step
expanded argument were read. Compile diagnostics led to reusing the existing
proposition names rather than repeatedly elaborating their large expanded types.

## Second reading by Q37

The dispatcher prohibits starting another agent; no independent worker was started.
I made a second clause-by-clause pass with the node and Lean source open. It found
that the first draft stated only the PBC presentation of field coefficients; the
explicit normalized intrinsic rational/common-stage refinement clause was added.
It also found a potentially circular theorem dependency: the six output predicates
live in the downstream assembly module. Their exact existing definitions now have
a definition-node record, and no downstream theorem is assumed. Independent
mathematical review is left to the maintainer as specified in the worker brief.

## New nodes

`def-pur-semilinear-exchange-descent-data` records, existing:true, the six exact
published proposition definitions in `Sheaf.Paper.SemilinearExchangeReindexing`.
They package scalar normalization, common-stage representatives, rational pasting,
refinement and finite compactification descent. This node asserts none of them.
The existing reindexing-data definition owns the finite/strict input predicates,
not these output predicates. Searches above established no Mathlib/upstream match
and no separate definition owner. Source: latest blueprint constituent compatibility
paragraph and its extracted scalar/refinement argument. No duplicate module or
predicate definition is supplied.
