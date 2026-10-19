## Worker report

Item: `lem-zl-framework-pbc-open-exchange-comparison`; Q09, stage 2.
The statement is split across the exchange comparison, whole-diagram naturality,
fixed-pair compatibility, and comparison-pasting declarations of
`Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison`. The four definition modules
below supply only missing bundles of the existing operations and their specified
normalizations. The original mathematical statement and proof are unchanged.
All theorem proofs are `sorry`; definition data are actual constructions.

### Hypotheses and clauses

1. The finite-field datum is `D : FiniteFieldDatum`; `l`, `[Fact l.Prime]`,
   `hl : l ≠ D.p`, and `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
   `[IsAlgClosure ℚ_[l] Ω]` render the coefficient hypotheses.
2. `OpenDiagram.X/Y/U/V`, their `Over`, `LocallyOfFiniteType`, `QuasiCompact`
   and `QuasiSeparatedSpace` fields render the four finite-type quasi-separated
   k-schemes. `f/f'` have the separated, locally finite-type and quasi-compact
   instances, and are k-morphisms. `v/u` have the quasi-compact open instances.
   The main theorem uses the k-linear alternative for ordinary open diagrams.
   The isomorphism alternative additionally provides exactly the support-transport
   squares needed for semilinear naturality; no k-linearity is imposed on those
   corner isomorphisms.
3. `c/c'` are the existing `Compactification` objects. `properSquare` and
   `openSquare` are the existing chosen Cartesian-square witnesses; together with
   the two compactification factorization identities they express the given
   Cartesian open base-change square and the pulled-back compactification.
   There is no new private definition of a compactification or a pullback.
4. All four corner schemes and both middle schemes have `IsNoetherian` and
   `Fact (∃ n : ℕ, topologicalKrullDim _ ≤ n)` fields. This includes the empty
   scheme, whose Krull dimension is bottom. The stalk-unit certificates follow
   from the k-structures and `hl`; they expose the invertibility required by the
   existing coefficient APIs. No absolute `IsSeparated` hypothesis occurs.
5. `pbcFiniteField l Ω E`, `pbcStageDatum l Ω E` and `pbcStageUniformizer l Ω E`
   are the recorded finite-subfield model, integer-ring completion datum and
   chosen uniformizer. `IntegralSquare.uniformizerIdeal` fixes its principal
   ideal. The existing quotient towers include every transition; the exponent
   convention is the existing positive quotient-index convention.
6. `S : FdCoefficientComparisonSystem` supplies the actual inverse coefficient-
   presentation integral equivalences, raw rational comparison equivalences,
   and common-stage comparison. `IntegralComparisons` uses `S.stage E` at the
   four corners; `FieldSquares` uses `S.coefficients` rather than a replacement
   coefficient category. The main theorem also retains
   `FdComparisonSchemeCoherence S`.
7. The framework support functors are
   `sfCompactSupportFiniteIntegralFunctor` and the existing
   `SfCompactSupportCoefficientAction` systems. The PBC support functors are
   the restrictions of `cbcDerivedOpenShriek ⋙ d.push`, with the existing
   `CbcCompactSupportCoefficientFamily` for their raw and pair stages.
   `supportComparison` uses `sfQcqsCompactSupportRealization`, so its source
   is the actual strict quotient/Roos reconstruction, not a separately chosen
   inverse-limit object. `pbcImageIso` is the unique open-adjunction comparison.
8. Framework pullback is `constructibleIntegralPullback`, with
   `rationalDerivedPullback` and `commonStageDerivedPullback` at field stages.
   PBC pullback is the actual `d.completedPull` restricted by its preservation
   certificate; field stages use `CbcCompletedPullCoefficientFamily`.
9. `CoefficientSquares` asserts equality of the actual coefficient maps.
   `coefficientChange` contains the specified completed-ring isomorphism and its
   genuine inverse. `IntegralSquare.support/support'` fix support comparisons to
   `supportComparison`: projection-normalized qcqs realization, coefficient
   restriction and the unique open-adjunction comparison. These depend only on
   the compactification, so the middle support comparison is the same under
   successive open restrictions.
10. `PullNormalization.chain` is `FdPullbackChain`, retaining all quotient
    coordinates and the zero shifted Roos coordinate. Its `normalization`
    field is the actual ordinary-to-completed unit equation. `rawPullComparison`
    uses this ambient comparison and the unique unit-compatible strict/reflector
    comparison. The latter is selected only from a uniqueness theorem determining
    it; it is not an arbitrary natural isomorphism. `IntegralSquare.pullV_spec/pullU_spec`
    fix precisely these comparisons at complete inputs.
11. `IntegralSquare.sfExchange_spec` now fixes the arrow to the independent
    `frameworkExchange`. Its definition uses the actual framework completed rings,
    the proper adjunction mate, and the inverse open-adjunction unit mate.
    `frameworkTowerExchange` constructs these mates on entire strict diagrams;
    `frameworkModuleQuotientTower` uses the actual `sfReductionRestricted` and
    `sfReductionTransition`. `frameworkAmbientExchange_strict` characterizes the
    ambient arrow by their total-Rlim image and canonical framework endpoints,
    before finite evaluation. `frameworkExchange` conjugates only by
    `sfQcqsCompactSupportRealization` (whose spec uses the published
    `sfCompactSupportFiniteReductionIso` Roos projections) and
    `frameworkOpenPullRealization` (fixed by every quotient-unit and the zero
    shifted coordinate). None of these definitions or specs mentions J, S_K,
    T_K, `cbcRealizationStrict`, or a PBC coefficient datum. The PBC arrow stays
    pinned to exactly `completedCompactSupportExchange` for the principal ideal.
12. `ZlExchange.Comparisons.source K` is a_v followed by P_v(b_f), and
    `target K` is b_f' followed by F_f'(a_u). `Comparisons.Commutes` is exactly
    S_K followed by Ex_pbc = J(Ex_sf_K) followed by T_K. The principal theorem
    states it integrally, at every raw finite field, and at the common-stage
    quotient. Equality at every component is equality of natural transformations.
13. `FamilyIso` retains a `StageSystem.Morphism.Hom`, not just isolated finite
    isomorphisms: its mixed beta equation uses the existing associators and
    includes repeated coefficient stages. `FieldSquares` identifies every finite
    comparison and exchange with the actual scalar localization of its integral
    map. `FamilyIso.pair`, `sfPairExchange`, `pbcPairExchange`, and the finite/pair
    comparison methods descend those actual maps with `functorCompIso` at the
    endpoints. Thus finite extension, identity extension, successive extension,
    and the common-stage Hom-colimit identifications are retained.
14. `PullSystem.identity/composition` use the published unit/composition
    isomorphisms and agree with S on scheme isomorphisms. In addition to the
    generic algebraic pasting lemma, `frameworkOpenRestrictionCoherence` now
    states the actual identity equation for `G.identity` and the successive-open
    equation for every `H : FurtherOpen G`, with `H.second` and `H.outer`.
    The shared compactification is literal; the outer proper and open squares
    are the Cartesian pastes. The equation uses the recorded
    `integralComparisonUnit` and `integralComparisonComposition`. The compatible
    coefficient families and their mixed beta equations transfer these same maps
    to raw rational and common stages, without new choices.
15. `DiagramIso` has all six corner/middle isomorphisms, the proper and open
    transport squares, the u/v squares and the equality for the middle arrow.
    `DiagramComparisons` fixes its support comparisons to the ordered exchanges
    on the two support-transport squares, and its pullback comparisons to the
    whole-system/unit-normalized square comparisons. `diagramNaturality` asserts
    both operation-square naturality equalities integrally, at every raw field,
    and at the common stage. No corner isomorphism is required to be k-linear.
16. `descendedFrobenius` is the actual `D.geometricFrobenius` conjugated by
    the supplied geometric-fibre equality. `frobeniusWeilSupportComparison` and
    `frobeniusWeilSupportComparisonPair` specialize to its actual support diagram
    and explicitly identify the framework actions with
    `sfWeilFrobeniusPullback` and `sfCommonStageWeilFrobeniusPullback`.
    Both framework and PBC support actions are required to have exactly the
    packet's rebuilt exchange as hom; the aX and aY maps are its prescribed comparisons.
    `ZlExchange.HasFixedPairSupportLift` requires a natural isomorphism on the
    existing IsoAlgebra fixed-pair categories whose underlying component is
    exactly b. The generic fixed-pair lemma remains only as the algebraic helper.
    There is no absolute separatedness assumption.
17. The theorem never asserts invertibility of the open-base-change exchange.
    Invertibility is used only for the scheme-isomorphism specializations needed
    for transport and fixed pairs, where it follows from that specialization.

### Dependency declarations used

All original `stmt_deps` were read, with their full recorded declarations and
relevant docstrings. In particular:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib: `IsAlgClosure`, `pullback`, `IsOpenImmersion`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `QuasiSeparatedSpace`, `IsNoetherian`, and
  `topologicalKrullDim`. The scheme-morphism-properties node is explicitly a
  convention collecting its named Mathlib notions, not an absent bundled object.
- `WeilConjectures.Compactification.Refinement` and `.BaseChange`:
  `AlgebraicGeometry.Compactification`, its refinement and pullback structures.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the recorded normalized-coefficient
  family modules provide `pbcFiniteField`, `pbcStageDatum`, `pbcStageUniformizer`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.IntegralUniformCoefficient`:
  `pbcBoundedConstructibleComplete` and its integral restrictions.
- `Sheaf.Paper.CompletedCoefficientPresentationTransport`:
  `purScalarModel`, `purCoefficientIso`, `integralDetailedTransport`.
- `Sheaf.Paper.RationalCoefficientCategoryComparison` and
  `.FdCoefficientComparisonSystem`: `rationalCoefficientCategoryComparison`,
  `FdCoefficientComparisonSystem`, `FdComparisonSchemeCoherence`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`, `sfCompactSupportFiniteIntegralFunctor`.
- `Sheaf.Paper.ProjectionCompactification`: `proEtaleRingCompactSupportImage`;
  the actual PBC proper/open derived operations are reused through its transport.
- `Sheaf.Paper.DerivedPullbackTensorHom` and
  `.IntegralPullbackComparisonRealization`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `commonStageDerivedPullback`,
  `integralComparisonUnit`, `integralComparisonComposition`.
- `Sheaf.Paper.PbcQbarCompletedPullback`, `.PbcActualStrictPullback`, and
  `.CompletedOpenExchangeTransport`: the recorded completed pullbacks,
  `pbcActualCompletedPullback_tower`, `cbcDatumActualStrictTransport`,
  `cbcDatumOrdinaryTransport`.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `completedCompactSupportExchange`.
- `Sheaf.Paper.CompleteProetaleStrictTowerRealization`:
  `cbcRealizationStrict`, `cbcRealizationSource`, `cbcRealizationTarget`,
  `completeProetaleStrictTowerRealization`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  its normalized whole-diagram proper/open identity and pasting laws;
  `Sheaf.Paper.ExactProductFunctorStrictLimit` supplies the canonical Roos endpoint laws.
- `Sheaf.Paper.NormalizedCoefficientFamilies` and
  `.CompactSupportCoefficientAction`: `CbcCompactSupportCoefficientFamily`,
  `CbcCompletedPullCoefficientFamily`, `SfCompactSupportCoefficientAction`.
- `WeilConjectures.CategoryTheory.StageSystem`: actual `Morphism.Hom`,
  `descNatTrans`, `isIso_descNatTrans`, `functorCompIso`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex` and
  `sfWeilFrobeniusPullback`; Mathlib's existing `Endofunctor.IsoAlgebra` and
  `IsoAlgebra.mapOfNatIso` express fixed pairs and their induced functors.

The geometric and coefficient helper bundles are new; none of the existing
categories, compactifications, coefficient families, or derived operations is
privately redefined. No dependency's recorded Lean interface is changed.

### Edge cases

Checked empty opens, the zero input, identity opens, two successive restrictions,
identity and repeated coefficient stages, and semilinear isomorphisms. Empty
schemes satisfy the finite-dimension formulation. All identities use the same
unit-normalized maps; there is no exception discarding an identity base change.
No uniform finite-Tor bound on the quotient tower, absolute separatedness, or
base-change invertibility is introduced. The two uniqueness-based choices in
canonical square comparisons have defining uniqueness equations, not arbitrary
existence data. No statement is marked disputed and no statement correction is
made.

### Searches

- msearch LeanFinder: "Framework reduction tower compact support exchange compared
  with completed proetale proper open base change": unrelated affine-limit hits.
- msearch Loogle: "CategoryTheory.NatTrans, CategoryTheory.NatIso": no match.
- msearch grep, CategoryTheory:
  "framework.*[Cc]ompar|[Cc]ompar.*framework|completedCompactSupportExchange": no match.
- msearch LeanSearch: "natural transformation comparison of compact support reduction
  tower and completed proetale exchange": generic NatTrans/limit hits, no item match.
- For each new bundle, msearch LeanSearch and LeanFinder:
  "compactification open Cartesian square normalized coefficient comparison systems":
  unrelated Stone-Cech, compact-subset, Nobeling and Gromov results; no such bundle.
- msearch grep, Mathlib AlgebraicGeometry:
  "structure (OpenDiagram|DiagramIso|FieldSquares)|FrameworkPbc": no match.
- rg in upstream WeilConjectures and shared lean/Sheaf, including exact item/new
  ids and specialized bundle names: no declaration of these specialized notions.
  Existing StageSystem compatible transformations were found and reused.
- DAG and `tools/blueprint_refs.py search 'compactification open comparison'`:
  zero blueprint matches and no existing specialized node. A broad DAG search
  had one unrelated intersection-structure-sections note. Complete msearch output
  is preserved in each new node's `mathlib_searches`.

## New nodes

`def-zl-compactification-open-diagram`:
`Sheaf.Paper.ZlCompactificationOpenDiagram` bundles precisely the six-scheme
geometric input and whole-diagram isomorphisms, using existing compactifications,
chosen Cartesian squares and Mathlib scheme properties. Its source is the owning
item's current blueprint/common-stage descent argument. The searches above found
no existing specialized bundle. It includes semilinear support transport without
changing the k-linear ordinary open-restriction hypotheses.

`def-zl-framework-pbc-open-comparison-data`:
`Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` supplies the missing specified
comparison-data interface: exact integral maps, whole-tower normalizations,
compatible raw-field families and actual pair descents. Canonical square
comparisons are characterized by unique whole-system/unit equations. Source:
the owning item's integral comparison and common-stage descent proof. Searches
found the constituent operations and compatible-transformation API, which are
reused, but no bundle encoding this comparison square and these normalizations.

`def-zl-open-diagram-comparison-transport`:
`Sheaf.Paper.ZlOpenDiagramComparisonTransport` bundles the actual support and
pullback comparison isomorphisms along a whole-diagram isomorphism, with their
integral normalization, mixed beta families, and finite/pair interpretations.
Source: the owning item's naturality-of-ordered-mates argument. The searches
above found no existing such transport data. Naturality equations themselves
are in the original theorem node, rather than hidden in the definition.

`def-zl-framework-open-exchange`:
`Sheaf.Paper.ZlFrameworkOpenExchange` owns the framework proper/open mate,
its strict-quotient/Rlim characterization, and its canonical Roos endpoint
realizations. Its statement also records the named normalization and uniqueness
properties used by the real definitions. The source is the item's strict-diagram
construction in the common-stage descent proof, with Stacks 07A7, 03S6, 099N,
08TC and 0A07 for the component operations. Fresh LeanSearch, LeanFinder and
Mathlib grep searches found no exact declaration; full outputs are in the node.
DAG, upstream and side-library grep found no duplicate, and blueprint_refs search
returned zero nodes for 'framework open exchange'. Existing operations, coefficient
rings, reduction transitions and projection-normalized endpoints are reused.

## Second reading by Q09

This is a serial second reading, not an independent worker review: the dispatcher
brief explicitly forbids starting other agents. The maintainer's independent
review is still required. Rereading found and repaired: missing semilinear
whole-diagram naturality; the need for genuine compatible families instead of
independent finite isomorphisms; identity/composition normalization of completed
pullback; induced fixed-pair structures; and the explicit comparison-pasting
clause. No hollow definition or extra absolute separatedness hypothesis remains.
The four new definition nodes were reread together with their modules.

## Repair of immutable returned head 8a4e0f61e72f (2026-10-19)

The returned packet normalized Ex_sf by conjugating a PBC strict-tower exchange
through S and T. That made the comparison tautological. The saved repair replaced
this with an independent framework construction but did not finish its node
record, compile, or update the report. The initial required dry run failed with
"ZlFrameworkOpenExchange.lean is the lean.file of no node file".

Primary H3: `strictExchange` was removed. Ex_sf is now defined independently in
`ZlFrameworkOpenExchange`. The framework-only tower proper and open mates,
strict quotient functor, canonical limit comparisons, quotient-unit realization,
and projection-normalized support endpoints are explicitly present. The generic
strict normalization is an equality of total-limit maps on a whole diagram; it
applies in particular to `frameworkStrictQuotients` of one flat K-flat complex.
The item's comparison now asserts compatibility between this independently
constructed arrow and the specified completed PBC arrow. The source's proof
steps 6 and 8 require the genuine presentation transport and endpoint calculation;
they are no longer consequences of a definition involving S and T.

Secondary H3: `OpenDiagram.identity`, `FurtherOpen.second`, `FurtherOpen.outer`,
and `OpenDiagram.automorphism` now provide actual geometric diagrams.
`frameworkOpenRestrictionCoherence` states identity and successive-open equations
on those diagrams. The two Frobenius theorems use actual finite-field models,
geometric Frobenius, the rebuilt exchanges, and the specified comparison maps,
then state the induced fixed-pair lift at raw finite and common coefficients.
`diagramNaturality` uses `IntegralSquare.sfExchange_spec`, hence the rebuilt arrow.
The older generic pasting and fixed-pair lemmas are retained as algebraic helpers,
not as substitutes for these geometric statements.

The initial compile also found two field-selector parse errors in the saved
framework tower adjunction/mate definitions. They were repaired, and long lines
in the saved Frobenius statements were wrapped. The new node and declaration
lists are recorded; the item's mathematical statement and proof are unchanged.

## Validation

All validation uses scompile.py and deliver2.py; no global build, live-file edit,
or direct Git mutation was run. Final per-file compilation and dry-run results
are recorded below after the checks complete.

A serial rereading against both H3 points checked the defining equations, not only
the module names: sfExchange_spec contains only frameworkExchange, and the latter
contains solely framework endpoint realizations and frameworkAmbientExchange.
The strict normalization refers to frameworkTowerExchange and framework completed
rings; no S, T, coefficient-presentation J or cbcRealizationStrict occurs there.
The identity equation uses G.identity; the pasting equation uses an actual
FurtherOpen and its second/outer diagrams. The Frobenius conclusions now use
HasExchangeFixedPairSupportLift to avoid repeating the same large common-stage
functor types: this predicate fixes both arrows and all four comparison maps and
requires the same natural IsoAlgebra lift, rather than choosing new actions.
Timing diagnostics were removed after identifying repeated kernel checking.
The generic DiagramComparisonBundle was moved outside the geometric-variable
context, with no field or universe restriction changed.

Final retained-packet self-check (2026-10-19): the required initial
`deliver2.py Q09 lem-zl-framework-pbc-open-exchange-comparison --no-push`
passed preflight and all five per-file compiles, producing dry-run commit
`e0c5b12b7e`. The saved repair was retained. A further serial reading checked
`IntegralSquare.sfExchange_spec`, the framework proper/open and strict-tower
mates, `frameworkAmbientExchange_strict`, the quotient-unit realization,
and the projection-normalized support realization against both returned H3
points. It also checked the actual identity, successive-open and descended
Frobenius statements. Relative to current shared main, the original item
changes only `lean` and adds the four new definition ids to `stmt_deps`; its
mathematical statement and proof are unchanged. All edits and validation
remain confined to the authorized sandbox and delivery wrappers.
