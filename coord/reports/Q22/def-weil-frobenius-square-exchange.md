## Worker report

The delivery constructs the exchange at all four coefficient stages. Its principal
entry point is `WeilConjectures.FrobeniusExchange.frobeniusCommonStage` in
`Sheaf.Paper.FrobeniusGeometricExchange`. The imported
`Sheaf.Paper.FrobeniusSquareExchange` owns its normalized coefficient descent. The finite and integral entry points are
`frobeniusDirectFinite`, `frobeniusCompactFinite`, `frobeniusDirectIntegral` and
`frobeniusCompactIntegral`; `frobeniusRational` is literal scalar localization.
`frobeniusDirectModel` selects the actual Frobenius square, and
`frobeniusCompactModel` retains the specified compactification over the finite field.
The common-stage entry point takes one of these recipes. No exchange morphism or
scalar comparison is an input to either recipe.

The definitions contain real data. The named postponed theorems have source and
natural-language proof docstrings and are recorded among the owning node's
`lean.declarations`. This is a statement delivery; their proofs remain `sorry`.
The item statement has not been changed.

Hypotheses and clauses of the item, in order:

1. The finite-field datum is `D : FiniteFieldDatum`; its existing fields supply
   `p`, `k₀`, `k`, the prime-power cardinal and the geometric field Frobenius.
   `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` are the prime hypotheses at the
   geometric integral, rational and common-stage entry points. The derived
   residue-field invertibility instances come from `sfWeilPrimeInvertible`; the
   ground-field unit comes from `zlClosurePrimeUnit`. Neither is a new assumption.
2. Finite coefficients are `Padic.coefficientExtensionRing l E n`, with `hn : 1 ≤ n`.
   `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
   `[FiniteDimensional ℚ_[l] E]` give the coefficient extension. For the algebraic
   closure `Ω : Type v`, the independent universes are retained; `Index l Ω`,
   `Coefficient l Ω E` and `coefficientInclusion` are the existing finite subfield
   stages and their actual inclusions. The finite and rational constructions are
   stated for any finite extension and then specialized to these subfields.
3. `X₀ Y₀ : Over (Spec (.of D.k₀))`, with locally-finite-type and quasi-compact
   structure maps, express finite-type models. `f₀ : X₀ ⟶ Y₀` is the model map.
   The separated, locally-finite-type and quasi-compact hypotheses on `f₀.left`
   are the stated separated finite-type hypothesis. `fiberMap` is an abbreviation
   for the existing `zlFiberMap`, not a new geometric fiber. The inherited
   properties are named in `fiber_finiteType` and `fiberMap_properties`.
4. `galois D T₀` is exactly `D.galoisMap` for the geometric Frobenius of `D.k/D.k₀`.
   The commuting-square equality and Cartesian proof are the specified projections
   of `D.frobenius_square_cartesian`. These are scheme maps; no `D.k`-linearity
   instance is imposed on either horizontal Frobenius. The finite ambient mate is
   also defined without any finite-type hypothesis on a geometric fiber over `k₀`.
5. `finiteExchange` is literally `mateEquiv` for the actual derived
   `sfIntrinsicConstantModuleAdjunction`, applied to `sfIntrinsicDerivedPullbackComp` and the
   commuting-square equality. Thus it has the stated unit/compositor/counit word.
   `finiteTensorExchange` conjugates by `openSquareDerivedPullbackModel`, whose
   ordinary comparison is uniquely fixed by the actual units on scalar sections.
   `finiteDirect` and `frobeniusDirectFinite` specialize it. The input category is
   all of `proEtaleDerivedCategory X A`; constructibility is not added to this
   ambient definition. It restricts to the finite constructible domain when used
   there.
6. Whole strict coefficient systems are the existing
   `coefficientSequenceModules` and `coefficientSequenceDerived`; their ring sheaf
   and semilinear transitions are unchanged. `systemDirect` derives the actual
   section direct image, and `systemAdjunction` derives its ordinary adjunction.
   `systemSquare` is the existing normalized system pullback compositor.
   `systemExchange` applies `mateEquiv` in this whole derived category, before
   evaluation or inverse limit. `systemExchange_evaluation` states the finite
   mate equation for that already constructed transformation. Evaluation index
   `n : ℕ` corresponds to exponent `n+1`, so every quotient exponent is positive.
7. `models` selects one global normalized model supplied by
   `integralPullbackComparisonRealization`; every coefficient field uses the
   `coefficient` projection of that same model. `reduction` is its actual coherent
   reduction functor, with the dependency's one-K-flat-complex quotient-generator
   normalization and quotient-induced transitions. It is not a separately chosen
   family of finite derived objects. `scalarModels` uses the scalar projection of
   the same global model, so source and target reduction diagrams agree.
8. `coefficientSequenceLimit` is the existing exact scalar restriction followed
   by total derived inverse limit. `realize H` is reduction, `H`, then this limit.
   `sourceComparison` is the normalized integral pullback realization followed
   by the whole-system reduction/limit counit. This is alpha. Its invertibility
   on the required domain for an isomorphism horizontal arrow is stated by
   `directAlpha_isIso` and `compactAlpha_isIso`.
9. `reductionPullbackIso` is the canonical pullback/reduction counit, made into an
   isomorphism by the existing whole-system effectivity theorem. Its inverse,
   followed by `H` and the limit, is beta. `integralExchange` is exactly alpha,
   then limit of the specified system map, then beta, in Lean's left-to-right
   composition order. `directIntegral` restricts this natural transformation to the recorded full
   constructible categories. `compactIntegral` acts on the recorded
   `sfCompactSupportFiniteIntegralFunctor`: `compactRealization` is chosen from
   `compactRealization_existsUnique`, whose `CompactRealizationSpec` fixes every
   finite projection to `sfCompactSupportFiniteReductionIso`. The latter is the
   actual Roos projection adjunct, also retained by
   `sfQcqsCompactSupportRealization`. `compactAlpha` starts with this identification
   and the system pullback/counit; `compactBeta` uses its inverse at the pulled
   input after the effective pullback counit inverse. Thus the entire compact
   integral exchange has the stated alpha-shriek–L(e)–beta-shriek formula.
   `directImage_constructible` and `compactImage_constructible` state the
   required bounded output; `directImage_roos` ties the direct-image model to the
   recorded `SfIntegralDirectImage` Roos object. These are simultaneous-system
   presentations of the existing operations, retaining their actual quotient
   transitions and total-limit projections.
10. `operationReduction` is the actual whole-system counit.
   `compactOperationReduction` transports it from the recorded integral Rf_!
   by the same projection-normalized identification. The equalities
    `directIntegral_reduction` and `compactIntegral_reduction` state compatibility
    of the constructed integral exchange with it and with the specified
    pullback counits. Together with finite evaluation, these give the stated
    reduction property. That property is not used to choose an integral map.
11. `localizedHom` is `F.mapLinearMap.baseChange` on the actual raw localized Hom
    modules. `localizedFunctor` keeps the integral object representative, and
    `localizedTransformation` sends a component to its image under
    `sfRationalConstructibleLocalization`. `modelRationalExchange` is this
    construction for the source and target composites. `localizedPullback_eq`
    identifies the localized pullback with the recorded `rationalDerivedPullback`
    using its pure-tensor normalization. No rational object is reduced modulo a
    uniformizer, and no Karoubi completion occurs.
12. The scalar comparisons are constructed, not supplied: `systemDirectScalar`
    is the mate of the actual system scalar/pullback comparison;
    `systemOpenScalarInv` is the inverse left-adjunction mate and
    `systemCompactScalar` its proper/open composite. `coefficientExchange`
    realizes these using the same alpha/counit/beta formula. `modelScalarMap`
    restricts this actual map, and `modelScalarMap_isIso` states its finite-free
    completed coefficient property. It does not assert flatness of a ramified
    map of finite quotient rings. `pullScalar` is fixed componentwise by the
    existing `integralPullbackScalarComparison`. `modelSourceScalar` and
    `modelTargetScalar` compose these comparisons in the prescribed orders.
13. `modelRationalScalar` is uniquely fixed by localization of these integral
    components. `stageBeta` expresses it in the existing stage-system transitions
    using `operationStageTransitionIso`. `stageBeta_coherence` states the full
    tower cocycle, including repeated fields. `stageExchange_compatible` states
    compatibility of the actual exchanges with those actual betas. `stageAction`
    and `stageExchange` therefore use the existing `StageSystem.Morphism` and
    `StageSystem.Morphism.Hom` interfaces. `commonStageExchange` is exactly
    `StageSystem.Morphism.descNatTrans`; at `(E,K)` its component is the class of
    the constructed rational exchange at `E`, on all common-stage representatives.
14. `c₀ : Compactification f₀.left` is the chosen factorization over `k₀`.
    `geometricCompactification` uses the existing
    `zlCompactificationMiddle`, `zlCompactificationOpen`, and
    `zlCompactificationProper`, all base-changed by `fiberMap`.
    `geometricCompactification_properties` states openness, properness and the
    factorization equality. The middle horizontal map is `galois` of that very
    retained middle model. Its proper and open squares are supplied by the
    existing Frobenius-square theorem.
15. `finiteCompact` is exact `j!` whiskering of `finiteTensorExchange` along `p`,
    followed by proper pushforward of `constantOpenSquareExchange.hom`.
    `frobeniusCompactFinite` specializes it to the geometric compactification.
    `systemCompactExchange` is the identical recipe for the whole system:
    exact `systemDerivedOpen`, proper `systemExchange`, and
    `systemOpenExchange.hom`. `compactIntegral`, its scalar comparisons,
    localization and common-stage descent keep this same `c` at every index.
16. `origin` is the existing etale comparison inverse image followed by canonical
    intrinsic coefficient realization. `originUnderlyingPullback` uses the actual
    `comparisonUpperStarCompUpperStarIso`; `originPullback` descends it exactly
    and changes to the recorded tensor-pullback coordinates. Given the retained
    `L` and `alpha`, `pulledOriginWitness` uses precisely `etalePull gX L`.
    `etalePull_lowerBound` preserves the same integer bound `b`.
    `pulledCompactOrigin` retains this object, the exact pulled Plus antecedent,
    and this specified comparison. Its induced functor has every ambient map.
17. `transportCompact` uses the coefficient-descent helper's actual
    `intrinsicCompactificationComparison ... d c`, evaluated at the original
    witness and `pulledCompactOrigin`. It is pullback of that comparison, then
    the specified `c`-exchange, then the inverse comparison on the pulled input.
    It is a natural transformation on the witnessed domain. No comparison map
    is a free parameter. Underlying-functor coherence is asserted in its own
    dependency; independence of the Frobenius transformation from `c` is not
    asserted.
18. Every exchange is a `NatTrans`, a mate, or a composite/whiskering/descent of
    natural transformations. The cohomology case is specialization to the
    terminal `k₀`-model and its structure map. It uses the very same direct or
    chosen compact recipe. There is no theorem asserting that either final
    Frobenius exchange is invertible.

Dependency declarations read and used, directly or through their canonical
specializations (modules are the recorded modules):

| Dependency module | Declaration or interface |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `FiniteFieldDatum`, `geometricFiber`, `galoisMap` |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | `Scheme.intrinsicFiniteTorsionConstructible` |
| `Sheaf.Paper.SfIntegralConstructible` | `sfIntegralConstructible`, full constructible category |
| `Sheaf.Paper.SfRationalizationKaroubi` | `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | `Stage`, `stageSystem`, finite subfield stages |
| Mathlib scheme morphism-property modules | `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsProper` |
| `Sheaf.AlgebraicGeometry.FrobeniusDetailed` | `FiniteFieldDatum.geometricFrobenius` |
| `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` | `ChosenCartesianSquare` and its square convention |
| `Sheaf.SixFunctors.FrobeniusSquareCartesian` | `FiniteFieldDatum.frobenius_square_cartesian` |
| `Sheaf.Paper.DerivedPullbackTensorHom` | `integralDerivedPullback`, `constructibleIntegralPullback`, scalar comparisons, `operationStageTransitionIso` |
| `Sheaf.Paper.SfDerivedDirectImage` | `SfIntegralDirectImage`, finite direct images and normalized transitions |
| `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` | `sfIntrinsicExtensionByZero`, `sfIntrinsicModuleEquivalence` |
| `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` | `sfIntrinsicCompactSupport` |
| `Sheaf.Paper.CondensedAmbientExchange` and `Sheaf.Paper.PbcActualRingedExchange` | retained general ambient interfaces; the ordinary finite specialization is owned by the system helper |
| `WeilConjectures.Compactification.Refinement` | `Compactification.Refinement`, actual refinement morphisms |
| `WeilConjectures.Compactification.CategoryBaseChange` | compactification cofilteredness over a field |
| `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare` | `FiniteFieldDatum.frobenius_open_square` |
| `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` | `constantOpenSquareExchange`, `openSquareDerivedPullbackModel` |
| `Sheaf.Paper.CompactificationCoherence` | landed `compactification_coherence`, normalized by `refinementComparisonIsomorphism`; intrinsic coordinate transport owned here |
| `Sheaf.Paper.ExchangeProjectionSuppliedDomains` | the ambient-mate/chosen-compactification recipe |
| `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` | `scalarReductionDerivedExtension`, exact restriction |
| `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` | completed-to-finite constant scalar maps |
| `Mathlib.CategoryTheory.Adjunction.Mates` | `mateEquiv`, `TwoSquare` |
| `Sheaf.Paper.CompletedRlimFunctor` | strict-tower total derived-limit computation |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | recorded finite coefficient comparison theorem signatures, whose normalized system specialization is explicit here |
| `Sheaf.Paper.PbcDescentFunctors` and `WeilConjectures.CategoryTheory.StageSystem.Functor` | actual compatible-transformation descent |
| Mathlib proper base change | stability of properness under base change |
| `Sheaf.Paper.QcqsCompactSupportRealization` | normalized simultaneous compact-support realization |
| `Sheaf.Paper.SemilinearDerivedSections` | whole-system ordinary-derived adjunction and evaluation calculus |
| `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` | restriction exactness |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | `sfIntegralDirectImage_constructible` |
| `Sheaf.Paper.IsomorphismDerivedPullback` | isomorphism pullback preserves the integral domain |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | compact-support bounded constructibility |
| `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` | canonical etale/pro-etale pullback comparison |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | actual system pullback, scalar extension, compositors and scalar/pullback comparison |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | `integralPullbackComparisonRealization`, normalized global system data |
| `Sheaf.SixFunctors.OpenTensorNormalization` | `OpenTensorNormalization.exactDerivedAdjunction` |
| `Sheaf.Paper.WeilCompactSupportCohomology` | `zlCompactificationMiddle/Open/Proper`, `zlClosurePrimeUnit` |
| `Sheaf.Paper.WeilIndSheafCategory` | `zlFiberMap` |
| `Sheaf.Paper.SfWeilSheafComplex` | `sfWeilPrimeInvertible` |

The original 34 statement dependencies were read, including their recorded full
signatures/docstrings or Mathlib matches. The added statement dependencies are
already landed except the three helper definition nodes described below.

Edge cases checked: positive exponent one; the index shift `n ↦ n+1`; the empty
scheme and zero complex; identity horizontal maps and identity refinements;
repeated coefficient fields and the identity inclusion; ramified coefficient
extensions (no finite-quotient flatness assumption); independent site/closure
universes; nonseparated finite-type structure schemes with separated relative
`f`; horizontal Frobenius maps that are not ground-field linear; and the terminal
base used for cohomology. Bounded-below etale witnesses retain their antecedent
and their lower bound. All integral reductions precede localization. No unit
statement or item statement correction was needed; no disputed statement remains.

Searches for an existing item: launcher `msearch.py` LeanFinder query for derived
direct-image/compact-support geometric-Frobenius exchanges at four coefficient
stages returned eight unrelated ring/Witt hits; Loogle query
`CategoryTheory.mateEquiv, CategoryTheory.whiskerLeft` returned no exact item;
Mathlib grep `frobenius.*[Ee]xchange|Frobenius.*[Ee]xchange|FrEx` returned zero hits.
LeanSearch for natural Frobenius exchange via strict semilinear coefficient
systems returned eight unrelated semilinear algebra results. `rg` in both
`WeilConjectures/` and `lean/Sheaf/` found underived/fixed-scalar Frobenius and
specialized proper/common-stage operations, but no declaration of this item.
The upstream item-id search had no hit. The actual search records remain in
`searches.jsonl`; the new node records its additional exact queries and results.

## New nodes

`def-weil-operation-exchange-coefficient-descent` owns the literal coefficient
passage and intrinsic coordinate helpers in `Sheaf.Paper.FrobeniusSquareExchange`.
It is the helper whose geometric specialization is the item, now in the sibling
`Sheaf.Paper.FrobeniusGeometricExchange`.

`def-weil-exact-derived-adjunction` records the existing exact derived adjunction
in `Sheaf.SixFunctors.OpenTensorNormalization`. Its full signature quantifies over
both abelian categories, their common explicit object/morphism/derived universes,
the additive functors, all four exactness instances, and the specified adjunction.
The result is the adjunction of their exact derived functors. Mathlib LeanSearch
and LeanFinder found the generic `Adjunction.localization`/`Adjunction.derived`
APIs; Mathlib grep found no exact named specialization. Project grep found the
existing definition at line 356. DAG grep found it only among normalization lemma
helpers, and `blueprint_refs.py search 'exact derived adjunction'` found no node.
The new record reuses that exact definition and its module, without duplicating it.


`def-weil-system-operation-exchange-realization` names the missing concrete helper:
realizing a specified transformation of whole strict coefficient-system operations
by coherent reduction, exact scalar restriction and total inverse limit, with the
normalized pullback/scalar counits. It supplies actual derived section direct
image and exact open extension in this specialization, their mates and their
bounded constructible restrictions. Its source is the item's whole-system
paragraphs and Zheng Construction 4.1/Lemma 4.10. The existing system node supplies
pullback/scalar categories and normalizations, not this realizer of direct/open
mates. Blueprint search for `simultaneous-system realization` returned zero nodes;
Mathlib/project/side-library searches found no exact declaration. LeanFinder and
LeanSearch results were generic categorical or semilinear results, recorded in
the new node. This is a concrete specialization of the existing calculus, not a
new coefficient category. Splitting this helper also keeps each file below the
single-file compilation limit.

`def-weil-operation-exchange-coefficient-descent` owns the retained support recipe
and its coefficient passage in `Sheaf.Paper.FrobeniusSquareExchange`, with
`commonStageExchange` as its principal declaration. It builds on the existing
`StageSystem.Morphism.descNatTrans`, rather than repeating general descent.
Its statement introduces finite-type schemes over an ell-invertible field,
the separated finite-type relative map and arbitrary scheme automorphism
horizontals; `SupportModel` keeps either the commuting direct square or the
specific compactification with its proper commuting and open Cartesian squares.
`modelRationalExchange` localizes the constructed integral map; `modelScalarMap`,
`pullScalar`, `modelRationalScalar` and `stageBeta` supply the actual coefficient
comparisons; `stageExchange` and `commonStageExchange` give canonical morphism
classes. The first sections also record the finite mate specialization and the
retained-antecedent compactification transport detailed in clauses 4–5 and 16–17
of the worker report. Source and full natural-language postponed-proof plans
are retained in every declaration's docstring, now tagged to this owning node.

Fresh LeanFinder and LeanSearch queries for literal localization and common-stage
coefficient descent returned generic categorical localization and unrelated
condensed/sheaf declarations. Mathlib grep for commonStageExchange,
modelRationalExchange, stageExchange_compatible and transportCompact had no hit;
project/source grep also had none. Blueprint search for 'operation exchange
coefficient descent' found no node. DAG grep returned fix-lem-exchanges and
lem-pod-weil-frobenius-compact-support-exchange, which are compatibility and
isomorphism theorems, not this concrete construction. The general
prop-weil-pbc-descent-functors is used for the descent step; it does not define
the coefficient comparisons of this operation recipe. Exact queries and results
are recorded in the new helper's mathlib_searches and searches.jsonl.

## Repair of immutable head de4b06279401, 2026-10-18

Finding 1 (H13/H4): the packet no longer contains the node
`prop-compactification-coherence-detailed` or the former
`IntrinsicCompactificationCoherence.lean` module. Q116's landed node record and
`Sheaf.Paper.CompactificationCoherence` are preserved and imported. The previous
report's duplicate-import explanation is withdrawn: these interfaces coexist.
The intrinsic-coordinate declarations moved into
`Sheaf.Paper.FrobeniusSquareExchange`, owned and enumerated by
`def-weil-operation-exchange-coefficient-descent`. Their constructions are
unchanged. `refinementIntrinsicOrigin` transports a recorded retained witness
using its actual antecedent, realization unit and fixed comparison.
`intrinsicCompactificationComparison_refinement` states that the intrinsic
pairwise comparison evaluated at this witness equals the landed
`refinementComparisonIsomorphism`, conjugated by `fixedCompactModel` at its two
endpoints. Its docstring gives the normalization and unit/counit calculation;
its proof is postponed. The helper node states this coordinate-compatibility
clause explicitly. `transportCompact` still uses the uniquely normalized actual
comparison, its pullback, the chosen exchange, and its inverse on the precisely
pulled witness. No comparison is introduced as an input.

Finding 2 (H3): retrieved the archived reviewer fix from
`local/verdicts/2/6bd5f5c837bdad3d0fef1e64b1d4cade868a0d45/fixes/` on the server.
`SystemOperationExchangeRealization.lean` now matches that fix byte for byte.
The evaluation theorem is placed after the canonical evaluation definitions;
its equation uses `systemDirectEvaluation` and `systemPullEvaluation.inv`
explicitly, at every system object and exponent n+1. Existential d/px/py no
longer occur. The definition of the mate, coefficient system, adjunctions and
all other previously accepted clauses are unchanged.

The delivered theorem `intrinsicCompactificationCoherence` now serves solely as
the intrinsic-coordinate transport property of the existing coherence result.
It does not replace its DAG node or publish a competing dependency record.
The extra normalization theorem connects the pairwise comparison used downstream
to the canonical landed refinement, including identity and noncartesian
refinements. Its formula determines comparison data, so the existing extraction
of the comparison from unique coherence remains non-hollow.

## Second reading by Q22

This in-thread self-check reads the node, its new helpers and the final files;
no additional agent was started. The two return findings are repaired in the
actual code and packet. The immutable-head content was retained except the
explicit evaluation equation, ownership/import change, and the witness transport
and normalization theorem requested by the return. The original 18-clause
mapping above still applies. The new witness transport keeps exactly O.2.L;
its alpha is exact-derived composition followed by the realized recorded alpha.
The normalization theorem uses the landed refinement map with the same field,
prime, coefficient field, exponent, morphism, refinement and witness. Its two
coordinate comparisons have the same endpoints as the intrinsic component.
Identity refinements, arbitrary ambient witness maps and noncartesian
refinements are included. The exchange still uses the same compactification
before and after coefficients. No mathematical statement of the item or any
landed dependency changes. Every declaration moved from the removed module
is listed under the coefficient-descent helper and carries its blueprint tag.
All universes and variables are explicitly bound. Definitions contain real data;
each postponed theorem is named and has its source and complete proof plan.

## Repair validation, 2026-10-18

The final scompile.py invocation compiled all three delivered modules cleanly.
Library checks: SystemOperationExchangeRealization 21.9 s,
FrobeniusSquareExchange 37.0 s, FrobeniusGeometricExchange 5.7 s.
The private coefficient-module check took 39.7 s; all preliminary and sandbox
checks also passed below the prescribed 60-second limit. There were no warnings.
The archived evaluation fix remains byte-identical. Static checks confirm that
every declaration has exactly one owning module/node, every node signature is
verbatim, every line is at most 100 characters, and the existing item differs
from the current shared record only in lean and its new-helper stmt_deps.
The Q116 coherence node is not in the packet.
