## Worker report

Repair of return L, immutable head dbf528add82f. The old `WeilPBC.FiniteStagePairCategory`
was an arbitrary interface: its operations were untyped and its main assertions were
free `Prop` fields. Both old modules have been replaced. There is no remaining
`WeilPBC` placeholder, arbitrary object family, arbitrary representative relation,
or unconstrained proposition standing for a conclusion.

`Sheaf.Paper.FiniteStagePairCategory` now constructs
`AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory` on the actual recorded raw rational
PBC categories. It reuses the upstream `CategoryTheory.StageSystem.PairCategory`.
`Sheaf.Paper.CommonStageCalculus` states the calculus for this concrete system as
`AlgebraicGeometry.Scheme.commonStageCalculus`, and gives the explicitly constructed
shift functors, unit and addition comparisons and finite-stage inclusion comparisons.
The generic supporting statements are in `CategoryTheory.StageSystem`; the final theorem
has the concrete scheme/coefficient binders and does not assume an arbitrary stage system.

Hypotheses and clauses:

- Prime ell: `l : ℕ` and `[Fact l.Prime]`. The fixed closure is `Ω : Type c`,
  `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The scheme is `T : Scheme.{u}`, `[IsNoetherian T]`,
  `hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m`, and
  `hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`.
- Finite stages are `Padic.FiniteCoefficientFields l Ω`, not finite sets. Their
  objects are `PbcRationalCategory T (pbcStageDatum l Ω E) (pbcStageUniformizer l Ω E)`.
  `pbcStageDatum` specializes the recorded `pbcIntegralDatum`. The actual field is
  transported along `Shrink.algEquiv`; the closure and scheme universes are independent.
- Pair objects, representatives, Hom quotient, transport and composition are the actual
  upstream `StageSystem.PairCategory`, `.Rep`, `.Rep.Rel`, `mkHom`, `S.tr`, and category
  instance. `Rep X Y` fixes both endpoints; `u` has precisely the common-stage Hom type.
  `S.tr` is inverse source associator, mapped arrow, then target associator in Lean's
  left-to-right composition convention. It is defined only for a stage inclusion.
- Reflexivity, symmetry and transitivity are `CommonStageCalculusSpec.relation`, an actual
  `Equivalence` of the defined eventual-equality relation.
- Additive transport and `(u_N)_P = u_P` are `.transport_add` and `.transport_cocycle`,
  literal equalities of typed finite-stage arrows.
- Representative-independent sums and zero are `.operations`, the actual
  `PairPreadditiveNormalized` equations on the quotient. Negation and identity are
  `.negation` and `.identity`. `.composition` specifies the common-stage composite for
  every chosen common upper field. Category laws are the upstream quotient category
  laws; the unique preadditive structure fixes addition by these formulas.
- Additive category means that actual `Preadditive` structure together with
  `.biproducts : HasFiniteBiproducts S.PairCategory`, including the empty biproduct.
- Every finite diagram is `.finite_diagram`: arbitrary finite object and arrow index
  sets, a typed graph, and all arrows represented at one field. Objects identify with
  their scalar extensions by the upstream `S.isoToStage`; `mkHom_eq_isoToStage` gives
  the conjugation formula. Specify composites as further graph arrows. The upstream
  `mkHom_comp_mkHom` computes their stage maps, and `.equalities` moves their asserted
  equations to one further common field. Thus both arrows and equations are simultaneous.
- Equality holds exactly after a further common stage: `.equalities` is an iff for an
  arbitrary finite family of parallel representatives, with one stage above a prescribed
  starting field. `pbcFiniteEqualities_detection` states the same supporting assertion.
- `(E,K)[1] = (E,K[1])` is `.shift_objects`; `.shift_maps` displays the full formula
  `sigma_source.hom ≫ shift.map u ≫ sigma_target.inv`. The source sigma is the normalized
  `pbcScalarCommShift`, inherited from the ambient tensor/derived restriction adjunction
  through the full integral inclusion and raw scalar localization.
- Well-defined additive shift with inverse `[-1]` is the actual `pbcPairShift`, constructed
  from an upstream stage-system morphism with sigma coherence. `pbcPairShiftZero`,
  `pbcPairShiftAdd` and `pbcPairHasShift` give its coherent shift structure.
  `.shift_additive`, `.inverse_additive`, `.inverse_left`, `.inverse_right` render the
  additive inverse-shift assertion. All comparisons have concrete stagewise components.
- Each inclusion commutes with shifts by `pbcStageInclusionShiftIso` and the installed
  `pbcStageInclusionCommShift`; `.inclusion_normalization` fixes the precise comparison.

The rational shift has a unique specification: its functors are
`ScalarLocalization.map` of the integral signed reindexing, and its zero/addition
components are the localized integral components. The integral subcategory uses
Mathlib's inherited full-subcategory shift. The tensor shift comparison is the mate of
exact scalar restriction's shift, and its rational version is uniquely fixed by the
integral/rational comparison. No shift or comparison is chosen from bare `Nonempty`.
The completed coefficient map is uniquely fixed by all finite quotient projections.
The integer-ring inclusion reuses the published
`WeilConjectures.integralScalarIntegerInclusion` from
`Sheaf.Paper.IntegralScalarExtensionWellDefined`, lifted through `ULift`.

Dependencies used: `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`,
`Padic.FiniteCoefficientFields` and its compositum/base/properties;
`Sheaf.Paper.PbcRationalCategory`, `Scheme.PbcRationalCategory`,
`Scheme.pbcRationalization`, `Scheme.PbcRationalDerivedCategory`;
`Sheaf.Paper.BoundedConstructibleComplete`, `Scheme.PbcBoundedConstructibleComplete`,
`Scheme.PbcIsBoundedConstructibleComplete`, `Scheme.pbcIntegralDatum`, `Scheme.pbcUniformizer`;
`Sheaf.Paper.BoundedConstructibleTower`, the actual `pbcDerivedExtend`,
`pbcDerivedScalarAdjunction`, `pbcDerivedRestrictComp`, and tensor-section/counit helpers;
`Sheaf.CategoryTheory.ScalarLocalization`, `ScalarLocalization.map`;
`WeilConjectures.CategoryTheory.StageSystem.Basic` and `.Functor`, the actual pair quotient,
transport, object isomorphisms and descent of stage-system morphisms;
Mathlib `ObjectProperty.hasShift`, `commShiftι`, `Functor.CommShift.ofComp`,
`Adjunction.leftAdjointCommShift`, and `HasFiniteBiproducts`.
The stated proof dependencies are imported using their published current modules.

Edge cases checked: identity and repeated coefficient fields take the literal identity
branch and the normalized tensor units; ramified extensions map maximal ideals into
maximal ideals and hence map every same-exponent ideal power into the target power,
without assuming uniformizers coincide. Quotient exponent is always `n+1`. Common-stage
transport is not assumed injective. Representatives with different endpoints cannot be
compared or added. Composition requires exactly matching middle objects. Empty graphs
and empty equality lists use the base finite field; equality witnesses can be enlarged
simultaneously. Zero and binary biproducts are included. Negative shifts use the same
signed reindexing construction and coherent inverse comparisons. Independent closure
and scheme universes are handled by canonical small coefficient transport.

Searches: `msearch.py` LeanFinder, query "finite stage pair category common-stage morphism
transport shifts additive category", returned eight generic composable-arrow declarations,
with no complete common-stage additive/shift result. Loogle `CategoryTheory.StageSystem.PairCategory`
returned unknown identifier (the service indexes Mathlib, not the upstream project).
Mathlib grep `StageSystem|PairCategory` in CategoryTheory returned zero. Read-only project
searches found the upstream StageSystem.Basic/Functor construction and the published
`CommonStage` generic additive descent interface. These were read; the upstream quotient
is reused rather than copied. The published concrete PBC specialization and common-stage
shift module were unavailable under `scompile.py --source`. Read-only delivery-branch
inspection found no delivered Q23/Q07/Q16/NQ specialization. The unpublished NQ and NG
sandbox construction was inspected and reused with its canonical tensor normalizations;
the new shift construction and final concrete theorem are part of this repair.
The blueprint source files were read over ssh from the server's literature directory.

No statement was corrected and no STATEMENT-DISPUTED marker is needed. All postponed proofs
are named, source-tagged theorems with natural-language proof plans. Definitions have real
data or use uniquely characterized existence theorems, never unspecified chosen objects.

Repair checks: read the three blueprint source pages (orders 1307--1309) from the
project server and checked the actual upstream `StageSystem.Basic` and
`StageSystem.Functor` signatures. Current `scompile.py --source` reports that neither
`Sheaf.Paper.FiniteStagePairCategory` nor
`Sheaf.Paper.PbcFiniteCompletedCoefficientMap` has a published source. Repeated the
LeanFinder, Loogle and Mathlib grep searches; their results agree with those above.
The finite-biproduct assertion uses `Limits.HasFiniteBiproducts` explicitly, and
the shifted representative supplies its shifted source and target explicitly to
`PairCategory.mkHom`, so the sigma-conjugated morphism has the required endpoints.
The files contain no unscoped heartbeat option.
The scalar-system assembly is an abbreviation, keeping its transition functors
and associators visible to typeclass synthesis at the concrete final theorem.
The integer-ring helper requires a public import because its body is exposed.
The existing sheafification and locally bijective instances are therefore
specialized explicitly to the PBC coefficient universe `u+1` and given priority
over the general tower instances. Both instances reuse the existing canonical
proofs; the scheme and algebraic-closure universes remain independent.

## New nodes

`def-weil-pbc-finite-completed-coefficient-map`: defines the actual integer-ring inclusion,
its finite quotient maps, the unique completed ring-sheaf map fixed by every projection,
and the recorded K-flat ambient tensor functor along it. The coefficient fields are
canonically shrunk independently of the scheme universe, with one explicit field/algebra
interface so different inherited ring-instance paths do not cause repeated conversion. Source: scalar-extension
blueprint order 1307, finite completed coefficient maps. Whole-DAG and blueprint search
found no existing node for this map. LeanSearch for a map of completed coefficient
sheaves was unavailable (Internal Server Error). LeanFinder for the uniquely
projection-normalized finite-extension map returned eight arithmetic adic-completion
maps, none the PBC sheaf map; a successful LeanSearch recheck returned eight
completion, sheafification and p-adic-field results, with no exact PBC map.
Mathlib grep of the coefficient-map names returned zero.
`rg` of the upstream source and published `lean/Sheaf` found no exact completed PBC map.
The more general integral-tower scalar module supplies the exact integer-ring helper,
which is reused; its different completed-ring and category realization cannot directly
supply this PBC completed map. Its owning node
`lem-weil-integral-scalar-extension-well-defined` is cited by the new node.
The exact queries/results are recorded in the node's `mathlib_searches`.

## Dependency modules

`def-weil-pbc-finite-stage-pair-category`: its returned record pointed to the arbitrary
placeholder interface identified by L. The replacement specializes the real upstream
pair quotient to actual raw rational PBC categories and their canonical completed tensor
extension. The integer-ring and limit-projection construction is in the new map node.
Tensor units, integral/rational factorization and associators are uniquely normalized;
the common-stage module fixes shift data on integral objects, tensor Homs, and comparison
components.
Its node changes only in `lean` and records all supporting declarations. The item's
statement and hypotheses are unchanged.

## Second reading by NS

I read the item, both delivered definition records, all three delivered Lean modules,
the current recorded dependency statements and signatures, and the actual upstream
`StageSystem.Basic` and `StageSystem.Functor` sources obtained with `scompile.py --source`.
I also reread the blueprint pages at orders 1307, 1308 and 1309 on the server, rather
than relying on the worker's cached source. For the Stacks references I read
`categories.tex`, `definition-directed-set` (00D3), `lemma-directed-category-system`
(0032), and `remark-trick-needed` (09P8). They concern directedness and replacement of
fixed-category index diagrams; they do not assert the varying-category construction.
The hypotheses on T come from the current pair-category and integral-category nodes,
not from an extra restriction on the Stacks indexing lemma.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Fix a prime ell: `l : ℕ` with `[Fact l.Prime]`. Correct, including ell = 2.
2. Fix its algebraic closure: `Ω : Type c`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
   `[IsAlgClosure (Padic l) Ω]`. Correct: arbitrary chosen closure, with no equality
   imposed between its universe c and the scheme universe u.
3. T is noetherian, finite-dimensional, with ell invertible: `T : Scheme.{u}`,
   `[IsNoetherian T]`, `hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m`, and
   `hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`. Correct inherited hypotheses.
   No separatedness, properness, smoothness, or base field is added.
4. The coefficient index consists of finite intermediate fields, not finite sets:
   `Padic.FiniteCoefficientFields l Ω`, whose source is precisely the subtype of
   `IntermediateField (Padic l) Ω` with `FiniteDimensional`. Correct. Its recorded
   compositum and base field supply `IsDirectedOrder` and `Nonempty`.
5. The coefficient category is the raw rational category, without a Karoubi envelope:
   `pbcStageCategory E = PbcRationalCategory T (pbcStageDatum E)
   (pbcStageUniformizer E)`. I read `PbcRationalCategory`, `pbcRationalization`,
   `PbcBoundedConstructibleComplete`, its three membership conditions, `pbcIntegralDatum`
   and `pbcUniformizer`. Correct: these are the recorded definitions. `Shrink.algEquiv`
   transports the actual finite field, rather than substituting another coefficient
   ring or restricting the closure universe.
6. Objects are pairs (E,K), and representatives from (E,K) to (F,L) carry a common
   overfield M and a map between the two prescribed extensions. Correct:
   `PbcFiniteStagePairCategory` is `(pbcScalarSystem ...).PairCategory`; the upstream
   `PairCategory` has `stage` and `obj`, and `Rep X Y` has `k`, `hX`, `hY`, `u` with
   exactly those dependent source/target types. There is no arbitrary object family
   or relation supplied as a hypothesis of `commonStageCalculus`.
7. Transitions are the specified derived coefficient extensions, with literal
   identity on repeated fields and tensor-normalized associators. Correct:
   `pbcAmbientScalarExtension` is the recorded `pbcDerivedExtend` along the canonical
   completed map; `pbcIntegralScalarExtension` restricts it to the actual full
   subcategories; `pbcRationalScalarExtension_exists` fixes its rationalization by
   equality on the localization composite. `pbcScalarExtension` takes the literal
   identity branch at E = F. Ambient associators are adjunction mates of canonical
   restriction composition; the integral/rational comparison equations fix their
   restrictions. `pbcScalarSystem_units` states the unit normalization.
8. Transport and eventual equality have the exact specified formulas. Correct:
   upstream `S.tr h u` is source associator inverse, mapped u, target associator;
   `Rep.Rel r s` is existence of one further common stage with equal transports.
   The quotient category uses this very relation and these transports.
9. The relation is reflexive, symmetric and transitive: `CommonStageCalculusSpec.relation`
   is `_root_.Equivalence (PairCategory.Rep.Rel ...)`. Correct, with fixed endpoints.
10. Additive transport and its cocycle: `.transport_add` and `.transport_cocycle`
    state literal equalities of finite-stage arrows. Correct: no injectivity of
    transition maps is assumed. Zero and negative transport follow from additivity.
11. Representative-independent addition, zero, negatives, identities and composition:
    `.operations` is `PairPreadditiveNormalized` for the actual installed Preadditive
    structure; `.negation`, `.identity`, and `.composition` give the remaining
    formulas, the last at every chosen common overfield. Correct. The normalization
    theorem uniquely determines the structure on the existing Hom quotient; the
    upstream category already gives associativity and identity laws.
12. The pair category is additive: its actual `Preadditive` instance together with
    `.biproducts : Limits.HasFiniteBiproducts S.PairCategory`. Correct; the latter
    includes zero and binary sums, and does not mean merely preadditive.
13. Every finite diagram, including composites and equalities, has one field of
    definition: `.finite_diagram` quantifies finite vertex and arrow types, a typed
    graph, and representatives at a single M. Correct in conjunction with
    `.composition` and `.equalities`: include each specified composite as a graph
    arrow, then move all its asserted equations to one larger stage. Object
    identifications are the upstream `S.isoToStage`; the exact conjugation formula
    is the existing `PairCategory.mkHom_eq_isoToStage`. This is representation up
    to the prescribed object isomorphisms, not equality of pair object stages.
14. Equality is detected exactly at a further common stage: `.equalities` is an iff
    for every finite family of parallel representatives, above any prescribed m.
    Correct: it includes both directions and a simultaneous witness. The existing
    upstream `PairCategory.mkHom_eq_mkHom_iff'` supplies the single-equation criterion.
15. (E,K)[1] = (E,K[1]): `.shift_objects`. Correct literal pair-object equality.
    The stage shift is the inherited signed reindexing, rationalized by the exact
    `ScalarLocalization.map` formula in `PbcRationalShiftNormalized`.
16. [M,u][1] is sigma-source, u[1], inverse sigma-target in Lean's left-to-right
    composition order: `.shift_maps`. Correct endpoints and direction.
    `pbcScalarCommShift` is fixed by compatibility of the integral/rational square,
    with the integral comparison inherited from the derived restriction-adjunction
    mate. It is not a freely chosen natural isomorphism.
17. Well-defined additive shift and inverse [-1]: `pbcPairShift` uses the existing
    stage-morphism descent, so equivalent representatives have the same image;
    `.shift_additive`, `.inverse_additive`, `.inverse_left`, `.inverse_right` state
    the required additive autoequivalence. Correct. `pbcPairShiftZero` and
    `pbcPairShiftAdd` explicitly use the images of the stagewise comparisons,
    so their data are fixed and the inverse comparisons are the prescribed ones.
18. Every stage inclusion commutes with shifts through the specified comparison:
    `.inclusion_comparison` and `.inclusion_normalization`, using
    `pbcStageInclusionShiftIso` and the actual installed CommShift instance.
    Correct: the comparison is the inverse of the existing
    `Morphism.ιCompFunctorIso`, with its zero/addition laws retained.

Edge cases: no finite graph or equality family is assumed nonempty; the recorded
base field covers the empty case, and the equality family can be enlarged above m.
`HasFiniteBiproducts` includes the zero object and empty sum. The empty scheme is not
excluded. Quotient index n = 0 means exponent n+1 = 1 throughout. Repeated fields
and identity inclusions are retained. Ramified extensions need only the inclusion
of maximal-ideal powers, not equality of uniformizers. Negative and zero shifts
use the same coherent HasShift construction. Arbitrary finite index types cause
no cardinality exclusion: finite types in other universes have equivalent finite
small models. The scheme, closure, site-object, site-morphism and coefficient
universes were checked independently; site coefficients remain in u+1.

Independent searches used other terminology than the worker:

- LeanFinder: `filtered category colimit finite diagrams simultaneous representatives
  equality shifts`. Eight hits, including `Functor.ιColimitType_eq_iff_of_isFiltered`,
  `Types.FilteredColimit.isColimit_eq_iff`, and `IsFiltered.sup_exists`. These concern
  fixed-category colimits and do not give the concrete PBC additive/shift assertion.
- Loogle: `CategoryTheory.Functor.CommShift`. Twelve hits, including `CommShift`,
  `CommShift.ofIso`, and `CommShift.ofHasShiftOfFullyFaithful`. The standard notion
  and transport APIs are reused; none states this pair-category calculus.
- LeanSearch: `canonical ring sheaf map on completed adic coefficients induced by
  finite field inclusion`. Eight hits about arithmetic completions and ordinary
  ring maps, none about the recorded PBC coefficient sheaves.
- LeanFinder: `completed coefficient sheaf map compatible finite quotient projections`.
  Eight hits about ordinary adic completion projections and unrelated sheaf maps,
  none giving this coefficient extension on the PBC sheaf realization.
- `rg` of Mathlib CategoryTheory, upstream `WeilConjectures`, and published `lean/Sheaf`
  for `PairCategory`, `pbcCompletedScalarMap`, `pbcScalarSystem`, and
  `CommonStageCalculusSpec`, plus reading the current StageSystem modules, found the
  quotient and functor descent but no complete concrete calculus or completed PBC
  coefficient map. DAG searches for completed coefficient/scalar maps found no
  existing node for the new construction. `CoherentPairFunctorDescent` uses a
  different `Diagram`/`PairStructure` interface, not this recorded StageSystem quotient.

New-node audit: `def-weil-pbc-finite-completed-coefficient-map` is warranted by order
1307's integral change of completed coefficient rings. I checked all its required
§5 fields, the five cited dependencies, and its own module. The inclusion is the
actual field inclusion conjugated by `Shrink.algEquiv`; integer inclusion reuses
`WeilConjectures.integralScalarIntegerInclusion`; quotient maps use the proved-to-be
ideal containment; finite sheaf maps use the recorded constant comparisons. The
completed map is chosen from an existence-and-uniqueness assertion fixed by every
projection, so the permitted choice determines real data. Its ambient extension
reuses `pbcDerivedExtend`, whose source was read together with the K-flat universal
counit and normalized scalar adjunction. The older integral-tower realization is
not a direct substitute for this PBC completed-sheaf realization. No new mathematical
assumption or characteristic restriction appears.

Dependency-module audit: `def-weil-pbc-finite-stage-pair-category` now has exactly
the objects, Hom quotient, transport and canonical operations of its node, as
matched above. Its `lean.note` correctly explains why the returned arbitrary
interface was unusable. The source units, associators and tensor comparisons
were checked through their actual normalization equations, not just their names.
The record changes only in `lean`; the new completed-map node is cited directly
by the item as permitted. All chosen functors/comparisons use uniqueness or an
explicit construction. Definitions contain no sorry data, and every postponed
named theorem has its owning blueprint tag and natural-language proof plan.

Mismatches repaired in this reading:

- H4: removed the unused supporting `pbcCommonStage_equality`, which restated the
  exact existing upstream `PairCategory.mkHom_eq_mkHom_iff'`. Removed it from
  `lean.declarations`; the final simultaneous-equality clause is unchanged.
- H8: supplemented the final theorem's brief ten-step outline with the ten full
  DAG proof paragraphs and their dependency citations. This retains the tensor
  signs, explicit object identifications, simultaneous witnesses, and negative
  shift calculations needed by the next proof worker.

No mathematical statement correction is needed; no `statement_change` or citer
audit applies. The final signature is unchanged and the item's `lean.statement`
is verbatim its file signature. The removed helper was not used by a definition
or by any other delivered declaration.

Validation: the prescribed `scompile.py NS prop-weil-pbc-common-stage-calculus`
invocation compiled all three sibling files separately and returned exit 0 with
no warnings or errors. All delivered Lean lines are at most 100 characters; the
main signature comparison is exact. The delivery dry run recompiles the final
files, including the expanded proof docstring, and runs the current preflight.
Current server-source probes also confirm that the alternatively named
`Sheaf.Paper.PbcFiniteStagePairCategory` and `Sheaf.Paper.PbcCommonStageCalculus`
are unavailable, so they supply no published replacement for these modules.
