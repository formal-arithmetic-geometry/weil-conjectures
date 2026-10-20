## Worker report

Item: fix-prop-projection-formula; group NK; stage 2. The delivery states the
compact-support projection formula, with all theorem proofs postponed. Definitions
contain actual functors, adjunction mates, full-subcategory lifts, conjugations,
localization comparisons, and common-stage inclusions. The original statement,
proof, proof dependencies, and source are preserved. Statement dependencies gain recorded interfaces and the new canonical
comparison definition nodes described below.

The main delivered module is `Sheaf.Paper.CompactSupportProjectionFormula`. Its main declarations
are `WeilConjectures.compactSupportProjectionFormula`,
`WeilConjectures.compactSupportProjectionFormula_coefficients`,
`WeilConjectures.CompactSupportWeilProjection.restriction`,
`WeilConjectures.CompactSupportPbcProjection.forward`,
`WeilConjectures.CompactSupportPbcProjection.tensor_identification`, and
`WeilConjectures.CompactSupportPbcProjection.commonIso`.
The node's `lean.declarations` lists the supporting declarations as well.

Sources read: the current main-20261015 blueprint's
`sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.md`, its proof,
`lem-fix-weil-operations.md` and its proof, the repaired DAG statement and its
fifteen proof steps, and coord/repair-notes/fix-prop-projection-formula.json.
The repair note is resolved at stage 1; its nonseparated-domain and arbitrary-K
requirements are retained here. No smooth-purity or Verdier-duality claim is used.

Hypotheses and clauses:

- The global finite field, distinct coefficient prime, algebraic closure, extension
  E and positive finite coefficient level are the actual `FiniteFieldDatum`,
  `D.CoefficientDatum`, `[Field E]`, `[Algebra (Padic C.l) E]`,
  `[FiniteDimensional (Padic C.l) E]`, and `hn : 1 ≤ n` of
  `SixFunctorOperationDatum`. No arbitrary operation package is substituted for it.
- X and Y are `SixFunctorSpace D`, whose structure morphisms are finite type.
  Only f has `[IsSeparated f.hom.left]`, `[LocallyOfFiniteType f.hom.left]`,
  `[QuasiCompact f.hom.left]`. Neither structure morphism is assumed separated.
- At finite coefficients K is in `sixFunctorFiniteCategory`, the full intrinsic
  bounded constructible category. L is in `finiteTorConstructibleCategory`.
  `CompactSupportFiniteProjection.domains` supplies the necessary constructible
  tensor closure and finite-Tor pullback closure, then `partialTensor` and
  `torPull` restrict the existing operations. K is never replaced by a finite-Tor
  object. The finite component is the actual fixed-site
  `ProEtale.projectionMapOfCompactification`, transported by the published finite
  realization, support and pullback comparisons and lifted through the full
  constructible inclusion. `fixedPullComparison` compares K-flat derived
  pullback to the exact inverse-image descent; they are not silently identified.
- At integral coefficients the second-input predicate is
  `S.integralFiniteTorDomain`. At rational and algebraically closed coefficients
  it is the whole category, since these are field coefficients. The theorem also
  covers every finite level of the integral normalization and every finite
  coefficient field of the closure normalization, with its integral, rational
  and finite levels.
- The higher-coefficient arrow is `compactSupportProjectionComponent`, namely
  the recorded `SixFunctorExchangeData.projectionComponent` on the identity
  base-change square retaining c. It is the proper counit projection followed
  by the inverse open projection and pullback composition, not an existential
  isomorphism. `CompactSupportProjectionLaws.isIso` and finite `Laws.isIso`
  assert invertibility of those exact arrows.
- Naturality in both variables is the two-variable map equation in each
  `naturality` field, including morphisms of arbitrary constructible K.
  `compactification` is the equation for every pair c,d of compactifications.
  `composition` is the equation intertwining the displayed projection with the
  actual support compositor and pullback compositor. `pentagon` compares the
  two threefold support-composition routes, transporting the composite
  compactification along associativity. These fields do not assume their laws.
- For proper f, `compactSupportProperProjection` is exactly the counit mate of
  the recorded proper adjunction. `proper` is its square with the actual
  `properIdentification`. The finite `properComponent` uses the identity-open
  compactification and the same identification. No nonproper direct-image
  projection formula is asserted.
- `CompactSupportProjectionChange` writes the scalar square for the specified
  `PurCompactSupport.projectionMap`, using its canonical `comparison`,
  `scalarTensor` and `scalarPull`. The coefficient-pullback composition
  equalities are asserted, not added as assumptions. The coefficients theorem
  covers all quotient reductions m→n with n≤m and positive levels, completed
  integral reduction, completed scalar extension, and ramified finite scalar
  extension. Both inputs are finite Tor only for the reduction clauses that
  state that domain; scalar extension retains arbitrary K. The square is in
  ordinary coordinates, and the completed comparison is obtained through the
  specified completion units. Rational and common-stage compatibility is the
  actual `SixFunctorExchangeComparison.projection` in the datum, obtained by
  localization and the common finite-field prescription.
- For the Weil restriction, the models X₀,Y₀ are separated finite type over k₀,
  f₀ is separated finite type, and the underlying operations use exactly
  `zlFiberMap D f₀`, its geometric compactification, and their canonical
  proper/open adjunctions. `CompactSupportWeilProjection.component` constructs
  the proper counit mate, inverse open unit mate, and pullback factorization.
  `supportPair` uses `fieldWeilShriekExchange`; `pullPair` uses
  `fieldWeilPullSquare`; `tensorPair` uses the canonical completed rational
  pullback/tensor comparison followed by tensor of the two given Weil maps.
  `restriction` asserts that this component is the forward arrow of the unique
  isomorphism between these precise fixed pairs. All rational structure
  isomorphisms are permitted, not only localizations of integral Weil maps.
- `CompactSupportPbcTransport` retains the difference between the completed
  Frobenius in `FdFrobeniusComparison` and exact transport in `WeilD`.
  `integralBridge` is the published
  `pbcIsoCompletedPullback_identification`, restricted to the full integral
  category. `bridge_existsUnique` fixes its rationalization on every integral
  representative; `bridge` chooses only this uniquely determined natural
  isomorphism. `toExact` and `fromExact` insert that comparison into the Weil
  structure and retain the same underlying object and arrow. The geometric
  Noetherian/dimension/invertibility facts are inherited from the recorded
  comparison and are not extra hypotheses on schemes.
- `CompactSupportPbcProjection.source`, `target` and `iso` are in actual
  `WeilD D C Y₀ E₀`, transported through the recorded coefficient equivalence
  and the uniquely normalized exact/completed bridge. `forward` specifies the unique Weil isomorphism whose underlying arrow is
  the coefficient image of the actual proper/open component; `iso` chooses only
  that uniquely determined isomorphism. The repaired tensor_identification
  supplies a UNIQUE comparison whose forward map is explicitly the normalized
  coefficient tensor comparison, followed by the W.finite/bridge counit
  cancellations on both inputs, followed by R.chi. Its second conjunct is the
  ordinary equality of the completedPair ambient carrier with the wfTensor
  object. Its third is the original structure-map HEq on those equal carriers.
  No unpinned Nonempty comparison remains.
- `commonIso` is the actual `WeilDQbar` isomorphism obtained by extending the
  two arbitrary input Weil objects to any common finite coefficient field,
  applying this finite-field isomorphism, and using `weilScalarSystem.ι`.
  It allows repeated fields and arbitrary larger common fields. The scalar
  squares of the coefficient theorem, the normalization of the coefficient
  comparison system, and the recorded scalar cocycles are the common-stage
  prescription; they compare the same arrows before taking their classes.

Dependency declarations used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, its actual
  finite/higher/closure operations and normalizations, and `SixFunctorSpace`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `sfIntrinsicCompactSupport`, `sfIntrinsicCompactSupportComparison`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: the recorded canonical
  compact-support compositor, used through the operation datum's normalized
  `composition` and `comparison` fields.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the supplied
  proper/open projection construction and its coefficient comparison interface.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the original finite, completed integral,
  raw rational and common-stage pullbacks/tensors; no duplicate tensor is defined.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`,
  `finiteTorConstructibleCategory`, `finiteTorConstructibleIntegral`. The node's
  Etale repair is retained; the original pro-etale and integral declarations
  remain the declarations used by the six-functor datum.
- `Sheaf.Paper.SfCommonStageDirectImage`: recorded derived direct-image notion;
  the projection conclusion uses it only with proper identification, through
  the datum's proper adjunction/direct-image fields.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the actual higher compact-support
  action, compatible with the completed proper/open realization and quotient
  projections, including nonseparated structure morphisms.
- `Sheaf.Paper.WeilTensorProduct`: `wfTensor`, `wfWeilStructure`,
  `wfTensorFrobenius`; `Sheaf.Paper.PbcWeilCategory`: `WeilD`, `WeilDQbar`,
  `weilFrobeniusPullback`, `weilScalarSystem` and its transitions/inclusions.
- `Sheaf.Paper.FieldWeilShriekShiftData`: `fieldWeilPull`,
  `fieldWeilProperAdj`, `fieldWeilOpenAdj`, `fieldWeilShriek`,
  `fieldWeilShriekExchange`, `fieldWeilPullSquare`, `fieldRationalPullComp`.
- `Sheaf.Paper.ZlFrobeniusCompactSupportComparison`:
  `zlGeometricCompactification_comm` and the published geometric construction.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`:
  `FdFrobeniusComparison`, `rationalCoefficientCategoryComparison`; the latter
  supplies the normalized comparison packages universally used by the interface.
  `Sheaf.Paper.FdCoefficientComparisonSystem` supplies the simultaneous
  `FdCoefficientComparisonSystem` and `FdPullbackSystem`.
  `Sheaf.Paper.FdCoefficientComparison` supplies its stage comparisons, fixed
  integral transport, and the action on every raw localized tensor.
- `Sheaf.Paper.DerivedPullbackTensorIso` and
  `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `canonicalRationalPullbackTensor`, with their actual representative and
  composition normalizations.
- `Sheaf.Paper.WfTensorCompletionFrobenius`:
  `WfTensorCompletion.RationalComparison`, its `Normalized`, `completedPair`,
  `wfTensorCompletionFrobenius`, and the common-field prescription.
- The finite fixed-site component is imported from
  `Sheaf.Paper.FiniteRingCompactSupportProjectionMap`; the underlying canonical
  mate is `ProEtale.projectionMapOfCompactification`. All stated proof-dependency
  modules are imported as the stage-3 plan; no proof is supplied here.

The independent purity comparison was deliberately not imported: its DAG path
runs through purity scalar naturality back to this item. The acyclic underlying
proper/open and coefficient-comparison declarations are used instead. There is
no dependency wait and no circular use of a downstream projection theorem.

Edge cases checked against the definitions: n=1 is included and n=0 is excluded
only by the stated positivity; empty schemes and zero complexes require no
nonemptiness hypothesis; identities and identity field extensions are included;
proper f uses j=id; open f uses the open unit mate; all compactifications and
non-Cartesian refinement comparisons are quantified. At A=O_E/(varpi²),
K=A/(varpi) is still allowed with finite-Tor L, although K has infinite Tor
dimension. The tensor unit is allowed. Threefold compositions retain the actual
associativity transport. Arbitrary rational Frobenius isomorphisms, equal input
fields, and strictly larger common coefficient fields are included. The ordinary
and completed Frobenius presentations are related by the actual completion
comparison, not by an imposed equality of universes or presentations.

Searches made before defining the components (full raw results in the sandbox's
searches.jsonl):

- msearch.py `leanfinder`, "compact support projection formula compatible
  composition coefficient change Weil categories": eight profinite projection
  hits; no constructible compact-support theorem.
- msearch.py `loogle`, `CategoryTheory.Adjunction.projectionFormulaMap, IsIso`:
  unknown Mathlib identifier, no hits. The actual project declaration
  `Adjunction.rightAdjointProjectionMap` was then found and read in source.
- msearch.py `grep`, `projection.*[Cc]oher|[Pp]rojection[Ff]ormula`,
  Mathlib/CategoryTheory: only coherent sequential-limit material.
- msearch.py `leansearch`, "Projection formula compact support constructible
  sheaves finite Tor dimension": eight unrelated projective-dimension,
  equalizer, and derived-resolution results; no match.
- Further leanfinder/loogle/grep searches for all coefficient stages, compact
  support, finite Tor and coherence are recorded with their actual results.
- rg searches of `lean/WeilConjectures` and `lean/Sheaf`, plus the item-id grep,
  found the canonical finite projection maps, abstract supplied projection
  construction, constructible finite projection theorem, completed coefficient
  comparisons and Weil tensor conventions used here. None states this concrete
  all-coefficient/all-coherence theorem on the required arbitrary-K and
  nonseparated structure-map domain. Existing maps and notions are reused.

No statement correction or dependency-record repair is claimed. The two original
definition-node bindings below reuse published definitions. The repair adds the
normalized coefficient tensor comparison definition and its own module. The additional declarations are the actual projections,
restriction interfaces, and canonical comparison helpers belonging to this item.
No STATEMENT-DISPUTED flag is raised.

Validation is by scompile.py on every delivered module, followed by deliver2.py
--no-push and its server preflight. The retained packet contains the returned H3 repair; the resumed dry run
identified the report-section omission described below. All postponed proofs remain
public named theorems with their sources and natural-language proofs. No axiom
or definition with postponed data is introduced.


## New nodes

- `def-sf-projection-weil-coefficient-comparison` binds the already published
  `WeilConjectures.FdFrobeniusComparison` in
  `Sheaf.Paper.RationalCoefficientCategoryComparison` (`existing: true`). Its
  fields are the inherited geometric hypotheses, the common and finite
  Frobenius-pair equivalences, and the equalities fixing their underlying
  fixed-pair functors. This extracts the existing definition from the owning
  existence theorem's node, as requested by preflight; it introduces no copy.
- `def-sf-projection-weil-tensor-comparison` binds the already published
  `WeilConjectures.WfTensorCompletion.RationalComparison`, `Normalized`,
  `ordinaryPair`, and `completedPair` in
  `Sheaf.Paper.WfTensorCompletionFrobenius` (`existing: true`). The functors,
  chi, both mu comparisons, and their normalization are exactly the original
  definitions. Their existence/equivariance theorem stays a proof dependency.

- `def-sf-projection-coefficient-tensor-total` defines the local pure-tensor
  coefficient comparison and its inverse signed-total comparison in
  `Sheaf.Paper.ProjectionCoefficientTensorTotal`. The module comparison is
  uniquely fixed on every local pure tensor; the total comparison uses the
  recorded signed direct-sum constructor.
- `def-sf-projection-tensor-coefficient-comparison` defines the canonical
  coefficient/tensor comparison in `Sheaf.Paper.ProjectionTensorCoefficientComparison`.
  Its normalization descends the pure-tensor comparison through K-flat
  representatives, the actual inverse quotient-completion unit, the full
  integral inclusion, and unchanged integral representatives in rationalization.
- `def-sf-constructible-projection-mates` defines the finite constructible
  projection mates and the finite/higher coherence predicates in
  `Sheaf.Paper.ConstructibleProjectionMates`. These reuse the fixed-site mate,
  coefficient realization and full inclusion, retaining arbitrary K and the
  finite-Tor second input. Its separate module preserves the per-file limit.

For the two existing-definition bindings the search checks were run before creating the records:
blueprint_refs searches returned zero separate blueprint definitions; rg of the
DAG found only the owning theorem records. Mathlib leanfinder and LeanSearch
returned perfection/Witt-vector Frobenius and ordinary adic-completion tensor
results, not these fixed-pair comparison data. Loogle reported unknown
FdFrobeniusComparison, and Mathlib CategoryTheory grep returned zero matches.
Source rg found the exact existing Sheaf declarations and no WeilConjectures
copy. The actual search-log entries are included verbatim in each new node's
mathlib_searches. The main item cites the new definition records; it does not
add theorem nodes to its statement dependencies.

The final preflight repair also removes the trailing assignment delimiter from
lean.statement, matching the maintainer's signature extractor. The remaining
signature text is copied verbatim; the Lean statement itself was unchanged.


## Repair of return c5b7cea9fac0

H3 is repaired by replacing the bare Nonempty tensor-presentation isomorphism
with a unique isomorphism satisfying an explicit underlying-map equation.

The new modules Sheaf.Paper.ProjectionCoefficientTensorTotal and
Sheaf.Paper.ProjectionTensorCoefficientComparison supply
object-level compatibility of the recorded coefficient equivalence with tensor.
ProjectionTensorCoefficient.module_existsUnique fixes the ordinary comparison
on EVERY local pure tensor, and includes naturality in both variables.
moduleComparison is chosen only from that unique characterization. total is the
published signed-total construction applied to its inverse summand comparison.
ordinary_existsUnique fixes the derived comparison by its entire K-flat
representative square, including the exact coefficient factorization and the
published tensor representative comparisons. integralArrow composes the inverse
of the specified quotient-completion unit with that comparison, for each existing
OpenFactorCoherence.Tensor normalized presentation. The integral lift is fixed by
that same arrow for EVERY normalized presentation. Such presentations exist by
constructible tensor completion and tensor descent; the condition is nonvacuous.
This avoids unfolding the proof of a chosen presentation while retaining both
Roos-coordinate normalizations.
integral_existsUnique lifts exactly that arrow through the full integral
constructible inclusion. rational_existsUnique fixes its rationalization on
every unchanged integral representative; the existing objects and tensors fields
of the coefficient equivalence and R.Normalized retain all rational denominators.
The final comparison definition chooses ONLY this unique normalized natural
isomorphism. These helpers define the missing comparison requested by the return;
they do not substitute a fresh tensor operation or arbitrary isomorphism.

CompactSupportPbcTransport.cancellation_existsUnique pins the underlying
cancellation to the ACTUAL W.finite counit at fromExact K. The bridge and its
inverse cancel in the Weil structure, with no change of carrier. Thus the first
conjunct of tensor_identification prescribes, in order:

1. comparison on the carriers of pairInverse K and pairInverse L;
2. R.ordinary applied to the two specified counit cancellations;
3. the actual R.chi component on K.carrier and L.carrier.

This is the canonical comparison requested by the return. An isomorphism with
different underlying arrow cannot satisfy its equation, by faithful forgetting.
The second conjunct is now an explicit ordinary equality of wfWeilCarrier of
completedPair and the actual wfTensor object. The third retains the structure-map
HEq, whose source and target types are equal by applying ambient Frobenius and
Hom to that carrier equality. On unchanged integral representatives the equality
is exactly the R.completed normalization, followed by the full-subcategory
inclusion; proof fields are irrelevant. The completedMu and localized tensor-map
normalizations give the corresponding structure-map equality. These equations
cover arbitrary rational Weil maps without an integral Weil lattice.

The finite/integral/rational/common-stage laws and coefficient squares accepted
in the return have identical statements and definitions. The advisory about the
pentagon and proof imports is not an instruction to alter those accepted clauses;
their imports remain the recorded stage-3 plan. The returned advisory about
identifying the datum's rational PF remains a proof-plan comparison, while the
Weil arrow in this packet continues to be the precise proper/open mate.

Additional edge cases for the repair: zero inputs, the tensor unit, identity
coefficient comparison, arbitrary localized numerators and denominators, and
Weil structure maps without integral lifts. The pure-tensor characterization and
the exact completion units impose no nonemptiness, lattice, finite-Tor, or
bounded-flat-resolution hypothesis on the rational inputs.

## New nodes (repair addition)

- def-sf-projection-tensor-coefficient-comparison records the missing canonical
  coefficient/tensor comparison in its own module. The definition is comparison,
  with the exact representative-normalization helpers listed in lean.declarations.
  Its field and scheme parameters are precisely those of the two recorded
  comparison packages. Its statement includes the ordinary pure-tensor map,
  signed-total descent square, inverse quotient unit, full integral lift and
  raw rational localization. Its statement cites the existing normalized
  tensor-completion presentation, rather than defining another one. The supporting theorems are well-definedness and
  uniqueness statements needed for that construction, each with a proof docstring.

Searches run for this addition are in searches.jsonl and copied verbatim into
the node: leanfinder returned eight field-theoretic tensor equalizer/flatness
lemmas; loogle reported unknown CategoryTheory.NatIso and no hits; Mathlib grep
found only ModuleCat/Descent and ordinary ModuleCat/ChangeOfRings. Project searches
found FdRationalStageComparison's object/pure-tensor normalizations and the
one-input scalar comparison in CompletedCoefficientPresentationTransport, which
do not provide this two-input tensor comparison. blueprint_refs.py search
'coefficient tensor' returned def-pur-section-invariant,
lem-coef-integral-residue-tor-residue-amplitude and lem-exc-constant-tensor;
none defines this presentation comparison. The current ordinary and completed
tensor constructions, coefficient functor, signed-total constructor, K-flat
models and quotient unit are reused.

## Second reading by NK

Worker self-check of the repair, followed by the maintainer's independent review:
the first conjunct now fixes the comparison arrow rather than merely its
endpoints; its normalization goes all the way to local pure tensors and the
actual quotient unit. The W.finite counit and bridge cancellation appear in the
displayed arrow before R.chi. The carrier equality is explicit, so the remaining
structure-map HEq compares morphisms over equal objects. The original all-stage
projection and coefficient-change statements are preserved verbatim.

- def-sf-projection-coefficient-tensor-total records the module-level pure-tensor
  comparison and its signed total. Its own module contains exactly that
  coefficient tensor family, its two equivalent naturality formulas, and the existing signed-total
  constructor specialized to it. Splitting it from the derived comparison keeps
  each file within the required single-file compilation limit. Its searches are
  the same actual recorded coefficient-tensor searches above.

The existence/uniqueness statements in the normalized tensor comparison are
well-definedness statements for these constructions. The ordinary comparison
accepts any recorded ProEtaleTensorModel with its representative comparison.
The integral lift must agree with the composite for every recorded normalized
tensor-completion presentation; no arbitrary presentation or extra assumption is
selected. Exact coefficient restriction, its pure-tensor family, the total map,
the unit and R.chi are all the existing operations with their fixed formulas.


The main projection module owns the normalized completed/exact Frobenius bridge
and its inverse-realization counit cancellation. These helpers use the actual
integral completed-pullback comparison and actual finite-equivalence counit.
Their declarations remain in the main node because their large derived category
types share the main module's existing imports.




## New nodes (constructible mate module)

def-sf-constructible-projection-mates records the canonical component in
constructible finite-coefficient coordinates and the exact coherence predicates
used by the projection theorem. The existing generic projection, fixed-site
projection, coefficient realization and full inclusion are reused. This module
contains the original declarations through CompactSupportFiniteProjection.Laws
without changing their formulas or statements. Source: proof steps 1--6.
LeanSearch returned sheaf/cokernel projection maps, LeanFinder returned unrelated
constructible-set and profinite projections, Mathlib grep returned zero hits.
Source and DAG name searches returned no matches; blueprint search returned
sk-thm-sf-pf-finite and thm-sf-pf-adic, which are theorems rather than this
constructible-coordinate definition. The full first input and finite-Tor second
input, positive coefficient level, nonseparated structure morphisms and proper
specialization are exactly as in the original module. Splitting these definitions
allows separate compilation within the per-file limit; the main theorem and
proof-dependency imports remain in the main module.


## Resumed packet self-check

The retained packet already contains the H3 mathematical repair described above:
no bare Nonempty tensor comparison remains. The comparison's underlying map is
fixed by the integral-representative-normalized coefficient comparison, the
actual finite-equivalence counit cancellations and R.chi. Reading
RationalComparison.Normalized, completedPair, wfWeilCarrier, wfWeilStructure and
wfTensorFrobenius confirms that the explicit ambient carrier equality makes both
structure-map types equal by congruence (apply ambient Frobenius and then Hom).
This includes arbitrary rational Weil structure maps.

The initial resumed dry run rejected only report organization: the exact
`## New nodes` section did not name three additions described in later sections.
All five new nodes are now named in that section. No Lean declaration or node
statement was changed for this report repair. A subsequent compile exposed
expensive automatic helper generation for the constructible coherence structures.
Disabling genInjectivity and genSizeOfSpec in the four delivered modules
retains the explicit declarations and statements while avoiding those generated
helpers. These are the same helper-generation settings as the published
WfTensorCompletionFrobenius module. Its scompile.py check now passes in 15.8 seconds (sandbox) and
14.9 seconds (library). Final validation and delivery use the prescribed wrappers.


Final per-file server validation: all four delivered modules compile cleanly
through scompile.py. The current-source confirmation recorded respectively
47.1 seconds (ProjectionCoefficientTensorTotal), 22.9 seconds
(ProjectionTensorCoefficientComparison), 17.2 seconds
(ConstructibleProjectionMates), and 41.8 seconds (CompactSupportProjectionFormula).
The main module respects definition transparency globally, retaining the original
lookup behavior locally for mu, pullFactor, component and integralBridge. These
elaboration-only settings change no explicit statement or construction.

The pure-tensor module also respects transparency, and moduleComparison and
 totalIso now carry explicit result types. These types are the original inferred
interfaces; the selected uniquely normalized family and total comparison are
unchanged. This avoids re-expanding their existence statements at use sites.

The final openMate result type is also explicit, preserving the same actual
proper/open component. After successful compilation, preflight identified only
the old abbreviated moduleComparison signature in its node record; that record
now copies the full explicit signature verbatim.

The final self-check gives the already specified three-part tensor composite the
name CompactSupportPbcProjection.tensorComparisonArrow, with an explicit source
and target. tensor_identification fixes its unique Weil comparison to exactly
this arrow. Unfolding this helper gives, verbatim, the normalized coefficient
comparison, R.ordinary on the two actual counit cancellations, and R.chi. This
names a construction belonging to the item, introduces no new choice, and leaves
the carrier equality and structure-map HEq unchanged. The helper is listed in
the main node's lean.declarations and has its source/blueprint docstring.

Final dry run: deliver2.py --no-push returned OK, with all modules compiling and
the full server preflight passing (dry-run commit 895cc0b014).
