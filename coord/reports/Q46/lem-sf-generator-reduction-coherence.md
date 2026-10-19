## Worker report

This is a substantive repair of returned immutable head b075ba55154b. The saved
packet's free generator arrows have been removed. The initial prescribed saved-packet
dry run failed because CanonicalOpenReduction.lean was owned by no delivered node.
That incomplete helper is now only a scratch artifact. Its required canonical open
mate construction is implemented in the owning item module, without a separate
unowned delivery file. The old SemilinearSystemModels replacement was removed after
comparison showed that its instance repair has since landed; the only difference
from current source was placement of the same attribute.

The natural statement is unchanged. The item uses the published
IntegralSystemRealization.Operations, Compositors, OpenComparisons, RingedModels,
RingedOpenComparisons and RealizationModel interfaces. These retain the actual
right-derived certificate, adjunction, representative normalization, and quotient
transitions. GeneratorKind stores structural constructors only. systemMap and
ringedMap case-split on those constructors and select actual adjunction units and
counits, tensor constraints, and canonical composition/open maps. integralMap
transports the independently defined ringedMap by the actual recursive completion
maps. It is not defined from a desired coefficient-square equation.

Every definition has real data. inverseOrZero totalizes inverses only outside their
invertible domain. completionMap_isIso explicitly states that the completion maps
are invertible on the theorem's domain. The open primitiveFormula states both actual
d_j inverse laws. Thus zero-map branches cannot supply arbitrary generator arrows
on the claimed domain. The three postponed named theorems are
primitiveReductionTranspose, completionMap_isIso and generatorReductionCoherence;
they are listed in lean.declarations and have source/proof docstrings for this node.
Nothing is proved at stage 2.

Hypothesis and clause correspondence:

- The algebraic closure of a finite field is the published FiniteFieldDatum D;
  C : D.CoefficientDatum supplies its prime, primality instance and l != p. E has
  the Field, Algebra (Padic C.l) and FiniteDimensional instances. The coefficient
  rings and uniformizer are the existing Padic constructions, not new rings.
- Finite-type schemes are W and FiniteTypeFamily W D.k: each actual structureMap
  is locally finite type and quasi-compact. Word.pull retains IsSeparated,
  LocallyOfFiniteType and QuasiCompact; Word.push also retains IsProper; Word.open
  retains IsOpenImmersion and QuasiCompact. There is no dummy Unit parameter.
- The small pro-etale site, strict systems, reduction, total limit, unit and counit
  are precisely the published coefficientSequence and IntegralSystemRealization
  declarations. System direct image is Operations.push, whose Direct.model is a
  CoefficientDerivedImage and whose Direct.adj is its actual derived adjunction.
- Integral tensor is integralCompletedTensor, the original recorded global
  quotient-tower construction; integral pullback is integralDerivedPullback. Integral proper
  push uses the item-owned integralSystemDerivedDirectImage helper. Integral
  open extension is the actual localized completed-ring ringedOpen.
- Admissible requires finiteTorConstructibleIntegral and SystemAdmissible of the
  actual reduction of each input. The former includes sfIntegralConstructible,
  hence derived completeness and bounded constructibility. SystemAdmissible
  requires normalization, the published Origins (whose level origins are actual
  FixedEtaleOriginWitness data and whose equations constrain transitions),
  intrinsicFiniteTorsionConstructible at every positive level, cohomological
  support contained in Icc lo hi and HasProEtaleTorAmplitude torLo torHi, with
  both intervals ordered. All four endpoints are arbitrary integers.
- Word.admissible checks the actual systemValue at every vertex of B and C,
  recursively in both tensor slots. It does not replace an intermediate system
  by reduction of a different integral object. GeneratorKind.admissible adds
  precisely the intermediate systems in the cartesian/clopen lambda factorization,
  including the systems on pullback p i and the successive direct images.
- tensorD is the inverse of the published normalized quotient-tower tensor
  realization. pullD is the inverse of the normalized pullback model.
  Proper image is its defining L S R tower, so d_push is identity in those
  coordinates. openD is L of the actual inverse open mate followed by inverse
  reconstruction unit; openDInv is that unit followed by L(openR). openR itself
  is the inverse of RealizationModel.openReduction, the actual open-adjunction
  mate of its whole-system K-flat normalized reductionPull square. This is the
  canonical transport of the specified open comparison, rather than a chosen
  lift of evaluated arrows.
- tensorR and pullR are independently constructed from reduction of the actual
  completion unit and the published reduction tensor/pull maps. pushR is the
  actual counit on the defining system tower; openR is the actual mate just
  described. Word.primitiveFormulas states their equalities with R(d_A inverse)
  followed by the actual adjunction.counit. For open it also states both inverse
  laws. primitiveReductionTranspose covers any one-operation word; the main
  theorem also supplies these formulas for all operations in its two short words.
- Word.r is a structural recursion: input is identity, unit is its normalized
  coefficient-unit map, unary cases compose r_A with the actual system functor
  applied to the child r, and tensor applies the system bifunctor to both child
  comparisons. It is not a separate unconstrained field per word.
- GeneratorKind.tensorAssociator/tensorLeftUnit/tensorRightUnit use the actual
  tensor constraints. pullComposition uses the fixed K-flat compositor;
  pushComposition uses its adjoint conjugate. pullPushUnit/pullPushCounit and
  openUnit/openCounit use their respective actual adjunction transformations.
- openBaseChange has endpoints P_g J_j and J_j' P_gU and requires the actual
  cartesian square. openTensor has endpoints J_j B tensor C and
  J_j(B tensor P_j C). Their maps are the published open-unit-normalized maps.
- properOpenInterchange has endpoints J_i S_r and S_p J_k. properOpenLambda has
  endpoints P_i S_p J_k and S_r. systemMap uses properOpenLambda's actual
  cartesian conjugation, clopen restriction, J_s = S_s and direct-image compositor;
  interchange is its inverse's open adjunct. ringedMap performs the independently
  normalized ringedProperOpenLambda construction and its open adjunct.
- hB/hC impose only the two endpoint length bounds, with binary tensor counted
  as one operation. The internal lambda factorization is not truncated at length
  three. Assertion is the requested equality r_B >> tau_sys = R(tau_int) >> r_C
  of morphisms in the actual derived strict-system category, with no Nonempty
  conclusion and no arrow variables. The lambda constructor supplies its own
  square. No arbitrary context, nested compact-support or evaluation-faithfulness
  assertion is introduced.

The module's proof-only imports include BasicOperationsCoefficientReduction,
CompletedOperationTowerSubstitution, IntegralOpenReductionComparison and
RingedExchangeTensorCoherence where appropriate to the plan. The last is explicitly
used in proof step 3 for the canonical ringed tensor/square identifications; it is
not an unused public API import. There are no auxiliary A/B' parameters.

Dependencies read and used (module prefixes are Sheaf):

- Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum and CoefficientDatum.
- NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing,
  together with its imported coefficient rings/transitions.
- Paper.CoefDerivedSystemEvaluationCalculus: CoefficientDerivedSystemCalculus,
  coefficientDerivedSystemEvaluationCalculus, adjunction and counit_projection.
- Paper.SemilinearDerivedSections: SemilinearSections.semilinearDerivedSections,
  including simultaneous adjunction/section and tensor normalizations.
- SixFunctors.IntegralSystemOperations: Operations, Direct.model/adj, Open.adj,
  Compositors, OpenComparisons and properOpenLambda.
- SixFunctors.IntegralSystemExpressionDomain: Origins, including level,
  FixedEtaleOriginWitness, originSquare and transitionSquare.
- SixFunctors.IntegralSystemCanonicalBridge: RealizationModel.openReduction,
  RingedModels, RingedOpenComparisons, ringedAdj, ringedOpenAdj,
  ringedPullComp, ringedPushComp, ringedAssociator and ringedProperOpenLambda.
- Paper.IntegralDerivedOperationsOnSlices and CompletedPullbackTensorComparison:
  integralCompletedTensor,
  integralDerivedPullback, pullbackTensorIntegralTensorModel,
  pullbackTensorIntegralPullbackModel and the fixed calculus.
- SixFunctors.GeneratorReductionStatement: integralSystemDerivedDirectImage (item-owned strict-system specialization used by integralPush).
- SixFunctors.IntegralOpenReductionComparison: integralOpenReductionComparison,
  Comparison.r/d/dFormula and actual reconstruction-unit normalization; used in
  the proof plan transporting the canonical open mate to this whole-system model.
- Paper.NormalizedDVRTower: IsNormalizedCoefficientSequence.
- Paper.SfIntegralConstructible: sfIntegralConstructible.
- AlgebraicGeometry.FixedEtaleOriginWitness: Scheme.FixedEtaleOriginWitness,
  retained through Origins rather than a private substitute.
- Paper.FiniteTorAmplitude: finiteTorConstructibleIntegral and the underlying
  HasProEtaleTorAmplitude. Its ordinary-etale presentation is currently recorded
  in FiniteTorAmplitudeSites; the record explicitly retains these original
  pro-etale/integral definitions, which are the ones used here.
- Paper.BasicOperationsCoefficientReduction: basicOperationsCoefficientReduction.
- SixFunctors.OpenTensorNormalization: SheafOfModules.openTensorNormalization;
  the normalized transpose interfaces are retained in OpenComparisons.
- SixFunctors.SemilinearProperOpenMatePasting:
  ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting; its canonical
  lambda construction is retained in IntegralSystemOperations and the bridge.
- Paper.RingedExchangeTensorCoherence: SheafOfModules.ringedExchangeTensorCoherence.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
  The scheme-morphism convention node fixes no new declaration; its existing
  IsSeparated, IsProper, IsOpenImmersion, LocallyOfFiniteType and QuasiCompact are used.

Edge cases checked at statement level: no input slots (unit-only words remain
available); no positive coefficient level omitted (n denotes exponent n+1);
arbitrary common finite intervals; repeated tensor slots; identity maps;
empty open and zero inputs; noncartesian proper/open refinement squares; a
cartesian open base-change square; lambda endpoints of lengths three and one;
and its internal factorization on the actual fibre product. No fixed [-3,3]
interval, fixed input count or evaluation-faithfulness hypothesis occurs.

Searches: the retained searches.jsonl records the earlier and renewed searches.
This retry ran LeanFinder on "canonical coefficient reduction compatibility
adjunction unit counit tensor proper open interchange": eight abstract monoidal
adjunction hits, no exact theorem. Loogle on
"CategoryTheory.Adjunction.homEquiv, CategoryTheory.mateEquiv": zero hits. Mathlib
grep on "reduction.*(counit|mate)|properOpenLambda" in CategoryTheory: zero hits.
The upstream source grep for the item id finds no declaration. Concept searches
under upstream WeilConjectures/SixFunctors find lower-shriek and ordinary exchange
coherence, not this strict varying-coefficient reduction statement. Project
searches find the published canonical bridge and operation-domain interfaces used
above, and no existing generatorReductionCoherence. No new independent notion
was necessary.

## Dependency modules

No dependency node is rebound. The landed `def-weil-derived-direct-image` record remains
`WeilConjectures.sfModelDerivedPush` in `Sheaf.Paper.SfCommonStageDirectImage` (the
common-stage declaration owned by N5). The integral strict-system specialization needed
by this item is declared in the owning module `Sheaf.SixFunctors.GeneratorReductionStatement`
as `WeilConjectures.integralSystemDerivedDirectImage`, and `integralPush` uses that
item-owned helper. This preserves the dependency record and avoids an unowned sibling
module.

## Citer audit

No statement correction is made, hence no statement_change or unsupported holds
flags are added. The current statement and proof are copied from current main.
A fresh search of every stmt_deps/proof_deps finds seven direct citers. Their
specific uses of this unchanged statement are:

- lem-sf-integral-compactification-comparison-bridge, proof step 2: uses the
  proper/open primitive transpose to derive L(r_A)u = d_A inverse. The repaired
  primitiveFormulas supplies that formula with the actual unit/counit.
- lem-sf-integral-compactification-system-realization, proof step 5: uses the
  primitive formula and short generator squares before its separate induction
  on expression trees. Both are retained; arbitrary-tree induction remains there.
- lem-sf-constant-semilinear-generator-comparison, steps 9, 10 and 13: uses the
  one-letter tower identification and transpose/naturality for proper/open
  operations, before comparison with constant coordinates. No faithfulness
  assertion has been added to support that argument.
- lem-pur-integral-realization-shift-coherence, step 2: uses the specified d_A
  through the separate recursive-characterization statement; shift compatibility
  is not inferred from this generator theorem alone.
- lem-pur-integral-basic-operation-shift, steps 4 and 5: uses the actual quotient
  and open d_A construction to prove its own shift square. Those constructions
  use the same recorded quotient models and actual reconstruction unit here.
- lem-pur-integral-realization-recursion, steps 3--7: uses identity at leaves,
  successive r_A in both tensor slots, and the basic transpose formula. These
  are the explicit Word.r recursion and primitiveFormulas; its unrestricted
  expression induction and uniqueness argument are separate.
- lem-zl-compact-support-realization-factor-normalization, steps 2--4: uses the
  proper transpose, pasting of the listed structural squares, and the separate
  compactification-comparison bridge. Those uses are unchanged; this theorem
  still asserts neither nested-support realization nor arbitrary whiskering.

No citer was edited. These are source-based checks of mathematical uses of the
unchanged natural statement, not claims that a sorry proves an unrelated property.

## Second reading by Q46

I reread the current natural statement, all five proof steps, the current blueprint
maps-used paragraph, the dependency declarations above, and the replacement Lean.
The decisive old defects were real: unconstrained arrows made zero maps possible,
word comparisons failed to recurse, several generator endpoints were the same
word on both sides, open adjunction generators were absent, and the origins and
intermediate domains did not use the recorded interfaces. These are replaced by
constructor-selected maps, recursive comparisons, actual adjunctions, the two open
adjunction cases, distinct open/proper endpoints and the recorded origin data.
The output is a Prop equality. The lemma and module docstrings describe the actual
canonical-map construction and the five-step proof plan. The independent ringed
maps are defined before their coefficient-square assertion. The dependency and
seven-citer checks are recorded above. Compilation and dry-run results remain
pending; this report does not claim a delivery before those checks succeed.

## Validation

The required initial saved-packet dry run failed on the unowned helper module.
After ownership repair, the new two-module packet was submitted to scompile.py
and deliver2.py --no-push. Final compiler and preflight results are pending.

## Continuation self-check

The prescribed saved-packet dry run was run first. It failed during dependency
compilation; it pushed nothing. Separate wrapper compilation of
DerivedDirectImageTower subsequently passed on the server in 4.7 seconds. The
main-module attempt progressed through the canonical bridge and substitution
interfaces, then stopped at an unrelated dependency timeout before checking this
file. These failures are not described as successful validation.

Source inspection found one remaining saved-packet API defect: the current
completedTensor_global_comparison is only Nonempty on good representatives, not
a natural isomorphism usable by .symm/.inv. This packet now uses the original
integralCompletedTensor throughout. It is the actual global finite-tensor Roos
construction stated by def-pur-integral-derived-operations; tensorD uses its
uniquely Roos-normalized pullbackTensorIntegralTensorModel and tensorCompletion
uses the independently representative-normalized Tensor.chi. No new arbitrary
comparison or hypothesis was introduced. This also removes the invalid .inv
use in tensorCompletion. The complete theorem signature is now recorded verbatim,
with B.length and Cw.length avoiding named-argument assignment tokens in the
record reader. The module now carries the project copyright header.

The second reading was performed in this worker as required by the dispatcher,
which explicitly prohibits starting other agents. It checked the actual source
of RealizationModel.openReduction (the mate of reductionPull), Direct.adj, the
normalized beta/projection transposes, and both clopen lambda composites. The
seven-citer audit above was checked again against every current dependency edge
and the proof text at its use; no natural-language statement was changed.

## Repair continuation on 2026-10-18

The prescribed saved-packet dry run was performed before editing. Both its
overlay attempt and server confirmation stopped at the imported
Sheaf.Paper.DerivedPullbackTensorIso, at the unchanged 60-second limit.
It therefore did not validate this item. A diagnostic copy retaining only
the statement imports was checked through scompile.py, with the delivered
DerivedDirectImageTower sibling. That revealed malformed unparenthesized
morphism codomains in GeneratorKind.systemMap and GeneratorKind.ringedMap,
and haveILetI/whitespace warnings. The actual delivered module now parenthesizes
those morphism types, uses let in proposition-valued instance-binding proofs,
and fixes the tuple spacing. The diagnostic copy then compiled cleanly,
including its library-path check (12.5 and 17.4 seconds); the delivered
DerivedDirectImageTower compiled cleanly too. The diagnostic copy is under
scratchpad and is not part of the delivery. All proof imports remain in
the delivered module; its complete compilation is being checked separately.

The saved module's pre-edit SHA256 was
ed8bedcbe2a43c7ba90aa7bb753b000039e6588ce6bb317d29d2844a48d86766,
which differs from the immutable rejected module's ad9b0111 prefix.
The return's required substantive changes are in the saved Lean code itself,
not merely this report. This continuation checked the complete selected-map
definitions and the actual source of Direct.adj, RealizationModel.openReduction,
RingedModels, Tensor.chi, Pull.unit, properOpenLambda and
ringedProperOpenLambda. The source normalizations determine the primitive
comparisons before the coefficient-square proposition is stated.

Renewed searches used LeanFinder with canonical coefficient reduction
compatibility/adjunction/tensor/proper-open terms (eight general adjunction
hits, no exact statement), Loogle with CategoryTheory.Adjunction.homEquiv
and CategoryTheory.mateEquiv (zero hits), Mathlib CategoryTheory grep with
reduction.*(counit|mate)|properOpenLambda (zero hits), and source/project
ripgrep for the item identifier and generatorReductionCoherence (only a
downstream proof-plan reference in the project). The seven current direct
citers and their uses were reread against the unchanged natural statement.
No statement_change or unsubstantiated holds flags are introduced.

## Final continuation validation (2026-10-18)

The initial saved-packet dry run in this continuation passed: deliver2.py
--no-push reported “OK (dry run): commit 6722c10178 passes the preflight
and compiles; nothing pushed”. Both delivered Lean files were checked by
the prescribed wrapper. This supersedes the pending validation entries above.
The retained main module has SHA256 b083f8d79bb614a25c31f97b1beaf82d7c302bedd98b20ec4d942742cf984c7c;
no Lean source was changed after that successful check.

The final self-check reread GeneratorKind.systemMap and ringedMap (including
both open adjunction constructors and the distinct beta, tensor and proper/open
endpoints), Word.r, primitiveFormulas and Assertion. It also reread the published
Direct.model/adj, OpenComparisons transpose normalizations, properOpenLambda,
RealizationModel.openReduction, RingedModels, ringedProperOpenLambda and Origins.
The actual counit, recursive comparisons and normalized geometric/open maps
replace the free fields of the returned head. The five-step theorem docstring
is present. All seven direct citer identifiers and their cited proof-step numbers
were re-enumerated against the current DAG and agree with the audit above.
The natural statement remains unchanged. The three already published framework
nodes in stmt_deps provide the operations, domain and canonical bridge used here;
they are reused, not redeclared. Only the Lean record dates and this validation
entry were updated after the successful saved-packet dry run.

## H13 ownership repair

The returned H13 finding required dropping the packet's `def-weil-derived-direct-image`
node copy and the unowned `Sheaf.Paper.DerivedDirectImageTower` module. The helper
`WeilConjectures.integralSystemDerivedDirectImage` was moved verbatim into this item
module and added to the item `lean.declarations`; the natural statement and `stmt_deps`
are unchanged. The saved packet then passed `deliver2.py --no-push` as commit
c885e5e96f before this relocation; the post-repair compile and dry run are recorded below.

## H13 continuation validation

The resumed saved-packet dry run passed as commit `2d4334fa13`: preflight and
compilation succeeded, and nothing was pushed. No interrupted delivery process
remained. The packet contains exactly one module and one node file; the
`def-weil-derived-direct-image` dependency copy and the old sibling module are
absent. Current main still records all fourteen N5 sfModel declarations in
`Sheaf.Paper.SfCommonStageDirectImage`. The item-owned strict-system helper is
listed in this item's `lean.declarations`, and its docstring now identifies the
owning item while retaining the direct-image source citation. Its data remains
verbatim reduction followed by the actual system direct image and total limit.

The continuation self-check reread the natural statement and source maps-used
paragraph, the helper and its call in integralPush, all thirteen generator cases
and their two selected maps, the recursive Word.r, the common-bounds and origin
restrictions, primitiveFormulas (including both open inverse laws), and Assertion.
No statement or selected-map data changed. The three framework stmt_deps remain
the accepted additions; only lean differs otherwise from current main. The
second reading is a same-worker self-check under the dispatcher's explicit
no-other-agents instruction. The Lean record date is the current UTC date.

After the ownership docstring and UTC-date update, scompile.py checked the full
module cleanly in both sandbox and library paths (12.0 s and 12.3 s), with no
errors or unexpected warnings. The final dry run and push use this same Lean file.
