## Worker report

The delivery states `WeilConjectures.AdicExceptionalProjection.exists_system`.
Its only proof is `sorry`; it asserts `Nonempty (System (k := k) l)`.
All helper definitions have actual data. The conclusion is deliberately a coherent
family: the item asks for comparisons under composition, identities, and all finite
coefficient extensions, so separate unrelated objectwise existential statements would
lose information. No target, existing mathematical statement, or proof plan was changed.

Hypotheses and categories:

- Arbitrary field: `(k : Type u) [Field k]`. There is no finite-field datum, separable
  closure, perfection, characteristic-positivity or field cohomological-dimension hypothesis.
- Prime invertible in k: `(l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]`.
  `residueInvertible` transports this unit along the actual structure/residue-field map.
- Finite E/Q_l: `Coefficient l` aliases the already recorded
  `ConstructibleExceptionalCoefficients.FieldStage`; it contains the field, its
  Q_l-algebra structure and `FiniteDimensional`; E is quantified in every operation and coefficient diagram.
  Valuation rings and positive quotients are the published `Padic` constructions.
  `n : ℕ` denotes exponent `n + 1`, hence exactly all positive exponents. No
  choice of an independent coefficient ring or uniformizer is introduced.
- Separated finite-type k-schemes: `Space.base : Over (Spec (.of k))`, with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  `Spaces k` is the induced category. Its arrows are the actual arrows over k;
  `arrowFiniteType`, `arrowSeparated`, and `arrowCompact` derive the morphism
  hypotheses from the source and target hypotheses, rather than adding restrictions.
- The completed category is literally `sfIntegralConstructibleCategory l E.carrier
  X.scheme`. `C`, `pull`, `tensor`, `support`, and `scalar` are abbreviations or
  restrictions of the recorded constructions, not new copies of those categories.
  Coefficients on the small pro-etale site retain its object/morphism size convention;
  finite fixed-scalar presentations use `ULift.{u + 1}` of the actual positive quotient.

Clause-by-clause rendering:

| Node clause | Lean field or construction |
| --- | --- |
| Exact R-linear Lf* ⊣ Rf* | `Operation.ordinary : ExactAdjunction ...`; additivity, linearity, CommShift, triangulatedness, adjunction, unit and counit shift equations are recorded. |
| The actual adic direct image | `Operation.directRealization` identifies the restriction with `sfCompletedDerivedDirectImage`. The identity-on-sections `directCoefficients` comparison transports the two existing presentations of its canonical completed coefficient map. `ordinaryNormalization` fixes the adjunction Hom bijection by the ordinary ringed adjunction and the actual completed pullback unit. |
| Exact R-linear Rf! ⊣ f! and constructibility | `Operation.exceptional` has codomain `C l E X`; `Operation.shriek` is the exact R-linear adjunction with the recorded `support`. All preservation data is output, not an assumption. |
| Natural reductions to transported etale f_n! | `Operation.reduction n` is a natural isomorphism to `finiteExceptional`, literally Rnu_* followed by the etale right adjoint followed by nu*. `reductionPlus` and `finiteBounded` discharge the bounded-below domain required by that existing interface. Constructibility is inherited from the reductions of the actual integral category. |
| The integral counit reduces to the finite counit | `Operation.counitReduction`. `finiteCounit` is the intrinsic realization comparison, canonical compact-support site comparison, canonical etale compactification comparison and etale counit, followed by the comparison-adjunction counit. It uses no unrestricted ambient pro-etale exceptional adjunction. |
| Canonical completed projection is invertible | `Projection.iso`. `Projection.normalization` fixes its inverse by the actual ordinary proper-counit/open tensor word and the completed tensor/pullback augmentation maps. `OpenFactorCoherence.Tensor` fixes both Roos coordinates; equality of individual finite evaluations is never used as equality of derived morphisms. |
| Support composition | `Compositions.comp` on every displayed compactification. `compNormalization` fixes it on compatible triangles by `ambientComposition`, the actual proper/open mate followed by the open and direct-image compositors. |
| Independence needed to state composition | `change`, `changeRefl`, `changeTrans`, `refinementOpen`, `refinementNormalization`, `changeRefinement`, and `compChange`. The open-adjunction transpose fixes each refinement comparison; the common-refinement construction then fixes the compositor on arbitrary compactifications. |
| Exceptional composition is its mate | `exceptionalComposition` is defined, with real data, by `conjugateIsoEquiv` applied to `comp.symm`. It is not an independently chosen iso. |
| Identity and associativity | `Compositions.unit`, `leftIdentity`, `rightIdentity`, and `associativity`, with canonical equality transports. Applying mate pasting to these equations gives the identical identity and associativity equations for `exceptionalComposition`. |
| Four scalar comparisons | `ScalarOperation.pull`, `.direct`, `.support`, `.exceptional`, each a `ScalarFunctor`. Pullback is pinned to `scalarPullbackCompleted`; support to the canonical coefficient-adjunction mate `PurCompactSupport.comparison`, through the actual scalar/support realizations. |
| Exceptional scalar comparison is the mate | `ScalarOperation.shriek : ScalarAdjunction ...`. Its unit and counit squares uniquely determine the right comparison as the transpose of inverse left comparison followed by the old counit. The same squares for `.ordinary` fix the direct-image mate. |
| Identity scalar extension | `ScalarFunctor.identity`, through `Scalars.unit`, whose components are the published `integralComparisonScalarUnit`. |
| Tower scalar equation | `ScalarFunctor.tower`, through `Scalars.comp`, whose components are the published `integralComparisonScalarAssociator`. Thus the ordinary multiplication and completion comparisons are retained. |
| Scalar carries both units and counits | The four explicit `ScalarAdjunction.unit`/`.counit` squares in `ScalarOperation.ordinary` and `.shriek`. |
| Scalar carries finite reductions | `System.reductionScalar` explicitly equates the two routes from the L reduction of scalar-extended integral exceptional pullback to the finite L exceptional pullback of scalar-extended reduction. Its four sides use `scalarOperation.exceptional`, `(operation L f c).reduction m`, `(operation E f c).reduction n`, and the independently constructed `finiteExceptionalScalar`. `Scalars.finiteBalance` supplies the canonical scalar/reduction balancing on X and Y, and `m + 1 = e * (n + 1)` retains the ramified exponent. |
| Scalar carries composition and its mate | `System.compositionScalar` and `identityScalar`; conjugate these diagrams using the retained unit/counit squares to obtain the exceptional diagrams. |
| Scalar carries projection | `System.projectionScalar`, with `Scalars.tensor` normalized componentwise by `scalarTensorCompleted`. Both routes are actual natural-transformation components in the completed category. |
| Shift compatibility | `ExactAdjunction.unitShift`/`counitShift`, both `Projection.firstShift`/`secondShift`, the four `System.*ScalarShift` fields, composition and exceptional-composition shift fields, change/identity/reduction and scalar unit/composition shift fields. Shifts are those inherited from the actual derived categories; both tensor variables are retained. |

Recorded dependency interfaces used include:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the coefficient field,
  valuation ring, positive finite quotients and their finiteness.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the completed coefficient
  sheaf and actual constant-to-completed map.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback` and
  `constructibleIntegralTensor`.
- `Sheaf.Paper.SfCommonStageDirectImage` and its `SfDerivedDirectImage` import:
  the ordinary completed-ring direct image and canonical coefficient/reduction maps.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  relating `sfCompactSupportFiniteIntegralFunctor` to the ordinary proper/open composite.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: completed scalar/pullback/tensor
  comparisons, including the normalized completion units.
- `Sheaf.Paper.IntegralScalarExtensionUniverses` and
  `IntegralScalarExtensionConstructibleIntrinsic`: actual integral scalar extension.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` and
  `ProEtaleSiteComparison`: the finite etale categories and comparison functors.
- `SfFiniteExceptionalInverseImage`, `SfOpenExceptionalBaseChange`, and
  `CanonicalCompactSupportSiteComparison`: actual finite exceptional transport,
  intrinsic realization and canonical site comparison.
- `Sheaf.SixFunctors.OpenFactorTensorModel` and `OpenFactorPullModel`: whole-chain,
  representative-normalized tensor/pull completion comparisons. Their existing
  definitions are reused rather than independently chosen comparison isos.
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`: the normalized ringed pull,
  push, open and proper/open mate words used for canonical composition.
- `IntegralCompactSupportCoefficientComparison`: actual coefficient-change mate,
  ordinary tensor square and retained ramified reduction square.
- Mathlib's `Adjunction`, `Functor.IsTriangulated`, `Functor.CommShift`,
  `conjugateIsoEquiv`, and the actual induced/over categories.

The main theorem imports every currently recorded proof-dependency module. The
unstated finite exceptional system theorem remains a proof dependency, not an
extra assumption in this statement. Its natural-language proof appears in the
main docstring as the corresponding step of the complete 14-step proof plan.

Edge cases checked on the statements and constructions: empty schemes and zero
complexes require no nonemptiness; identity morphisms use canonical equality
transports; arbitrary fields include characteristic zero and imperfect positive
characteristic; only invertibility of l is used. Exponent one is included via
n = 0, and no zero quotient is silently substituted. Identity coefficient maps
have the actual multiplication/completion normalization. Towers include ramified
extensions, with target exponent e*n and explicit positive e,n. No common
cohomological-dimension assumption on k, no finite-Tor assumption on the integral
input, and no replacement by a finite-field-only category was introduced.

Searches: LeanFinder for adic constructible exceptional adjunction/projection and
scalar extension returned eight condensed-category results; LeanSearch returned
only generic scalar adjunctions/adic completion results; Loogle returned generic
adjunction declarations for the first query and no hit for the combined
Adjunction/conjugateIsoEquiv/CommShift query. Mathlib grep returned no exceptional
adic interface (the broad adic/adjunction regex also matches monadic adjunctions).
Source and side-library rg found the finite-field coefficient framework, whose
categories and hypotheses differ, and the canonical normalization models reused
here. `blueprint_refs.py search 'adic exceptional'` returned zero blueprint nodes.
The complete successful msearch results are recorded unchanged in each new node.

## New nodes

The six definition nodes supply reusable, narrower interfaces needed to express
this theorem with full canonical diagrams. They assert no new theorem:

- `def-per-adic-exceptional-context`: the actual categories/operations in bundled
  geometry and coefficients, the finite canonical counit, and exact adjunction data.
- `def-per-adic-exceptional-operation`: one ordinary/exceptional adjunction with
  its actual realizations and finite counit normalization.
- `def-per-adic-exceptional-projection-data`: the full ordinary-to-completed
  normalization equation for the projection, and both shift variables.
- `def-per-adic-exceptional-scalar-data`: normalized scalar comparison records,
  identity/tower equations, and the two adjunction squares.
- `def-per-adic-exceptional-composition-data`: normalized refinement/composition
  records and their identity/associativity equations; exceptional composition is defined as a mate.
- `def-per-adic-exceptional-coherent-system`: the simultaneous family with scalar,
  finite-reduction and shift coherence, used as the existential conclusion.

Each uses Bhatt--Scholze Section 6.7/Remark 6.8.15 and the item's canonical-system
proof plan as source. Each includes the authentic searches above and cites the
existing canonical constructions instead of copying their notions. The source
framework's coefficient-field index is reused; its existing finite-field operation
bundles cannot express these arbitrary-field,
actual `sfIntegralConstructibleCategory` interfaces.

## Dependency modules

`def-coef-semilinear-system-models`: the published module initially failed at
scalar model projections in `scalarExtensionSection`, `ScalarTensorPure`,
`scalarEpsilonIso`, and `ScalarTensorComparisonModel` with stuck independent
universe maxima. The lean-only repair uses the current explicitly universe-instantiated
`ScalarData.ordinary`, `object_eq`, `counit`, and `computesOnKFlat` projections in
those definitions, preserving their published names and definitions. It changes no mathematical statement, category, model or
coefficient universe. The module and unchanged node fields are delivered together.

`def-weil-derived-pullback-tensor-hom`: the recorded module could not
elaborate its common-stage pullback, tensor and internal-Hom comparisons against
the current generalized coefficient interface. The delivered dependency module
keeps the same completed, rational and common-stage constructions and statements;
it supplies explicit comparison objects and `ObjectProperty.homMk` endpoints,
with elaboration settings for the stage-category abbreviation. No coefficient
field, category, universe or mathematical hypothesis is changed. Both the
module and its consumer interfaces compile through `scompile.py`.

## Second reading by NY

The dispatcher expressly prohibits starting agents; there was no independent
worker reader. I reread the item and all helper interfaces after writing them.
The maintainer's independent delivery review remains the independent review.
The rereading found and repaired: an unusable finite-field-only framework; an
ordinary direct-image coefficient-map presentation mismatch; an initially missing
canonical compactification comparison in the finite counit; and an insufficient
finite-evaluation-only way to pin the projection. The final interfaces use the
actual whole-chain normalizations and mate equations described above.

## Saved-packet validation, 2026-10-18

Reread the saved theorem and six definition interfaces against the current node.
The hypothesis/clause table above still applies. The current shared
SemilinearSystemModels module gained a sheafification-instance exclusion after
the saved attempt; retained that line alongside the explicit universe repair,
so delivery does not undo the concurrent source update. No statement changed.

## Saved-packet compile repair, 2026-10-18

The first dry run found the unavailable qualified name `Functor.flipFunctor` in
`Projection.firstShift`. Mathlib defines this functor at
`CategoryTheory.flipFunctor`; the corrected reference preserves the identical
first-variable shift compatibility requirement.

The dependency module for `def-weil-derived-pullback-tensor-hom` retains all
constructions and statements. Its final internal-Hom representative map now
supplies the source and target explicitly to `ObjectProperty.homMk`, avoiding
inference of these large category expressions. The compatibility
elaboration options are explicit. Development profiler settings were removed.
The two imports concurrently added to the published SemilinearSystemModels
module are preserved alongside its universe repair.

## Saved-packet validation, 2026-10-18 (continued)

The required dry run compiled the six new interfaces, then identified two
under-applied universe-fixed scalar-model projections in the dependency repair.
`scalarExtensionSection` now applies `ScalarData.objEq` explicitly to the
coefficient map, model and module; `scalarEpsilonIso` likewise applies
`ScalarData.computes` to the coefficient map, model, complex and K-flat witness.
These are elaboration repairs of the existing section and counit constructions.
The item and composition node records now retain their complete signatures,
including the named `(k := k)` arguments, rather than truncating at that syntax.


## Returned-delivery repair self-check, 2026-10-18

The retained packet already contains substantive changes relative to the returned
interface described in the brief. F1: `Operation.ordinaryShift` fixes pullback to
`fieldConstructiblePullShift`; `Operation.supportShift` fixes support to exact-open
and right-derived-proper shift through `sfQcqsCompactSupportRealization`.
`ExactAdjunction.rightShiftCanonical` requires each right shift to equal the
specified adjunction's `rightAdjointCommShift`. Projection uses the two recorded
`tensorShifts` components, including the signed second slot, in explicit component
squares. `redShift` uses the recorded reconstruction-adjunction shift evaluated at
the finite level. `finiteExceptionalShift` uses the etale right-adjunction mate,
comparison adjunction and intrinsic equivalences. `Scalars.shift` is a definition,
transporting the canonical scalar shift through the normalized realization; it is
no longer a free field. Reduction compatibility has no existential shift witness.

F2: `finiteExceptionalFixedScalar` uses the published
`Etale.ExceptionalCoefficients.mateMap`, itself the finite compact-support counit
transpose, and the canonical comparison-site scalar maps.
`finiteExceptionalScalar` transports this map to intrinsic coordinates.
`System.reductionScalar` now mentions the system's own reduction and exceptional
scalar fields and states the full finite exceptional square explicitly. The old
report table entry describing a mere `ReductionComparisonEquation` was stale and
has been replaced above. The owner of `PurCompactSupport.comparison` is cited by
the scalar, composition and coherent-system definition nodes. No independent
second agent was started, as expressly prohibited by the dispatcher.

Validation is blocked by the published build rather than a Lean diagnostic on
these changes. The required saved-packet dry run, a separate `scompile.py` call
for `AdicExceptionalBase.lean`, and a repeated dry run all report:
`INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or
lacks) the live module Sheaf.SixFunctors.IntegralOperationShiftData`.
The corresponding live `.olean` does not exist. The dry runs say nothing was
pushed. The dependency is recorded and its source exists; no duplicate module,
launcher modification, live edit or global build was used to bypass this gate.
The nine delivered files still require successful compilation and preflight once
the published build includes that module.

## Saved-packet retry, 2026-10-18

Started with the retained report and the prescribed `deliver2.py NY
lem-per-adic-exceptional-projection --no-push`. The dry run compiled the private
`DerivedPullbackTensorHom` overlay (48.0 s), then stopped at
`AdicExceptionalBase` because the published live
`Sheaf.SixFunctors.IntegralOperationShiftData.olean` does not exist. The wrapper
again classified this as `INFRASTRUCTURE RETRY (stale live olean)`.
`scompile.py --source Sheaf.SixFunctors.IntegralOperationShiftData` succeeded and
returned its actual canonical tensor/reduction shift source. A separate prescribed
`scompile.py` compile of `AdicExceptionalBase.lean` confirmed the same missing
published object file and exited 75. Thus this is unavailable compiled dependency
infrastructure, not an absent declaration to recreate. The retained canonical
shift and finite exceptional scalar-square repairs were inspected and preserved.
No delivery was pushed; no launcher script, live module or build artifact was
modified, and no global build or duplicate dependency was attempted.

## Saved-packet retry after dispatcher resumption, 2026-10-18

Started by reading this retained report and running the required
`deliver2.py NY lem-per-adic-exceptional-projection --no-push` on the saved
nine-module packet. It again compiled the private
`DerivedPullbackTensorHom` overlay (48.0 s), then failed on the import of
`Sheaf.SixFunctors.IntegralOperationShiftData` in `AdicExceptionalBase`.
The exact wrapper classification remains `INFRASTRUCTURE RETRY (stale live
olean)`; the published object file is absent. The prescribed independent
`scompile.py NY lem-per-adic-exceptional-projection` check of
`AdicExceptionalBase.lean` independently reproduced that diagnostic and exited
75. `scompile.py --source Sheaf.SixFunctors.IntegralOperationShiftData`
successfully returned the recorded source, including `tensorShifts`,
`reductionShift`, and `integralShifts`.

The retained F1 canonical-shift definitions and F2 system-dependent finite
exceptional scalar square were preserved. This failure occurs before Lean
can check them, and supplies no new statement or elaboration diagnostic to
repair. No source was duplicated to evade the published-build gate, and no
delivery was pushed. Successful per-file compilation and preflight of all
nine modules remain required.

## Saved-packet retry, 2026-10-19

Read the retained report first and ran the prescribed `deliver2.py NY
lem-per-adic-exceptional-projection --no-push` without changing the packet.
The private `DerivedPullbackTensorHom` overlay compiled in 48.0 seconds; the
next file, `AdicExceptionalBase`, failed before elaboration because published
`Sheaf.SixFunctors.IntegralOperationShiftData.olean` is absent. The wrapper
classified this as `INFRASTRUCTURE RETRY (stale live olean)` and pushed nothing.

A separate prescribed `scompile.py` check of `AdicExceptionalBase.lean`
reproduced the identical missing-object diagnostic and exited 75.
`scompile.py --source Sheaf.SixFunctors.IntegralOperationShiftData` succeeded,
confirming that the recorded canonical construction's source remains available.
Inspected the retained canonical pull/support/reduction/finite-exceptional
shifts and the system-dependent `reductionScalar` square. Their repairs remain
intact; the missing published compiled dependency prevents their validation.
No live files, launcher files, or compiled artifacts were edited, and no delivery
was pushed. All nine files still need successful compilation and preflight.

## Interrupted-turn continuation, 2026-10-19

Checked the retained report and running processes before repeating any delivery:
no earlier `deliver2.py` or `scompile.py` process for this item was running.
Ran the required saved-packet dry run with `deliver2.py NY
lem-per-adic-exceptional-projection --no-push`. It compiled the private
`DerivedPullbackTensorHom` overlay in 48.0 seconds, then failed before
elaboration of `AdicExceptionalBase` because the published
`Sheaf.SixFunctors.IntegralOperationShiftData.olean` is absent. Its exact
classification was `INFRASTRUCTURE RETRY (stale live olean)`; nothing was pushed.
A separate prescribed `scompile.py` call on `AdicExceptionalBase.lean`
confirmed the same missing published object file and exited 75.
The retained canonical-shift and finite exceptional scalar-square repairs
remain in the sandbox. No live source, launcher, or compiled artifact was
changed. Successful compilation and preflight remain required before delivery.

## Saved-packet infrastructure confirmation, 2026-10-19

This retry began with the saved report and the prescribed delivery dry run.
`deliver2.py NY lem-per-adic-exceptional-projection --no-push` again compiled
the private `DerivedPullbackTensorHom` overlay (48.0 seconds), then rejected
`AdicExceptionalBase` because published
`Sheaf.SixFunctors.IntegralOperationShiftData.olean` is missing. An independent
`scompile.py NY lem-per-adic-exceptional-projection
lean/Sheaf/Paper/AdicExceptionalBase.lean` reproduced that exact diagnostic
and exited 75. Both wrappers classify it as
`INFRASTRUCTURE RETRY (stale live olean)`.

Inspected the retained canonical support, reduction and finite-exceptional
shifts, the right-adjoint shift constraint, the operation shift constraints,
the two projection shift clauses, and the finite exceptional scalar square.
The prior repairs are retained. No Lean diagnostic on those repairs was reached,
no live or launcher file was changed, and nothing was pushed.

## Saved-packet dry-run confirmation, 2026-10-19

This session began with the saved report and the required unchanged-packet
`deliver2.py NY lem-per-adic-exceptional-projection --no-push`. The private
`DerivedPullbackTensorHom` overlay compiled (48.0 s), but `AdicExceptionalBase`
stopped at its import: published
`Sheaf.SixFunctors.IntegralOperationShiftData.olean` does not exist (0.8 s).
The wrapper reported `INFRASTRUCTURE RETRY (stale live olean)` and nothing pushed.
A separate prescribed `scompile.py` on the sandbox `AdicExceptionalBase.lean`
confirmed the identical diagnostic (0.9 s, exit 75).

Inspected the retained support/reduction/finite-exceptional canonical shifts,
right-adjoint shift constraint, operation and projection shift constraints,
and finite exceptional scalar mate and system-dependent reduction square.
The substantive F1/F2 repairs remain present. No new elaboration diagnostic
was reached, and no live source, launcher file or compiled artifact was changed.
All nine delivered modules still require successful compilation and preflight
when the published dependency is available.

## Interrupted-dispatch retry, 2026-10-19

Read the retained report and ran the required unchanged-packet dry run before
any delivery mutation. `deliver2.py NY lem-per-adic-exceptional-projection
--no-push` compiled the private `DerivedPullbackTensorHom` overlay (48.0 s),
then stopped on `AdicExceptionalBase` (0.8 s): published
`Sheaf.SixFunctors.IntegralOperationShiftData.olean` does not exist.
It reported `INFRASTRUCTURE RETRY (stale live olean)` and nothing pushed.
The independent prescribed `scompile.py` call on `AdicExceptionalBase.lean`
confirmed the identical missing object diagnostic (0.8 s, exit 75).

Self-check retained F1's canonical pull/support/reduction/finite-exceptional
shifts, right-adjoint constraint, normalized scalar shift and both tensor shift
squares, and F2's finite compact-support mate and system-dependent exceptional
reduction/scalar square. These substantive repairs remain in the saved packet.
No new elaboration diagnostic was reached; no live source, launcher script or
compiled artifact was changed. Successful compilation and preflight are still
required before pushing.

## Resumed returned-delivery repair validation

The independent prescribed compile of `AdicExceptionalBase` now passes: the
previously missing published shift dependency has become available. The full
dry run reached the retained new scalar helpers and exposed two elaboration
errors that the stale-build gate had hidden. `finiteScalarRingMap` now explicitly
binds the lifted source and target ring types in `CommRingCat.ofHom`; the
comparison direct-image field access is written with valid syntax. The next
per-file compile passed the scalar and composition modules, then found the
missing explicit prime argument in calls to the newly defined `Scalars.shift`.
All these calls now pass `l`. These are typing repairs with the canonical maps
and all shift/scalar squares unchanged.

Rebased the dependency packet against the current shared source and node records.
`SemilinearSystemModels` now uses the published `ScalarData.ordinary`,
`object_eq`, `counit` and `computesOnKFlat` aliases; it preserves the four public
aliases, the current imports and the instance exclusion. The former private
packet aliases are removed. Both dependency node copies preserve the current
review metadata and change only `lean`. No live file was edited.

Self-check of the numbered return: F1's pull, support, reduction, finite
exceptional and both tensor-slot shifts are canonical definitions.
`Operation.ordinaryShift` and `.supportShift` constrain the two left shifts;
`ExactAdjunction.rightShiftCanonical` constrains both right shifts to the
displayed adjunction mates. `Scalars.shift` transports the normalized ordinary
derived scalar shift through the normalized realization. Each comparison is
required to commute with these fixed shifts, and reduction has no existential
shift witness. F2's `finiteExceptionalFixedScalar` uses the finite compact-support
counit mate `Etale.ExceptionalCoefficients.mateMap`, together with the canonical
comparison-site scalar maps. `finiteExceptionalScalar` transports it to intrinsic
coordinates. `System.reductionScalar` states the actual square using the E and
L operation reductions, their exceptional scalar isomorphism, this finite mate,
and the scalar/reduction balancing on both schemes at the retained ramified
exponent. The owner of `PurCompactSupport.comparison` remains cited.
The item's original hypotheses and conclusion are unchanged.

## Final saved-packet self-check, 2026-10-19

The initial required dry run passed: all nine modules compile and server preflight
accepts the retained packet (dry-run commit `700b596a0a`). The prior infrastructure
failure is resolved. Reread the canonical shift definitions and their consumers:
`pullShift` uses `fieldConstructiblePullShift`; support uses the recorded integral
compact-support shift through its realization; both tensor slots use `tensorShifts`;
`redShift` uses `reductionShift`; finite exceptional shift uses the specified
etale/comparison right adjunctions and intrinsic equivalences. The operation's left
shift equalities and `rightShiftCanonical` fix the adjunction shifts, and scalar
shift is transported through the normalized scalar realization. The comparison
fields impose equations for these shifts, with no existential replacement shift.

Reread `finiteExceptionalFixedScalar`, `finiteExceptionalScalar` and
`System.reductionScalar`: the finite comparison is constructed from
`Etale.ExceptionalCoefficients.mateMap`, independently of the integral comparison.
The square explicitly contains both operation reduction maps and
`scalarOperation.exceptional`, with canonical scalar/reduction balancing and the
ramified exponent equation. Both numbered return findings are addressed. Compared
the delivered node copies with current shared records: the two dependency nodes
change only `lean`, and the item changes only `lean` and the added definition-node
`stmt_deps`. No new Lean edits were needed after the successful dry run.
