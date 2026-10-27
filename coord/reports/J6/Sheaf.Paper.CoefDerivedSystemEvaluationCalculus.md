## What changed

Repair of returned delivery `adf7546a9e3`, reviewer C-adf75, findings 2, 2b and H10.
Only `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, its existing node attachment,
and `coord/changes/J6-local-derived-instance-selection.md` change.

The rejected edits to `CoefficientRingedTensorHomModel`,
`CompletedIntegralCoefficients`, `PrescribedScalarTensorComparison` and
`DerivedChangeOfRingsIndependentCoefficients` are excluded entirely. The published
`coefficientTotalTensor` bifunctor body and the inverse-limit body of
`completedIntegralCoefficientSheafUnrestricted` remain unchanged. The hand-written
`._proof_1` and `._proof_2` declarations are excluded.

All 92 existing declaration headers, structure fields and public imports match
current source. All 154 compiled declaration and field types have identical
expression hashes, all 92 universe-parameter lists agree, and 15 relevant exported
reducibility statuses and instance priorities agree. Both inferred global
comparison definitions retain their complete source bodies. No field is renamed
or aliased, and no target or source-library module changes.

Seventeen item-local bodies retain their original constructions and equations
through twelve new definitions: the recorded ordinary adjunction, its quotient
transformation, the canonical localized counit, three generic comparison equations,
three tensor-model isomorphisms, two mapped complex transformations, and the
original unique-comparison choice. Each choice selector is literally the original
`h.choose`; the tensor comparisons apply the recorded model fields. No additional
mathematical data are chosen.

The scalar-sections model names its ordinary functor separately at each level
and supplies its additive zero-map proof explicitly. Restriction composition uses
`Functor.ext_of_iso` and the existing `normalizedDVRRestrictionCompIso`, already
available from the node's normalized-tower dependency. Unused local monoidal
instances are removed from the K-flat preservation proof. Existing invertibility
proofs and the standard derived instance are supplied explicitly where needed;
the instance-priority adjustment is confined to the new finite tensor constructor.
Both transparency-respecting options remain true.

The additivity instance now applies the existing proved
`scalarReductionExtensionAdditive` directly. Local elaboration uses the ordinary
128 inference-size bound; let cleanup is disabled only for
`CoefficientScalarSectionsModel`, where an isolated benchmark removed about
0.8 seconds of redundant processing. These settings do not alter declarations.

The earlier item-local candidate compiled in 50.1 seconds. Its complete file with
the unchanged standard delivery axiom probe passed in 54.9 seconds, reporting only
the two original theorem holes. Seven compatibility modules also passed: nine full
predicate equations and ten constructor/comparison bodies agree with their
original formulas by `rfl`, five structure-field contracts and eleven constructor
result types check, and the type, universe and attribute comparisons above pass.
For the scalar-sections equation, the displayed original formula supplies its
implicit finite-sections zero-map proof explicitly; no hypothesis is added.

Later full-file checks exceeded 60 seconds, including the first normal delivery
attempt at 78.5 seconds; nothing was pushed by that attempt. A diagnostic with the
128 inference bound passed the same probe in 42.1 seconds, but subsequent actual
item checks remained over the limit. These rejected runs are not claimed as
successful checks. The latest changes are the existing named additivity proof
and the scalar-sections cleanup setting described above. The normal delivery
compile and axiom gates must pass before this packet is pushed.

All 105 current direct importers were checked individually against one fixed compiled item artifact. 98 passed within 60 seconds; 7 exceeded the limit. No Lean errors were reported. Sources changed during the batch were refreshed and checked again. The remaining timing failures and the corresponding checks of identical consumer sources against the original item are:

| Consumer | Repaired item (s) | Original item (s) |
| --- | ---: | ---: |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | 95.4 | 89.1 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | 65.1 | 69.0 |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | 81.4 | 66.7 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | 73.7 | 54.8 |
| `Sheaf.Paper.IntegralOperationRoosEffectivity` | 67.4 | 68.8 |
| `Sheaf.Paper.InternalSectionHomContinuityComparison` | 72.1 | 68.3 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | 72.6 | 73.7 |

These timing checks remain rejected; this report does not claim a passing consumer build. No consumer is adapted.

Additional attempts on the three reviewer-named regression consumers also hit timing limits: `IntegralScalarExtensionWellDefined` completed type checking in 91.1 seconds without Lean errors; `RingedHomCompositionModel` and `RingedSignedBidualLocalization` stopped at 120 seconds. They are not claimed as passing checks. A source import-closure check confirms that none of these three modules imports this item, even transitively. Their shared dependencies are entirely unchanged by the repaired packet.

## Proved and sorry left

Against current source: zero holes closed, zero holes added, two holes left.
No statement is split off. This definition/interface repair claims no new theorem
proof. Existing proved theorem bodies are retained and adapted to the named
constructions where necessary.

The unchanged open declarations are
`WeilConjectures.coefficientEvaluationTensorIso_exists` and
`WeilConjectures.coefficientDerivedSystemEvaluationCalculus`, both attached to
`lem-coef-derived-system-evaluation-calculus`. No definition contains `sorry`.

## No longer needed

All four shared-module edits and their extra node copies and change records from
the returned packet are excluded. The rejected shared tensor aliases, changed
scalar-comparison predicates and hand-written auxiliary proof-name declarations
are excluded. The former `coefficientCompositeRightDerivedComparison` and
`coefficientMappedComparisonComposite` helpers are unnecessary: both original
global-comparison bodies suffice. The unused private `quotientNatTrans_exists`
helper is removed after its short extensionality argument is inlined.

The unaccepted additional evaluation proof is retained only in the scratchpad.
Its five extra private imports are excluded:
`Sheaf.Paper.SemilinearTensorEvaluation`,
`WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`,
`Sheaf.Paper.SystemOrdinaryTensorReduction`,
`Sheaf.CategoryTheory.SequenceModulePullbackEvaluation`, and
`Sheaf.Algebra.Homology.ScalarHomTensorCoherence`.
These modules remain in the library. No library module or DAG node is withdrawn,
and no global module is claimed pruned. The open calculus assembly retains its
original dependencies and route.

## Where the brief, the DAG or earlier work was wrong

The returned packet's isolated checks did not establish library compatibility.
Its shared total-tensor body change broke `mapBifunctor.hom_ext` in
`RingedHomCompositionModel` and `RingedSignedBidualLocalization`. Replacing the
completed ring by a forgotten commutative-ring sheaf broke scalar-instance
synthesis in `IntegralScalarExtensionWellDefined`. Both changes are excluded in
full. `CompletedIntegralCoefficients` and its reviewed 27 direct consumers see no
change to that module's published definition or interface in this packet.

The returned version also unnecessarily changed shared predicates, inferred
comparison types and item signatures. Every original item signature is restored;
all naming now stays in standalone item declarations. No broader instance-priority
change, shared definition change or forced adaptation is required.

The earlier HomComplex import-environment failure is no longer reproduced. No
retired HomComplex module or environment workaround is included.

The current source import graph, rather than the older cached downstream list,
identifies the direct importers checked here. A fresh comment-stripped use scan
covers all seventeen changed bodies and finds 384 users, including those direct
importers; the change record lists their current holders and unchanged interfaces.
No absent or quarantined module is created, deleted or claimed withdrawn.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
