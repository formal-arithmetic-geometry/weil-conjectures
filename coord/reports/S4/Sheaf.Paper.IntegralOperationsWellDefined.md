## What changed

Prove `WeilConjectures.integralOperationsTensorTransition_existsUnique`.
Transpose the two finite semilinear reduction maps under scalar extension, use
its normalized signed-total tensor comparison, and transpose back. Its generator
formula gives naturality. Local surjectivity of the completed projection, tensor
extensionality and direct-sum extensionality give uniqueness. The adjunction-unit
generator is compared with the original sheafification generator before integral
specialization. Naturality compares the curried total map with the simultaneous signed-total map,
then uses the scalar-restriction naturality equation. The node records this
argument and its dependencies.

The repair changes only IntegralOperationsWellDefined. Drop all returned changes
to CompletedIntegralCoefficients and IntegralReductionTowerUnrestricted. Restore
the private `goodComplexes_isLocalization`, and retain the original operation
return types and ordinary transparency of TensorLevel. Remove the dead
`uncurry_map`, empty TensorTransition section and file-level linter suppressions.
Reuse existing flat-representative localization and site tensor-invariance proofs.

Seven public transparent helpers share forgetful-functor, section-evaluation,
termwise scalar-restriction and tensor-composite data. Ten existing private theorem
headers and the private restrictComplexMap header use definitionally equal aliases.
TensorLevel factors the original curried tensor composite through its transparent
helper; its return type and ordinary transparency stay verbatim. The private
projection body uses the same forgetful functor alias. Every other existing
non-theorem body stays verbatim. The change record contains all sixteen actual
old/new interfaces or bodies and the consumer inventory. New proof helpers are
private and proved. The eight new private proof definitions use no_expose; no
original private declaration has that attribute added. No coefficient object, scalar action, generator formula,
operation or mathematical proposition changes. Challenge is untouched.

Validation: deliver3.py checks the complete final file with its timed single-file
compile and the axiom probe for every public declaration before it pushes.
The final source passed lcompile.py in 59.2 seconds. The actual delivery also passed
its compile, all 49 public-declaration axiom probes, and server preflight. The named consumers below
were checked using unchanged live or quarantined sources against definitionally
equal public operation data and propositions. The final private restriction-functor
and adjunction caches are transparent wrappers; the private restrictComplexMap
header also uses that alias. All 111 original declarations remain. A fresh compatibility check also passes (2.3 seconds): it imports the rebuilt
module and checks scalar-restriction functor equality by rfl, restrictComplexMap
at its original header, and restrictComplexMap_apply at its original equation.
Diagnostic sources and compiled artifacts are outside the delivery payload.

| Consumer | Result against this repair |
| --- | --- |
| NormalizedIntegralTensorTower | Pass, 37.9 s |
| IntegralTensorTransitionCompatibility | Kernel check passes; latest 62.5 s exceeds the limit (earlier pass, 56.4 s) |
| PurTwistSheafLocallyFree | Pass, 4.4 s |
| IsomorphismComparisonNatural | Pass, 51.0 s, with its unchanged derived-operation and comparison dependencies rebuilt in the same job |
| IntegralDerivedOperationsOnSlices | No proof errors; 66.7 s exceeds the limit. Its unchanged published baseline also exceeds the limit at 65.1 s |
| NormalizedPullbackCompositionTransport | Cannot load CompletedPrimitiveCounitComparison. That dependency is currently quarantined in coord/rework.tsv with an unavailable upstream SfP1ChartExchange dependency; this consumer passed an earlier definitionally equal prototype in 26.0 s |
| PointTransportConeComparisonDescent | Kernel check passes in the six-file rebuild; its reported 66.1 s exceeds 60 s |

Compiling consumers against old dependency artifacts exposed references to
changed generated auxiliary proof names. Rebuilding the derived-operation and
comparison chain resolves these for IsomorphismComparisonNatural. The compile
tool deliberately ignores unchanged sandbox artifacts in later jobs, so these
compatibility checks rebuild the unchanged chain and consumer together. This also
resolves the generated-name errors in PointTransportConeComparisonDescent. Consumer
source adaptations are absent. The named missing published dependency is an
existing quarantine entry, and the slice module's timing failure reproduces on
the baseline.

## Reviewer correction (cc review of 14229d41)

The delivered public statements of integralOperationsPullbackTransition_existsUnique
and integralOperationsTensorTransition_existsUnique, and the private liftMap_apply,
were wrapped in the reducible section-evaluation aliases. They are definitionally
equal to the originals, but `rw` in unchanged consumers no longer matched:
NormalizedIntegralPullbackTower:355, CompletedTensorFiniteShift:380 and
IntegralTensorLeftShiftUnique:522 failed against the delivered module and pass
against the published one. The reviewer restored the three original statements byte
for byte; the proofs are unchanged and compile. The change record and node note now
count thirteen changed declarations. The "definitionally equal, source unchanged"
claim for consumers above was not sufficient: a syntactic statement change breaks
`rw` even when the kernel accepts it.

## Proved and sorry left

Original holes: 1. Closed: 1, by name:
`WeilConjectures.integralOperationsTensorTransition_existsUnique`
(blueprint: `lem-pur-integral-operations-well-defined`).

Added holes: 0. Split off: 0. Remaining holes in the item: 0.
All new proof helpers are proved, and no definition contains a hole.

## No longer needed

Remove the direct proof import
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`:
`CategoryTheory.flat_representative_localization` from FlatRoosFunctorDescent
supplies good-representative localization. Remove the direct proof import
RingedKFlatSingleTensorComparison: existing private site-descent helpers supply
tensor quasi-isomorphism invariance. Its unused direct localization dependency
is removed from the node.

The direct dependency `lem-pur-cochain-comparison-monoidal-equations` is unused:
naturality follows from the generator formula and input-map naturality.
The independent scalar-extension tensor comparison and its homogeneous-generator
equations are used. No declaration or module is withdrawn; the unit route stays.

Every returned edit to the coefficient and reduction modules is absent. The
returned extra operation return types and TensorLevel implicit_reducible attribute
are absent. No additional consumer modules are delivered.

## Where the brief, the DAG or earlier work was wrong

The returned packet changed coefficient and operation interfaces and incorrectly
claimed that consumers needed no adaptations. This repair follows the item-local
option, restores the missing private localization helper, and records the exact
remaining transparent changes instead of claiming all source interfaces verbatim.
The tensor transition is now proved by actual Lean composition and generator
arguments. No adopted source-library declaration changes.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
