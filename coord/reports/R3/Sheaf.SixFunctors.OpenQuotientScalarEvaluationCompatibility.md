## What changed

Withdraw `Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility` after replacing
its sole parent route. `ScalarCompatibility` now retains only `finite` and `sections`;
the strict quotient transitions and finite component equations remain in
`ScalarComparison.iso` and `ScalarComparison.components`. No downstream proof used
the removed `systems` or `evaluation` projections.

`openQuotientScalarCompatibilityData` now constructs its normalized finite comparisons
from the proved generic `WeilConjectures.openScalarComparison` in
`IntegralOpenScalarRestrictionComparison`, imported privately with `import all`.
The mathematical input is `lem-cbc-ringed-open-scalar-adjunction`; the private
helper implements its continuous-pushforward transport. The proof supplies the coefficient square from `o.projections`, inverts the generic
comparison, and proves its generator formula by inverse cancellation. It does not
use any of the four formerly split helper holes. The scalar-unit proof and strict
tensor comparison keep their existing component formulas and statements.

The DAG definition and the two parent nodes record this route and its interface
change; the withdrawn node is retained with its Lean attachment set to null.
The change record is `coord/changes/open-quotient-finite-scalar-route.md`.

Validation: all 16 files in the direct-consumer and named indirect-consumer
check compiled individually in import order. The slowest was
`OpenTensorQuotientCochains` at 42.7 seconds. Its source and all other consumer
sources were unchanged. The sole warning was a docstring line in the changed
scalar-unit module; that line has been shortened. Temporary consumer copies
were removed before delivery.

## Proved and sorry left

The assigned theorem `openQuotientScalarEvaluationCompatibility` is withdrawn, not
proved: 0 of its 1 sorry is proved, 0 holes are added or split off. No sorry remains
in any changed delivered Lean module. The existing hole-free constructor
`openQuotientScalarCompatibilityData` has a new complete direct proof; its private
helper `normalizedFinite` is completely proved. `#print axioms` for the replacement
constructor reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

The retained, unedited helper holes `openQuotientScalarFiniteCompatibility`,
`openQuotientScalarSectionCompatibility`, and
`openQuotientScalarSystemsCompatibility` leave this route. They are not counted as
proved. The existing `openQuotientScalarComparisonTransition` hole remains needed
and is not changed by this delivery.

## No longer needed

The constructor removes imports of all four modules:
`OpenQuotientScalarFiniteCompatibility`, `OpenQuotientScalarSectionCompatibility`,
`OpenQuotientScalarSystemsCompatibility`, and
`OpenQuotientScalarEvaluationCompatibility` (all under `Sheaf.SixFunctors`).
Their corresponding nodes are
`lem-sf-open-quotient-scalar-finite-compatibility`,
`lem-sf-open-quotient-scalar-section-compatibility`,
`lem-sf-open-quotient-scalar-system-compatibility`, and
`lem-sf-open-quotient-scalar-evaluation-compatibility`.
The constructor's DAG proof dependencies remove all four. Only the assigned item
is withdrawn; the other workers' modules are retained untouched.

`ScalarCompatibility.systems` and `.evaluation` are unused auxiliary fields,
not the strict tower maps required downstream. `ScalarComparison.iso` retains
all coefficient transitions. `ScalarComparison.components` retains the actual
finite scalar component equations. The realized statement and steps of unit
`sk-prop-sf-pf-coherence` stay intact; none of the four pruned helpers is a unit's
own realized statement or step. The source's termwise tensor argument (Stacks
0E8I and 0GL1) does not require the surplus independent system comparison.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned theorem universally equates two independently
arbitrary isomorphisms. Negating only the system comparison leaves its type and
naturality unchanged but negates every evaluated component, so it cannot agree
with the same finite comparison on a nonzero module of characteristic different
from 2. The node's generator argument assumes a normalization absent from its
hypotheses. The analogous old section helper also claimed normalization for an
arbitrary finite isomorphism. This delivery does not invoke either false helper:
it specializes the already proved generator-normalized generic construction.

The old parent decomposition introduced the false evaluation obligation by choosing
its two comparisons independently. Its conclusion included an extra unused system
witness that is not part of the unit's statement. The correction prunes that witness
and gives the complete finite construction actually used by the scalar-unit proof,
rather than trying to prove a weaker replacement of the false evaluation theorem.
The node statement-change records include the old statements and complete citer
audits. No target statement or adopted source-library signature changes.

Edge cases: the generic comparison allows empty and identity opens and zero modules;
the proof uses no nonemptiness, quasi-compactness, boundedness, or restriction on n.
The inverse-cancellation calculation is valid at n=0 as well. The independently
chosen sign-twisted comparison is deliberately not claimed to satisfy normalization.

## Related modules compiled before delivery

39 related module(s) compiled against this delivery by deliver3.py: 38 OK, 1 SLOW.

```json
{"capped": false, "direct": 12, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData": "375521322a276e216752d687a123915554536fe8", "Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.SixFunctors.OpenTensorQuotientData": "dd848f2eae08595ba82107c59f15d85cd76f98f8", "Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility": "8bf1933ae0cbfa59c6411f312948757337a5bf2c"}, "results": {"Sheaf.Paper.CondensedCompositorIntegralLaws": {"hash": "20b936e3ad2b126b53e7ee6679113e826d53b04a", "status": "OK"}, "Sheaf.Paper.CondensedCompositorIntegralRefinement": {"hash": "bed48a075d0d0814398ee4e462fcc21b06599c75", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealization": {"hash": "f3c1e919f021fb3cdb00a8632b9769a75da95541", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealizationData": {"hash": "a0c7b3b8f4c75aba5a0683ba8ad1d550af600aee", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealizationSquare": {"hash": "e3186c1b28171ea2655f06c3eb4fb103ac186cb7", "status": "OK"}, "Sheaf.Paper.CondensedCompositorSystemIndependence": {"hash": "96aa1011abeb2cfef878047d0f4669028f1019b0", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "8339b4e3e8b675fccaec54fc404987de96ebcd23", "status": "OK"}, "Sheaf.Paper.FixedPresentationUniformizerReductions": {"hash": "2195e8aeb4868a9a702ababa433fe6e635c0b07e", "status": "OK"}, "Sheaf.Paper.IntegralProjectionSupportFactorCoordinates": {"hash": "c155141d262d956b48c94dedf4453c261d9a4bbf", "status": "OK"}, "Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates": {"hash": "29822a6085d1fa21a3549b52b76ca7fd3ae0f847", "status": "OK"}, "Sheaf.Paper.IntegralSupportReductionNormalization": {"hash": "13c2c8849d429ec6a339d763cfb51f2bff6d4219", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralTraceData": {"hash": "f7c116653c7faa062b478b61abb0a121463a5af7", "status": "OK"}, "Sheaf.Paper.ResidueCompatiblePullbackFrobenius": {"hash": "3809fb3bf7cf447f73328d73f4943b7fdf05fed4", "status": "SLOW"}, "Sheaf.Paper.TransportIntegralCounitRealization": {"hash": "362789f01525bd317330b272608a9f8d1b5f57d3", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction": {"hash": "dc3510828603f0e52ff4d7a2249b3f08c25fa75c", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly": {"hash": "029bbfb7a3f95cade80e36f8432d666abf17022a", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstruction": {"hash": "ecfed2c7ccc5b634e5234ed5d7238a3c6e1b0b1d", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence": {"hash": "ba3c7868a918eff9ff9e82173364432b81326775", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralSystemExistence": {"hash": "3a2762881292a445abf50cc8f61fb3b3c0be90cb", "status": "OK"}, "Sheaf.SixFunctors.IntegralOperationShiftData": {"hash": "d79d356f094f2fb511f9e0bde2182c3cf96581b4", "status": "OK"}, "Sheaf.SixFunctors.OpenBaseChangeSquare": {"hash": "b1a9eb196eedf6fedd21da03746a629bb1ca2a3e", "status": "OK"}, "Sheaf.SixFunctors.OpenBaseChangeSquareData": {"hash": "23f0050ac3536f128ebd58ad39f3bdbf90af00b7", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorCoherence": {"hash": "40ec5b9e9aebdb322607072e367e522ba8fe214e", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorOpenRealization": {"hash": "b0df9d461069cdec99e0f95bd996476c034fee1b", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorProjectionRealization": {"hash": "699e9dc51edc2bc2d815c1c5eeed30ef90243182", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorQuotientRealization": {"hash": "68a3d8246c930ac0d6d054bf01f6f229d1ecf41e", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarComparisonAssembly": {"hash": "63af754f0493de8ea89967ab3e5f3665e46cb33e", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence": {"hash": "ce933dfed0f9ff0e493da5da797a1dc8c7f3e611", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData": {"hash": "a02014747ab87b117b52907bce21c7efd85fd0bb", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition": {"hash": "8f746f63f296edeed0ccb04b0372f85457ce035e", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibility": {"hash": "67073a17ecbc09d6a14b9b91f3018caaaeb75855", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility": {"hash": "18a3896961b3f560755391ca8f77e371c4738a69", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarSystemsCompatibility": {"hash": "0fceb2a8bad5cf960f924d503fe84d0416272cab", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientAugmentation": {"hash": "d904f1c4144df41fb8695b22e9e9ff731efa2b47", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientCochains": {"hash": "87ce5d0d62cc2097a2fb8d472226a6c55794d836", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientCoefficientComparisons": {"hash": "4e4d8189f0badec569cc53c51c0ae0018049c11b", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientGeometry": {"hash": "d54cdc02726063dde89125f9cc7b7c23fe42f86f", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientRoosNormalization": {"hash": "cf3729f2bee2f45f20c2a4a8d49551a96c094077", "status": "OK"}}, "seconds": 188, "time": "2026-10-28T09:38:25+0800", "transitive": 27, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
