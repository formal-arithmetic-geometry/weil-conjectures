## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralBasicOperationShift` by
constructor cases, using `basicSystemShiftResolutionCalculus` for the tensor
slot coherence and `basicRealizationShiftSquare` for the specified derived
comparison squares and naturality. The proved private helper
`coherentTriple` proves the generic composite component equation without
unfolding the derived total-limit model; `basicSourceCoherent` identifies the composite Mathlib CommShift with the
prescribed reduction-operation-limit source comparison. The proper-image
comparison is identity, so its two equations are proved directly.

The proper-image branch of `BasicShiftOperation.sourceShift` now uses the
canonical composite component of `basicIntegralPushShift`, instead of expanding
that same component. This preserves the constituent shifts and their normalization
while avoiding expensive kernel normalization of the derived-limit model. The
change record is `coord/changes/J6-integral-basic-operation-source-shift.md`.
The downstream scan found no actual external use of this definition and no forced
consumer adaptation. Independent definition/statement review is requested there.
The theorem statement, public imports and unit route are unchanged. Updated the
item's proof plan and proof dependencies to match the assembly. No new nodes.

## Proved and sorry left

Closed the single hole in
`WeilConjectures.IntegralSystemRealization.integralBasicOperationShift` (node
`lem-pur-integral-basic-operation-shift`): 1 of 1 original holes closed.
Zero holes remain in the item, zero holes added and zero split off. The proof
uses the already stated dependencies, including their existing open proofs;
this does not assert that the transitive dependency closure is sorry-free.

## No longer needed

The following private proof imports were removed after replacing the old model
argument with the two existing basic-operation interfaces:

- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.SfCommonStageDirectImage`
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`
- `Sheaf.SixFunctors.CompletedTensorShiftRight`
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.Paper.DerivedAdjunctionShift`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`
- `Mathlib.CategoryTheory.Shift.CommShift`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`

The direct proof uses only `def-pur-integral-operation-shift-data`,
`lem-pur-basic-system-shift-resolution-calculus`,
`lem-pur-basic-realization-shift-square`, and Mathlib's composition-shift
infrastructure represented by `lem-weil-pbc-commshift-nattrans-comp-whisker`.
The following former direct proof dependencies are subsumed by the existing
realization-square declaration and are removed from the item's proof_deps:
`def-pur-integral-derived-operations`, `def-weil-derived-direct-image`,
`lem-pur-completed-primitive-counit-comparison`,
`lem-pur-injective-tower-roos-shifts`, `lem-pur-reduction-limit-shift-adjunction`,
`lem-sf-integral-open-reduction-comparison`, and
`lem-sf-primitive-reduction-transpose`. They remain needed by the dependencies;
no module is withdrawn and no whole-closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The module's old docstring carried the earlier six-step model argument, whereas
the current DAG already exposes resolution laws and derived realization squares
that permit a direct assembly. The latest blueprint places
`fix-prop-coherence.proof.md` under `sk-thm-sf-compatibility` rather than the old
`sk-thm-sf-package` path. No mathematical statement correction was needed. The expanded proper
source shift was mathematically correct but caused avoidable kernel normalization;
the equivalent presentation is documented in the change record.

Searches run through msearch: LeanFinder returned
`CategoryTheory.Functor.CommShift.comp` and its component formula; Loogle for
`Functor.commShiftIso` reported an unknown identifier; grep found the composite
component lemmas. Local source search located the two existing basic-operation
interfaces, avoiding any split-off statements.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
