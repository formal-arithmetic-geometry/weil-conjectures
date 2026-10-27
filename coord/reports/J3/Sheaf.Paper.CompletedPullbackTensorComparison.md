## What changed

The parent module now proves `pullbackTensorComparisonCounits` by assembling the
tensor counit component and the derived pullback counit component. Two new
modules prove these components from `purNormalizedReconstructionOfScheme`,
`transportedReductionSystems_normalized`, reduction tensor compatibility, and
actual counit naturality. The parent applies the pullback component twice after
identifying its sequence inverse image with the existing functor.

Three existing normalization formulas now have named predicates to avoid
repeated kernel checking in their selection definitions. Local irreducibility
keeps those predicates from being expanded during this file’s elaboration,
while importers keep normal transparency. Unfolding the predicates
restores the original formulas definitionally; no normalization condition or
selected isomorphism changes. The existing evaluation existence proof is kept,
preceded by that unfolding. The refactored parent compiled cleanly in 45.2 seconds,
with all profiling code removed. The unchanged direct consumer
`Sheaf.SixFunctors.PrimitiveQuotientAugmentations` also compiled against the
refactored parent. Its temporary test copy is not part of the delivery.

## Proved and sorry left

Closed:

- `pullbackTensorComparisonCounits`

Also proved, with no new `sorry`:

- `completedPullbackTensor_tensor_counit`
- `completedPullbackTensor_pullback_counit`

Closed 1 of the item's original 24 holes; added 0 holes. The remaining 23
parent obligations retain the same mathematical statements and proof holes.
The tensor-model and quotient normalization formulas now use definitionally
equal named predicates. All 23 are
attached to `def-pur-completed-pullback-tensor-comparison`.

Remaining declarations with `sorry`: `pullbackTensorReductionModel_existsUnique`,
`pullbackTensorReductionEvaluation_existsUnique`,
`pullbackTensorSequenceInverseEvaluation_existsUnique`,
`pullbackTensorRoosModel_existsUnique`, `pullbackTensorPullbackTower_existsUnique`,
`pullbackTensorTensorTower_existsUnique`,
`pullbackTensorIntegralPullbackModel_existsUnique`, `pullbackTensorReductionGood`,
`pullbackTensorIntegralTensorModel_existsUnique`,
`pullbackTensorSequenceCochain_existsUnique`, `pullbackTensorSequenceGood`,
`pullbackTensorSystemComparison_existsUnique`,
`pullbackTensorSystemComparison_evaluation`,
`pullbackTensorSystemComparison_associativity`,
`pullbackTensorSystemComparison_braiding`, `pullbackTensorSystemComparison_unit`,
`pullbackTensorQuotientOrdinary_existsUnique`, `pullbackTensorFiniteGood`,
`pullbackTensorQuotient_existsUnique`, `canonicalFinitePullbackTensor_quotient`,
`canonicalCommonStagePullbackTensor_existsUnique`,
`canonicalIntegralPullbackTensor_scalar`, `canonicalRationalPullbackTensor_scalar`.

The new lemmas isolate the tensor and single-input pullback components; both have
complete Lean proofs from existing declarations.

## No longer needed

None. No existing imports or DAG dependencies were removed. The new tensor
component uses reductionTensor directly, so no separate normalized tensor closure
obligation is introduced. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

None.

## New nodes

`lem-pur-completed-pullback-tensor-counit` records the proved naturality and
reductionTensor argument. `lem-pur-completed-pullback-tensor-pullback-counit` records
the proved specialization of transported reduction normalization and actual
reconstruction. Both inherit the parent unit and blueprint ancestor. The three normalization
predicates attach to the existing parent node; they introduce no new statement
or proof obligation.

Change record: `coord/changes/j3-completed-pullback-tensor-counits.md`.

Performance change record: `coord/changes/j3-completed-pullback-tensor-normalization-cache.md`.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
