## What changed

Proved `pullbackTensorSequenceDirectEvaluation_existsUnique` in
`Sheaf.Paper.CompletedPullbackTensorComparison`. The proof obtains the sectionwise
identity comparison from the new split helper and discharges uniqueness by the
helper's sectionwise uniqueness statement. Added
`Sheaf.Paper.CompletedPullbackTensorDirectEvaluationExistence`, with explicit
sequence-site direct-image data and the two smaller existence/uniqueness
statements used by the consumer.

## Proved and sorry left

Closed the original `pullbackTensorSequenceDirectEvaluation_existsUnique` hole.
The split helper leaves these named statements for later proof:

- `completedPullbackTensorDirectEvaluation_exists`
- `completedPullbackTensorDirectEvaluation_unique`

The pre-existing holes remain in:

- `pullbackTensorReductionModel_existsUnique`
- `pullbackTensorReductionEvaluation_existsUnique`
- `pullbackTensorSequenceInverseEvaluation_existsUnique`
- `pullbackTensorRoosModel_existsUnique`
- `pullbackTensorPullbackTower_existsUnique`
- `pullbackTensorTensorTower_existsUnique`
- `pullbackTensorIntegralPullbackModel_existsUnique`
- `pullbackTensorReductionGood`
- `pullbackTensorIntegralTensorModel_existsUnique`
- `pullbackTensorSequenceCochain_existsUnique`
- `pullbackTensorSequenceGood`
- `pullbackTensorSystemComparison_existsUnique`
- `pullbackTensorComparisonCounits`
- `pullbackTensorSystemComparison_evaluation`
- `pullbackTensorSystemComparison_associativity`
- `pullbackTensorSystemComparison_braiding`
- `pullbackTensorSystemComparison_unit`
- `pullbackTensorQuotientOrdinary_existsUnique`
- `pullbackTensorFiniteGood`
- `pullbackTensorQuotient_existsUnique`
- `canonicalFinitePullbackTensor_quotient`
- `canonicalCommonStagePullbackTensor_existsUnique`
- `canonicalIntegralPullbackTensor_scalar`
- `canonicalRationalPullbackTensor_scalar`

## No longer needed

No declared DAG dependency or imported module was pruned. The helper's direct
`ProEtaleOperations` import was removed because the sequence-systems import
already supplies the declarations used by the helper.

## Where the brief, the DAG or earlier work was wrong

The planned direct-image comparison did not expose a reusable declaration for
its sectionwise identity construction. The proof therefore isolates existence
and sectionwise uniqueness as two strictly smaller helper statements, while the
consumer performs the real combination and type identification.

## New nodes

Added `lem-pur-completed-pullback-tensor-direct-evaluation-existence` for
`completedPullbackTensorDirectEvaluation_exists` and
`completedPullbackTensorDirectEvaluation_unique` in
`Sheaf.Paper.CompletedPullbackTensorDirectEvaluationExistence`.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
