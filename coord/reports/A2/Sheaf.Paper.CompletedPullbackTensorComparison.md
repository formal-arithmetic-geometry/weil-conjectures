## What changed

Filled `WeilConjectures.pullbackTensorDerivedEvaluation_existsUnique` in
`Sheaf.Paper.CompletedPullbackTensorComparison`. The existing cochain evaluation
comparison is composed with the finite intrinsic realization, then descended
through `DerivedCategory.Q` using `Localization.liftNatIso`. The component formula
gives the prescribed representative square. Cancelling the target factorization
and applying `Localization.natTrans_ext` proves uniqueness. Two fully proved private
helpers carry the categorical argument over general abelian categories, avoiding
repeated kernel checking of coefficient-site definitions.

Updated the existing node's proof route and localization dependency. Existing
statements, definitions, imports and the blueprint unit route are preserved.

Validation: the full module compiled through `lcompile.py` in 58.9 seconds, with
no errors or warnings. No profiler or trace options remain.

## Proved and sorry left

Closed 1 of the original 26 holes:
`WeilConjectures.pullbackTensorDerivedEvaluation_existsUnique`.
Added 0 holes and split off 0 statements.

The following 25 existing holes remain, all attached to
`def-pur-completed-pullback-tensor-comparison`:

- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceDirectEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceInverseEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`
- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
- `WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionGood`
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
- `WeilConjectures.pullbackTensorSequenceGood`
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`
- `WeilConjectures.pullbackTensorComparisonCounits`
- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique`
- `WeilConjectures.pullbackTensorFiniteGood`
- `WeilConjectures.pullbackTensorQuotient_existsUnique`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`
- `WeilConjectures.canonicalRationalPullbackTensor_scalar`

## No longer needed

None. No imports, declarations, modules or planned dependencies are withdrawn.
The proof uses existing infrastructure and adds no intermediate obligations.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The existing cochain comparison and the Mathlib
localization API suffice for derived evaluation. Attempts on the ordinary direct
and inverse comparisons encountered excessive unfolding of the coefficient-site
definitions; those attempts remain outside the delivery and their statements are
unchanged.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
