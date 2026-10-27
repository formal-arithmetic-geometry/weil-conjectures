## What changed

The item theorem now assembles two extracted proof components. `QuotientExpressionKFlatModels`
proves the strict tower construction, transition compatibility, reduction comparisons, and
levelwise `Good` witnesses by applying the existing strict tower theorem and inducting from
`Expression` to `Generated`. `QuotientExpressionKFlatOperations` states the remaining
normalization, tensor-adjoint, and pullback-adjoint component and is imported privately by the
item. The item theorem combines these components with the unchanged public signature.

## Proved and sorry left

Closed the original `quotientExpressionKFlatNormalization` sorry. Closed the new
`quotientExpressionKFlatModels` theorem. One strictly smaller proof obligation remains as the
named theorem `quotientExpressionKFlatOperations` in
`Sheaf.Paper.QuotientExpressionKFlatOperations`; its proof is intentionally left as `sorry` with
its source and proof plan in its docstring and node.

## No longer needed

The item proof no longer uses the direct imports of `ChangeOfRingsKFlat`,
`KFlatTotalTensorModel`, `SheafRingDerivedCoefficientAdjunction`,
`KFlatScalarComparisonNormalization`, `ProEtaleConstantExact`, or
`ProEtaleConstantRingMap`; these private imports were removed. The proof route uses only
`QuotientExpressionKFlatModels` and `QuotientExpressionKFlatOperations` beyond the existing
public statement imports. No existing DAG dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The original ten-step proof plan conflated strict tower construction with normalized operation
adjoints. The strict tower theorem supplies the former but deliberately does not assert
invertibility of transition adjoints. The delivery separates that missing implication into a
strictly smaller operation theorem rather than treating the strict tower output as normalization.

## New nodes

`lem-pur-quotient-expression-kflat-models` records the proved strict-model extraction.
`lem-pur-quotient-expression-kflat-operations` records the remaining named operation-normalization
obligation and its source proof plan.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
