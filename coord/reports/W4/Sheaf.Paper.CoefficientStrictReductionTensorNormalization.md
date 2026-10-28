## What changed

Added the proof-only import `Sheaf.Paper.CoefficientStrictReductionTensorComparison` and
closed the item theorem by composing its strict comparison existence with the fixed-
comparison representative normalization theorem. The new module contains the two
strictly smaller intermediate statements required by this decomposition.

## Proved and sorry left

The item declaration `WeilConjectures.coefficientStrictReductionTensorNormalization`
is proved. Two strictly smaller intermediate declarations remain sorry:
`WeilConjectures.coefficientStrictReductionTensorComparison_exists` at node
`lem-coef-strict-reduction-tensor-comparison`, and
`WeilConjectures.coefficientStrictReductionTensorNormalization_of` at node
`lem-coef-strict-reduction-tensor-normalization-fixed`.

## No longer needed

No imports or existing nodes were pruned. The original direct proof dependencies are
replaced in the item node by the two intermediate declarations.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combined construction of the strict comparison and its
simultaneous representative normalization in one theorem. These are independent
steps, so the delivery records them as two named intermediate statements.

## New nodes

`lem-coef-strict-reduction-tensor-comparison` records existence of the strict derived
tensor comparison before normalization. `lem-coef-strict-reduction-tensor-normalization-fixed`
records normalization for a chosen comparison. Both are in the new comparison module.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientStrictReductionTensorComparison": "811319f78c461cb42daa5ce7a5af18a60c9ddc45", "Sheaf.Paper.CoefficientStrictReductionTensorNormalization": "d0606d1dbe3bdb0ab8b5f4564aa037679b0cc332"}, "results": {}, "time": "2026-10-28T10:40:51+0800", "transitive": 0, "version": 1}
```

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
