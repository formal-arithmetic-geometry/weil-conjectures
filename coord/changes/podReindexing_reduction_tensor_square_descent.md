# podReindexing_reduction_tensor_square_descent

## Reason
The former declaration quantified over arbitrary `w` and `v`, but no hypotheses related either argument to the canonical normalized comparisons. Since both arguments occur in the conclusion, the statement was under-specified. The corrected declaration uses `podReindexingSystemTensor` and `podReindexingIntegralTensorHom`, which are the canonical maps used by the parent theorem.

## Old
The theorem accepted `(w : ... ≅ ...)` and `(v : ∀ M N, ...)` as unconstrained arguments and concluded the reduction/tensor square using them.

## New
The theorem has no `w` or `v` binders. Its conclusion uses `podReindexingSystemTensor l E g` and `podReindexingIntegralTensorHom l E g c h M N`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PodReindexingReductionTensorSquare` | F6 / unclaimed in this sandbox | Forced adaptation: its call now supplies only the canonical data already used in its frame. |

## Status
landed 20261028T020327-L-2495141 2026-10-28 (merge of deliver/E3/Sheaf.Paper.PodReindexingReductionTensorSquareDescent)
