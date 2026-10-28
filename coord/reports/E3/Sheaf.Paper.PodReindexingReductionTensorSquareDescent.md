## What changed

Corrected `podReindexing_reduction_tensor_square_descent` so it uses the canonical
`podReindexingSystemTensor` and `podReindexingIntegralTensorHom` rather than accepting
unconstrained `w` and `v` arguments. Moved the unchanged canonical declarations
`podReindexing_sequence_pullback_eq`, `podReindexingSystemTensor`,
`podReindexingIntegralTensorHom`, and `podReindexingIntegralTensorHom_eq` into the
descent module to avoid an import cycle; the parent now publicly imports this module.
Adapted `Sheaf.Paper.PodReindexingReductionTensorSquare` by removing the moved
local declarations and simplifying its call to the descent theorem.

## Proved and sorry left

No existing sorry was closed. The corrected declaration
`podReindexing_reduction_tensor_square_descent` remains the single sorry in the item
and is recorded by node `lem-pod-reindexing-reduction-tensor-square-descent`.
No new sorry was added, and the moved definitions and theorem have zero sorrys.

## No longer needed

No proof imports were removed. The parent no longer needs local copies of the four
canonical declarations because they are imported publicly from the descent module.

## Where the brief, the DAG or earlier work was wrong

The previous statement was false as an interface: `w` and `v` were arbitrary, while
the conclusion depended on them and no compatibility hypotheses were supplied. A
natural-isomorphism component and a derived-category morphism are not generally
subsingleton, so the conclusion cannot follow from `hPure`, `hA`, and `c` alone.
The node now records this statement change. The parent adaptation was forced: with
the declarations moved, the original parent source produced duplicate declaration
errors; with a private import it produced unknown-identifier errors, so the import
had to become public. The parent theorem's public statement and all moved declaration
signatures are unchanged.

## New nodes

None.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingReductionTensorSquare": "56e89477229aa7381f169a340065e18f63af98f5", "Sheaf.Paper.PodReindexingReductionTensorSquareDescent": "d81a6f9d38b64b4fb01b0cdb8b001976ca05856c"}, "results": {"Sheaf.Paper.PodReindexingTensorLimitModel": {"hash": "e7845dc499daadf8d368cecc8191cd72a3379cb2", "status": "INFRA"}, "Sheaf.Paper.PodReindexingTensorLimitModelDescent": {"hash": "13195861040c7e66e26ae4446eddf389e3ae92cd", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T08:17:05+0800", "transitive": 0, "version": 1}
```

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
