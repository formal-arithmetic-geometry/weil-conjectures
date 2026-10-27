## What changed

Proved `WeilConjectures.IntegralProjectionReduction.finiteIntrinsicTensorRealization_component`.
The proof uses `pullbackTensorFiniteModel` and `pullbackTensorFiniteModelIso` from
`Sheaf.Paper.FinitePullbackTensorConstruction`, then transports the existing
`finiteScalarTensorRealization` through the inverse coefficient realization in both
variables. The realization counit and currying counit identify the result with
`evaluatedTensor`.

Added the two proof-only imports required by this route and updated the item's DAG node
with the implemented proof dependencies.

## Proved and sorry left

Closed the only item hole,
`WeilConjectures.IntegralProjectionReduction.finiteIntrinsicTensorRealization_component`.
There are zero `sorry`s left and no holes were added.

## No longer needed

Removed the unused proof imports and planned proof dependencies for
`lem-sfb-proetale-intrinsic-tensor-comparison`,
`lem-exc-intrinsic-realization-tensor-complex`, and `lem-pc-kflat-resolution`.
Their modules are not needed by the implemented transport through the canonical finite
pullback tensor model and the existing finite scalar realization.

## Where the brief, the DAG or earlier work was wrong

The planned representative-level route was longer than necessary. The already available
canonical finite pullback tensor model has exactly the intrinsic tensor required here,
and `finiteScalarTensorRealization` already supplies the fixed-to-intrinsic comparison.
Whiskering this comparison and applying the realization and currying counits proves the
whole natural isomorphism directly, so no new intermediate theorem is needed.

## New nodes

None.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteIntrinsicTensorComponent": "02cfe53b5b9ae3fa5de8818d89727ef63059bc6f"}, "results": {"Sheaf.Paper.FiniteIntrinsicTensorRealization": {"hash": "c6dab40782ee54614459be8d3bc0c9bb401b60ae", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T06:57:27+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
