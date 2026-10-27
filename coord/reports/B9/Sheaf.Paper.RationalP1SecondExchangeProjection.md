## What changed

Filled `AlgebraicGeometry.ProEtale.RationalP1.second_exchange_projection` by reducing it to the native endpoint form of the same exchange/projection square. Added `Sheaf.Paper.RationalP1SecondExchangeProjectionNative`, which records the remaining geometric normalization as the strictly smaller native endpoint theorem. The item imports this proof-only module and rewrites the wrapped exchange endpoint to `nativeExchange`.

## Proved and sorry left

Proved the item declaration `second_exchange_projection` (one hole closed). Added one split-off hole, `second_exchange_projection_native`, in node `lem-sfb-rational-p1-second-exchange-projection-native`; its statement keeps the tensor, Tate-line and pullback comparisons but exposes the native module-object exchange endpoint. No definition contains `sorry`.

## No longer needed

No imports or DAG dependencies were pruned. The native endpoint theorem retains the ringed exchange/tensor and module/ringed comparison dependencies recorded by the parent route.

## Where the brief, the DAG or earlier work was wrong

The parent module's wrapper `secondPretraceExchangeMap` unfolds to the native ambient exchange only after the module-object pullback and pushforward aliases are unfolded. The current compilation confirms this endpoint normalization, while the remaining fixed-map coherence is isolated in the new node.

## New nodes

`lem-sfb-rational-p1-second-exchange-projection-native` records the native endpoint normalization theorem in `lean/Sheaf/Paper/RationalP1SecondExchangeProjectionNative.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondExchangeProjection": "89b86c50c691ddc884d6eb69d9a854bae7b013e8", "Sheaf.Paper.RationalP1SecondExchangeProjectionNative": "a10368fb7e42f121eb2b8e4d2ba76db73f69df17"}, "results": {}, "time": "2026-10-28T05:30:01+0800", "transitive": 0, "version": 1}
```

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
