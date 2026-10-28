## What changed

Added the canonical-model comparison subclaim and proved the requested comparison by transporting its natural isomorphism across the fully faithful realization. The target theorem now has no `sorry`; the canonical-model subclaim remains the one explicit deferred geometric construction.

## Proved and sorry left

Closed `WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit_comparison` (1 of 1 original hole). Added one strictly simpler named hole, `WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit_model_comparison`, for the canonical family of ForgetModels and its comparison.

## No longer needed

The target proof uses only `Sheaf.WeilSheaf.NativeExceptionalForgetfulData` for the interfaces and the new canonical-model subclaim. The original planned proof dependencies `lem-sf-native-weil-open-proper-forgetting`, `lem-sf-native-weil-scalar-frobenius-counit`, and `lem-sf-adic-qbar-constructible-realization` are retained as dependencies of the split-off subclaim, but are not imported by the target module directly.

## Where the brief, the DAG or earlier work was wrong

The direct geometric construction is strictly below the target's interface and cannot be imported from its existing lower implementation without recreating the known cycle through the parent counit module. The canonical-model subclaim exposes precisely that missing lower interface; the remaining transport is proved directly from full faithfulness.

## New nodes

`lem-sf-native-exceptional-ordinary-counit-model-comparison` in `dag/nodes/sec-six-functors/lem-sf-native-exceptional-ordinary-counit-model-comparison.json`, with module `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitModelComparison`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison": "654f73cd910ecc9a26a1f9c4d3656c79ee8d85d4", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitModelComparison": "7d6fa33d66a0d7922958236b9e11fac250e9f4a4"}, "results": {}, "time": "2026-10-28T09:28:17+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
