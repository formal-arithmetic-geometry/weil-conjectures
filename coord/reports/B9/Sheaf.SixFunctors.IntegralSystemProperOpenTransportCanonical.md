## What changed

Closed `integralSystemProperOpenTransportCanonical` by composing three mate identities. Added the explicit `properOpenTransportMate` construction and three split-off theorem modules for adjunct normalization, intrinsic mate identification, and bridge transport.

## Proved and sorry left

The assigned theorem `integralSystemProperOpenTransportCanonical` is proved. Three strictly simpler declarations remain as named proof obligations: `properOpenTransportMate_normalized` (node `lem-sf-integral-system-proper-open-transport-core-canonical-mate-normalized`), `integralSystemIntrinsicMate` (node `lem-sf-integral-system-proper-open-transport-core-intrinsic-mate`), and `properOpenTransportMate_bridge` (node `lem-sf-integral-system-proper-open-transport-core-bridge-mate`). No `sorry` occurs in a definition.

## No longer needed

No imports or declared dependencies were pruned; the proof uses the adjunct module and all three new mate modules.

## Where the brief, the DAG or earlier work was wrong

The original single proof step hides three independent categorical mate calculations. Splitting them into the normalized mate, intrinsic mate, and bridge transport statements gives strictly simpler obligations and leaves the target proof as a real composition of equalities.

## New nodes

`lem-sf-integral-system-proper-open-transport-core-canonical-mate` records the explicit transported mate definition. `lem-sf-integral-system-proper-open-transport-core-canonical-mate-normalized` records adjunct normalization. `lem-sf-integral-system-proper-open-transport-core-intrinsic-mate` records the intrinsic mate identity. `lem-sf-integral-system-proper-open-transport-core-bridge-mate` records the bridge component equation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportBridge": "c34c3f6464a5fed174a073b79746ffb44106c609", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonical": "a22dc2f1f830b02584b057d67e20ffc8334e4310", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonicalMate": "3444dfdac6e30544c936383c2c7d637e044bdc76", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportIntrinsicMate": "008611a6315e20c058c05d12d8b518acf1df38ea"}, "results": {}, "time": "2026-10-28T07:16:46+0800", "transitive": 0, "version": 1}
```

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
