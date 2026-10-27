## What changed

Restored the quarantined item module and proved
`AlgebraicGeometry.ProEtale.finiteGeneralRingIntegrationExponent` by reducing its
normalization to a framewise Kummer trace comparison and applying the existing
uniqueness of `vectorBundleIntegration`. Added the proof-only import of
`Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceExponent`.

## Proved and sorry left

The target theorem `finiteGeneralRingIntegrationExponent` is proved. The categorical
uniqueness helper `integration_eq_of_normalization` is proved. One strictly smaller
geometric statement remains as a split-off sorry:
`finiteGeneralRingLocalTraceExponent`, node
`lem-sp-general-ring-integration-exponent-local-trace`.

## No longer needed

No declared proof dependency was removed. The final proof uses the canonical data,
the vector-bundle integration normalization/gluing API, and the new framewise local
trace node; no additional imports or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The global build record reported a bad import because this item and its canonical-data
dependency were quarantined during the rework. The restored source compiles against the
current published artifacts. The original DAG proof hid the framewise Kummer trace
calculation; it is now represented explicitly by the new local-trace node.

## New nodes

`lem-sp-general-ring-integration-exponent-local-trace` in
`dag/nodes/sec-smooth-purity/lem-sp-general-ring-integration-exponent-local-trace.json`,
implemented by `lean/Sheaf/SecSmoothPurity/FiniteGeneralRingLocalTraceExponent.lean`.
Its statement is the framewise local normalization equation, strictly weaker than the
global integration identity.

The item remains a rework repair; its source was restored from the quarantine copy named by the current rework record.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent": "6757fbc6c4c4dd8b1aec51c104ea1dd3206411c8", "Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceExponent": "163b5881a2403285cf90d27a4c6b53ae69fc9e91"}, "results": {"Sheaf.SecSmoothPurity.FiniteGeneralRingExponent": {"hash": "9366d23b859c06db2997022bcf9a3144d25f7c33", "status": "OK"}}, "seconds": 41, "time": "2026-10-28T00:53:15+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
