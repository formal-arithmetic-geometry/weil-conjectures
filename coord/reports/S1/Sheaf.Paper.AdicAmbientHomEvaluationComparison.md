## What changed

Refined the proof of `adic_ambient_hom_evaluation_comparison` to bind the two
strictly smaller component packages with `have` and assemble their fields directly.
The theorem's statement and all public interfaces are unchanged. The two component
proof interfaces remain the named split points already recorded in the DAG.

## Proved and sorry left

`adic_ambient_hom_evaluation_comparison` is proved by a constructor assembling
`CoreLaws` and `CoherenceLaws`. The only remaining sorries are the two previously
split component theorems:

- `adic_ambient_hom_evaluation_comparison_core`, node
  `lem-sf-adic-ambient-hom-evaluation-comparison-core`;
- `adic_ambient_hom_evaluation_comparison_coherence`, node
  `lem-sf-adic-ambient-hom-evaluation-comparison-coherence`.

No definitions contain `sorry`, and this delivery adds no new sorry.

## No longer needed

None. The declarations and imports used by the existing interfaces remain needed.

## Where the brief, the DAG or earlier work was wrong

The recorded global-build failure was caused by the dependency quarantine state:
`NativeAdicRealizationData` and its prerequisites were unavailable to that build.
The restored dependency chain compiles in the S1 sandbox. The DAG decomposition into
`CoreLaws` and `CoherenceLaws` remains the appropriate strict split of the seven-step
argument.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": "bbfaf7d01205bc9f63062395db482061f6d3f51e"}, "results": {}, "time": "2026-10-28T02:17:38+0800", "transitive": 0, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
