## What changed

Added the proof-only module `Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceCore`, whose
single theorem isolates the local Kummer trace comparison before global vector-bundle
normalization. The assigned module now obtains normalized N-level data and the existing
`VectorIntegrationNormalization` of `vectorBundleIntegration`, rewrites the N-side local
restriction, and applies the core comparison. The assigned theorem statement and its three
public imports are unchanged; the new core module is a private import.

## Proved and sorry left

The assigned declaration
`AlgebraicGeometry.ProEtale.finiteGeneralRingLocalTraceExponent` is proved from the
existing normalization theorem and
`AlgebraicGeometry.ProEtale.finiteGeneralRingLocalTraceExponent_core`.
The core theorem is a deliberately split-off local Kummer trace calculation and remains the
one `sorry`, with node
`lem-sp-general-ring-integration-exponent-local-trace-core`.
One sorry was added by decomposition; no sorry remains in the assigned theorem.

## No longer needed

The assigned proof no longer directly uses `lem-amb-kummer-any-base`,
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` as a proof dependency, or the direct
`def-sp-general-ring-canonical-data` proof route; those are encapsulated by the split core
statement. The assigned module still imports its original public modules because its
statement uses their declarations. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing hypothesis was found. The original proof plan conflated the
local Kummer comparison with the separate global normalization step. The DAG now records
these as two statements: the core node is the local calculation, while the assigned theorem
is the short normalization-and-composition wrapper.

## New nodes

Added `lem-sp-general-ring-integration-exponent-local-trace-core`, stated in
`lean/Sheaf/SecSmoothPurity/FiniteGeneralRingLocalTraceCore.lean`; its proof is the
projective-line and ordered-affine Kummer trace calculation from the source proof.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceCore": "94ed5103317aa4fa25188f9df4798303010db34f", "Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceExponent": "35d73aaea85943aa66e79d7657c595d54bceb44d"}, "results": {}, "time": "2026-10-28T03:45:17+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
