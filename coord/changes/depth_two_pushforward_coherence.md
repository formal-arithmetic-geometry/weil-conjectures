# AlgebraicGeometry.Scheme.depth_two_pushforward_coherence

## Reason

The proof now imports two new proof modules. The delivery checker requires a
change record for the target declaration's interface because its imported
proof dependencies and elaborated declaration record changed relative to the
sorry-only module.

## Old

The declaration `AlgebraicGeometry.Scheme.depth_two_pushforward_coherence`
with the target statement recorded in
`dag/nodes/sec-smooth-base-change/lem-sbc-depth-two-pushforward-coherence.json`.

## New

The same declaration and exactly the same theorem signature, with its proof
filled using `exists_depth_two_coherent_module_extension` and
`depth_two_hartogs_algebra_comparison`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension | unclaimed | continues to use the same theorem and signature |

## Status

landed 20261013T054227-L-445829 2026-10-13 (merge of deliver/M3/Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence)
