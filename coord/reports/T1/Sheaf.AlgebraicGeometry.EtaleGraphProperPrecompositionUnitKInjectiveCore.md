## What changed

Proved the assigned representative component theorem by postcomposing its equality with the
codomain identity, applying the split representative normalization theorem, and cancelling
the identity epimorphism. The normalization theorem is isolated in a separate module.

## Proved and sorry left

Closed `graph_proper_precomposition_unit_component_on_complex` (one theorem hole).
The split theorem `graph_proper_precomposition_unit_component_on_complex_after_identity`
remains as one `sorry`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original node treated the representative calculation as one unresolved statement. It
can be reduced to the identity-postcomposed representative equation and a genuine categorical
cancellation step.

## New nodes

Added `lem-pur-graph-proper-precomposition-unit-component-core-after-identity`, whose statement
is the representative equation after postcomposition by the codomain identity.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore": "442f01c764fe59e41b440773a5cc8dd5520158fa", "Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCoreAfterIdentity": "b4a90ea142e1b323c9bf2306543b40829ec9d85f"}, "results": {}, "time": "2026-10-28T04:48:58+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
