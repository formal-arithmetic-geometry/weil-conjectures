## What changed

Added the categorical cancellation module `Sheaf.Paper.CanonicalSectionProjectionCoreCoherence` and imported it from the assigned module. The assigned theorem now postcomposes with the inverse canonical comparison, applies the coherence statement, and cancels the isomorphism.

## Proved and sorry left

`canonical_section_projection_core` is proved. One strictly lower proof step remains as `sorry`: `canonical_section_projection_core_coherence` in `Sheaf.Paper.CanonicalSectionProjectionCoreCoherence`.

## No longer needed

No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned DAG node had no proof steps even though the categorical cancellation is a separate concrete transport step. It is recorded as the new coherence node.

## New nodes

`lem-sfb-projective-canonical-section-projection-core-coherence` records the postcomposition cancellation step and is implemented by `Sheaf.Paper.CanonicalSectionProjectionCoreCoherence`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CanonicalSectionProjectionCore": "ead046f67035675e46f38a9533e90ca38ca556e6", "Sheaf.Paper.CanonicalSectionProjectionCoreCoherence": "a1ba036745c33fd8e08e57d9cc1ff04c4a40a97d"}, "results": {}, "time": "2026-10-28T05:34:52+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
