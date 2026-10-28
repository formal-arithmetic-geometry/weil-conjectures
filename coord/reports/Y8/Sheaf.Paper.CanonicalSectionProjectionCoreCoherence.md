## What changed

Added the final inverse-cancellation proof to `canonical_section_projection_core_coherence`.
The proof rewrites with the strictly simpler precomposition coherence theorem and
cancels the canonical pushforward comparison. Added the split-off module
`CanonicalSectionProjectionCorePrecomposition` and its DAG node.

## Proved and sorry left

Proved `canonical_section_projection_core_coherence` (one existing sorry closed).
The split-off theorem `canonical_section_projection_core_precomposition` remains a
single sorry, with its node recorded in the delivery.

## No longer needed

Removed the unused proof import `Sheaf.CategoryTheory.SectionProjectionUnit`.

## Where the brief, the DAG or earlier work was wrong

The concrete ringed projection/composition transport is not available as a proved
library declaration in the current import closure, so it is recorded as the strictly
simpler precomposition theorem required by the categorical cancellation step.

## New nodes

`lem-sfb-projective-canonical-section-projection-core-precomposition` records the
precomposition identity used by the delivered inverse-cancellation proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CanonicalSectionProjectionCoreCoherence": "b930c97a4ebee0f48886f8b71051dd29c9661e7d", "Sheaf.Paper.CanonicalSectionProjectionCorePrecomposition": "56d924c41ead2c96a54f9cacf5868f7e89979259"}, "results": {"Sheaf.Paper.CanonicalSectionProjectionCore": {"hash": "ead046f67035675e46f38a9533e90ca38ca556e6", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T08:15:12+0800", "transitive": 0, "version": 1}
```

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
