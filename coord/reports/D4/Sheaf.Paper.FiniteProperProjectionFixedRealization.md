## What changed

Restored the quarantined module source and proved `properComponent_fixed_realization`
from the expanded fixed-coordinate calculation
`properComponent_fixed_realization_core`. The core calculation is recorded as a
new DAG node in the same module; the target proof only unfolds the proper component
and coordinate inclusion and applies that intermediate result.

## Proved and sorry left

The target declaration `properComponent_fixed_realization` is proved. One strictly
lower intermediate declaration remains sorry: `properComponent_fixed_realization_core`
(node `lem-sf-finite-proper-projection-fixed-realization-core`).

## No longer needed

None. The module keeps its existing public import because the coordinate definitions
and proper projection constructions are used directly.

## Where the brief, the DAG or earlier work was wrong

The global build failure was caused by the dependency module being quarantined during
the 2026-10-28 build repair. The item source itself remained present and compiled
against the published dependency artifacts after restoration.

## New nodes

`lem-sf-finite-proper-projection-fixed-realization-core` records the expanded
coefficient-level calculation used by the target proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteProperProjectionFixedRealization": "99230460633f6b252c138e977fe3933cedd039d6"}, "results": {"Sheaf.Paper.FiniteProperProjectionTranspose": {"hash": "e383f59ebf5c73b50c4f1b2fc2e2fbe451929c34", "status": "OK"}}, "seconds": 85, "time": "2026-10-28T01:07:15+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
