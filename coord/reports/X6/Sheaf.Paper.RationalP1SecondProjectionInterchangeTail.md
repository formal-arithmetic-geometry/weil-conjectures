## What changed

Closed `AlgebraicGeometry.ProEtale.RationalP1.second_projection_tail_cancellation` by reducing it to the explicit fixed projection-map composite in the new proof-only module `Sheaf.Paper.RationalP1SecondProjectionTailCore`. The target proof removes its unused local bindings and rewrites `secondForwardProjection` to that explicit composite.

## Proved and sorry left

The assigned theorem `second_projection_tail_cancellation` is proved. One strictly smaller intermediate theorem remains as `sorry`: `second_projection_tail_cancellation_expanded` in `Sheaf.Paper.RationalP1SecondProjectionTailCore`, recorded by node `lem-sfb-rational-p1-second-projection-interchange-tail-expanded`. No definition contains `sorry`.

## No longer needed

The attempted naturality helper was removed because its source map is not a pushforward of an arrow on the diagonal surface, so the generic twisted-projection naturality square does not typecheck. No existing project import was removed; the final proof uses only `RationalP1SecondProjectionInterchangeCore`, `RationalP1SecondProjectionTailCore`, and the declarations imported by them.

## Where the brief, the DAG or earlier work was wrong

The target's `R` and `Z` local bindings are unused. After eliminating them, the target is exactly the explicit projection-tail cancellation step, with `secondForwardProjection` only hiding its defining composite. The remaining categorical cancellation is recorded as the smaller expanded theorem for a later worker.

## New nodes

`lem-sfb-rational-p1-second-projection-interchange-tail-expanded` records the explicit cancellation theorem in `lean/Sheaf/Paper/RationalP1SecondProjectionTailCore.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondProjectionInterchangeTail": "c22f117d08471c857ac3406700ceb4bf34978b2f", "Sheaf.Paper.RationalP1SecondProjectionTailCore": "4176fda3b8f6824bb5b46581f08168f3dff8a42b"}, "results": {"Sheaf.Paper.RationalP1SecondProjectionInterchange": {"hash": "4e32217ceb9ceb3840280046d74161f1ddb8e93e", "status": "OK"}}, "seconds": 33, "time": "2026-10-28T08:20:37+0800", "transitive": 0, "version": 1}
```

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
