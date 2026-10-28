## What changed

Completed `WeilConjectures.scalarModelRoosZeroLift_strict_exists` in
`Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictExistence`. Apply the existing
`scalarModelRoosZeroLift_strictify` to obtain a map with zero shifted coordinate
and unchanged unshifted quotient coordinates. Apply `scalarModelRoosZeroLift_core`
to that map, then rewrite the coordinate hypothesis to obtain the predicate for
the original map. The statement, definitions, and imports are unchanged. The
existing node proof and proof dependencies already describe precisely this route,
so no DAG edit is needed.

Single-file remote compilation passed without warnings in 5.6 seconds, including
compilation of the current unpublished strictification dependency in the private
overlay.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.scalarModelRoosZeroLift_strict_exists`
(node `lem-trf-scalar-model-roos-zero-lift-strict-existence`).
There are zero `sorry`s left in the delivered module and zero holes added.
No new statements were split off. The proof uses the already stated
`WeilConjectures.scalarModelRoosZeroLift_strictify` in its existing module;
that dependency's existing hole is not modified by this delivery.

## No longer needed

None. Both existing imports are used. Both declared proof dependencies remain
necessary: `lem-trf-scalar-model-roos-zero-lift-strictification` supplies the
strict representative and coordinate equality, and
`lem-trf-scalar-model-roos-zero-lift-core` supplies the scalar lift.

## Where the brief, the DAG or earlier work was wrong

The previous partial body applied the core directly to the original map, leaving
its zero shifted coordinate as an unjustified goal. The existing strictification
interface resolves that goal by changing the input map and preserving exactly the
coordinates used by the conclusion. The current DAG already records this argument.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictExistence": "9917a21bdf149d6db7cd3699d7d37f2ea4d118f8"}, "results": {}, "time": "2026-10-28T11:52:22+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
