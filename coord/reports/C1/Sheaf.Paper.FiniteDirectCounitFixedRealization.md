## What changed

Added the concrete proof of `directCounit_fixed_realization`.  It applies the
finite direct adjunction normalization, transports the coordinate counit to the
intrinsic coefficient adjunction, and cancels the finite pullback isomorphism.
The transport calculation is recorded as a separate module and DAG node.

## Proved and sorry left

- Proved `WeilConjectures.CompactSupportFiniteProjection.directCounit_fixed_realization`.
- One sorry remains in `directCounit_coordinate_transport`; it is the split-off
  coefficient-realization calculation in node
  `lem-sf-finite-direct-counit-fixed-realization-transport`.

## No longer needed

None.  The proof still uses the finite projection coordinates, operation-stage
normalization, and Weil pro-etale inverse-image declarations listed by the DAG.

## Where the brief, the DAG or earlier work was wrong

The running build-error record referred to an obsolete import spelling; the
current source import `Sheaf.Paper.FiniteProjectionFixedCoordinates` compiles.
No mathematical statement was changed.

## New nodes

- `lem-sf-finite-direct-counit-fixed-realization-transport`, implemented by
  `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteDirectCounitFixedRealization": "dde982c49ed88814700b1b1cd6b6f2f308735cf6", "Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport": "c0c5d700a97db9fb861ee8a8c69f933d8ed42aa2"}, "results": {}, "time": "2026-10-28T01:31:18+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
