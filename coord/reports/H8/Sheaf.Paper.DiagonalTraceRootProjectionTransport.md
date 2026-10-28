## What changed

Added the proof-only core module `Sheaf.Paper.DiagonalTraceShiftedRootProjectionTransportCore`.
The assigned theorem now unfolds `rootProjectionEquation`, cancels the common source shift
isomorphism, and applies the core transport equation. The core is a strictly smaller
post-cancellation equation and has a documented proof plan. Both modules compile in import
order.

## Proved and sorry left

The assigned theorem
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_shiftedRootProjection_transport`
remains one `sorry`, decomposed into the strictly smaller core theorem
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_shiftedRootProjection_transport_core`,
which also remains one named `sorry`. No definition contains a `sorry`; no original hole is
closed. The core has node
`lem-sfb-diagonal-trace-shifted-root-projection-transport-core`.

## No longer needed

No existing import or declared proof dependency was pruned. The item directly imports the
new core and uses the existing exact-cone projection only through the core's proof plan.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled cancellation of the common source shift isomorphism with the
finite projection transport. That cancellation exposes a strictly smaller equation, so it
is recorded as a separate theorem for parallel proof. The statement of the assigned theorem
is unchanged.

## New nodes

Added `lem-sfb-diagonal-trace-shifted-root-projection-transport-core`, stated in
`Sheaf.Paper.DiagonalTraceShiftedRootProjectionTransportCore`; its proof plan uses the
normalized exact-cone projection, the diagonal limit interface, the trace models, and the
strict root-system transport.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceRootProjectionTransport": "95bfc4dfd88a3786c841ed3a7e90b6fe6a871e6d", "Sheaf.Paper.DiagonalTraceShiftedRootProjectionTransportCore": "20c2e276f9062f743043adb0884d3318c7d5ea4b"}, "results": {}, "time": "2026-10-28T10:44:58+0800", "transitive": 0, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
