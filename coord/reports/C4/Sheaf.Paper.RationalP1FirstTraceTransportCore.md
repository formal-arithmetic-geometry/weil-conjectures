## What changed

The core theorem now normalizes `CounitComponentNormalized` by extracting its
canonical projection invertibility witness and converting its `HEq` witness to an
equality. It substitutes the arbitrary counit and applies the new normalized
counit equality theorem. The normalized equality is isolated in
`Sheaf.Paper.RationalP1FirstTraceTransportCounit` with its own DAG node.

## Proved and sorry left

The `sorry` in
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_trace_transport_core`
is closed. One `sorry` remains in
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_trace_transport_counit`,
the strictly simpler equality with the ambient counit already replaced by its
canonical `counitComponent` and with its projection invertibility supplied
explicitly.

## No longer needed

No imports or declared mathematical dependencies were removed. The core proof
uses only the new normalized-counit theorem after the explicit normalization
calculation; the original core module's broad proof plan is retained on the
new theorem's DAG node because it is the remaining trace/Kunneth calculation.

## Where the brief, the DAG or earlier work was wrong

The earlier split left the core equality coupled to the arbitrary counit and its
normalization predicate. That coupling is a separate, fully provable step: the
predicate is existential data whose `HEq` field directly identifies the counit
with `counitComponent`. The DAG now records this normalization as the actual
proof of the core theorem and leaves only the canonical-counit trace transport
calculation as a new node.

## New nodes

- `lem-sfb-rational-p1-first-trace-transport-counit`, implemented by
  `Sheaf.Paper.RationalP1FirstTraceTransportCounit`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1FirstTraceTransportCore": "25a633feefafb9e4b99d6c68a26dab6e33476922", "Sheaf.Paper.RationalP1FirstTraceTransportCounit": "2c28b2e05f5ba97f66679a09af1ea4fc471a63db"}, "results": {}, "time": "2026-10-28T03:59:06+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
