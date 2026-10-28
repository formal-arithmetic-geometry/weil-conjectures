## What changed

Added `Sheaf.Paper.RationalP1FirstTraceTransportCounitExpandedForDiagram`, which states the
expanded counit transport for an arbitrary `Diagram` on the selected coefficient line.
The assigned module now proves its theorem by specializing this generalized theorem to
`diagram l c Y family`. The generalized theorem is intentionally the sole remaining
proof obligation and has one named `sorry`.

## Proved and sorry left

The assigned declaration `rationalP1_first_trace_transport_counit_expanded` is proved by
specialization. One `sorry` remains in
`rationalP1_first_trace_transport_counit_expanded_for_diagram`, the split theorem in the
new module and DAG node
`lem-sfb-rational-p1-first-trace-transport-counit-expanded-for-diagram`.

## No longer needed

No statement imports were removed. The failed exploratory prefix split was removed from
the sandbox and is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The DAG proof step treated the selected family/reference data as essential to the displayed
map equality, but the conclusion only uses the resulting `Diagram` and its trace maps. The
proof route therefore generalizes the equation to an arbitrary diagram and specializes it
back; the generalized calculation remains a separate stage-3 obligation.

## New nodes

`lem-sfb-rational-p1-first-trace-transport-counit-expanded-for-diagram` records the
arbitrary-diagram split theorem and its Lean attachment.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded": "325265215e48b90b507c6b7f549f97d26145e241", "Sheaf.Paper.RationalP1FirstTraceTransportCounitExpandedForDiagram": "453a23ac2e83b32cf84b796c1759b6eb30c0a048"}, "results": {}, "time": "2026-10-28T08:12:51+0800", "transitive": 0, "version": 1}
```

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
