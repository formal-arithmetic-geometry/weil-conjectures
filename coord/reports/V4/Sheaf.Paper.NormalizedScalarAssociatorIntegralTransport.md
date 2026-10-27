## What changed

Added the proof-only import `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore`.
The original `normalized_scalar_associator_integral_transport` theorem is now proved by
transporting its `HEq` goal to equality, applying faithful intrinsic inclusion, and invoking
the ambient core theorem. Added the core module and its DAG node.

## Proved and sorry left

The original `normalized_scalar_associator_integral_transport` sorry is closed. The new
`normalized_scalar_associator_integral_transport_core` theorem remains as one split-off sorry;
its node is `lem-sf-normalized-scalar-associator-localization-transport-integral-core`.

## No longer needed

None. The two original public imports remain required by the item statement, and the core
proof interface uses the same scalar-composition and completed-comparison declarations.

## Where the brief, the DAG or earlier work was wrong

The item DAG planned the ambient normalized-comparison calculation but did not expose a
Lean declaration for its faithful-inclusion equality. The proof therefore splits that
strictly simpler ambient equality into a new node; the item theorem is a genuine faithful
transport from it.

## New nodes

`lem-sf-normalized-scalar-associator-localization-transport-integral-core` is stated by
`Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore`; its proof is the ambient
normalized-comparison calculation described in the theorem docstring.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NormalizedScalarAssociatorIntegralTransport": "6bf8e1aa15937c5a2fca7abf4758301c8a406e12", "Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore": "93dd081f7ddacb1aa531c46511e5a93d77595ad2"}, "results": {}, "time": "2026-10-28T03:30:25+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
