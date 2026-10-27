## What changed

The proof of `rationalP1_first_trace_transport` now constructs the first-projection
isomorphism from `localizingPreservationChecks`,
`line_localizing_of_preservation`, and `projectionMap_isIso_localizing`.  The
remaining terminal trace equality is stated as the strictly simpler theorem
`rationalP1_first_trace_transport_core`, imported privately and applied with the
constructed witness.  The core theorem has a DAG node and retains the detailed
blueprint proof obligation as its source.  No target signature or definition was
changed.

## Proved and sorry left

The original `sorry` in `rationalP1_first_trace_transport` is closed: its
existential witness is proved and the theorem is reduced by a real application
to the core equality.  One `sorry` remains in the new declaration
`rationalP1_first_trace_transport_core`; it is the strict equality component
with the first-projection isomorphism supplied.  The new declaration has the
same blueprint source and a corresponding DAG node.

## No longer needed

The upper proof removes no public imports.  The new core module does not import
the localizing-projection module; that import is needed only by the upper proof.
The broad original proof-plan dependencies remain recorded on the core node,
where they are the dependencies of the unsolved equality, so no mathematical
DAG dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The existing module was a rework item because its published snapshot had bad
imports for sibling modules.  Against the current source tree, the sibling
modules and the localizing results compile.  The original three-step plan is
still the correct route for the equality, but the existential invertibility
part can be discharged directly from the already stated localizing-preservation
lemmas; this makes the split core theorem strictly smaller than the target.

## New nodes

`lem-sfb-rational-p1-first-trace-transport-core` records
`rationalP1_first_trace_transport_core` in
`Sheaf.Paper.RationalP1FirstTraceTransportCore`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1FirstTraceTransport": "770dd6623b95b679aa7caada85cca47687899add", "Sheaf.Paper.RationalP1FirstTraceTransportCore": "3de2d7b6e14eef21c9de683ac5b8efc17a803857"}, "results": {"Sheaf.Paper.RationalP1FirstAmbientContraction": {"hash": "816047452ecc54db4e313b40dee1180b0a19d2f4", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T03:23:35+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
