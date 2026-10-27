## What changed

Added a `STATEMENT-DISPUTED` note to the assigned module and retained its
single theorem and signature unchanged. The module compiles with its existing
proof hole. No imports or declarations were changed.

## Proved and sorry left

No theorem was proved. The existing declaration
`WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportPasting`
remains one `sorry` (node `lem-sf-integral-system-proper-open-transport-pasting`).
No new holes were added.

## No longer needed

None. The existing import and the declared proof dependencies remain needed for
the intended corrected transport theorem.

## Where the brief, the DAG or earlier work was wrong

The theorem quantifies over an arbitrary supplied `gamma`, but gives no
hypothesis identifying it with the bridge-conjugate intrinsic semilinear
proper/open gamma, nor any hypothesis asserting the three coherence equations.
Its conclusion is precisely those equations, so the statement does not follow
from the listed `Operations`, `Compositors`, and `OpenComparisons` data. The
blueprint proof text transports equations for one specially constructed
`gamma`; it does not prove them for every function of the displayed type. The
parent module correctly passes the `gamma` produced by
`integralSystemProperOpenTransportCore`, but this item has no such connection in
its signature. A corrected node should either take that transported gamma (with
the bridge compatibility data required by the transport argument) or state
existence of a suitable gamma instead of universally accepting an arbitrary one.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting": "e8d0d00ddaf7f8e0c76f722da337dc1f8c745063"}, "results": {}, "time": "2026-10-28T03:29:18+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
