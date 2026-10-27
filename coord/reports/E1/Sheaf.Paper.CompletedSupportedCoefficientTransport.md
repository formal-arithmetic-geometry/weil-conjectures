## What changed

Proved `completedSupportedCoefficient_transport` by constructing the normalized
source from the ordinary coefficient square and applying the exact derived
square to the supplied supported source. Added the strictly simpler ordinary
normalization theorem in `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization`.

## Proved and sorry left

Closed the `completedSupportedCoefficient_transport` hole. One strictly simpler
hole remains in `completedSupportedCoefficient_transport_normalization`, whose
proof is the ordinary degree-zero normalization substep described in its
module docstring.

## No longer needed

No declared dependencies were pruned. The proof uses the completed push square,
the canonical diagonal right-derived construction, the coefficient-reference
interfaces, and the local single-square comparison lemmas.

## Where the brief, the DAG or earlier work was wrong

The planned ordinary normalization step was larger than the derived transport
step and had no independent declaration. It was split into a separate theorem
so the transport proof is complete from a named, strictly simpler statement.

## New nodes

- `lem-diagonal-completed-supported-transport-normalization`: ordinary support
  normalization for the composite coefficient isomorphism.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompletedSupportedCoefficientTransport": "12ac96cda865af05e12b5512703204121bae4e89", "Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization": "ccb36ca7163c658973e858f82ddae27824dec2d2"}, "results": {"Sheaf.Paper.DiagonalCompletedFrame": {"hash": "cae242de3b4cbc84ff5918e44b05bb6448186092", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T04:24:18+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
