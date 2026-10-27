## What changed

The item theorem now composes two new, strictly simpler public steps. The existence step supplies the normalized open scalar projection mate, and the transport-square step supplies its realization equation. The item imports these two proof modules and combines their conclusions without changing the original statement.

## Proved and sorry left

The original declaration `AlgebraicGeometry.etaleBrownOpenScalarTransport` is proved by a real composition of the two split-off declarations. Two strictly simpler obligations remain as named theorems with `sorry`: `AlgebraicGeometry.etaleBrownOpenScalarTransport_exists` in node `lem-pur-etale-brown-open-scalar-transport-existence`, and `AlgebraicGeometry.etaleBrownOpenScalarTransport_square` in node `lem-pur-etale-brown-open-scalar-transport-square`.

## No longer needed

No existing imports or declared dependencies were pruned. The item uses the normalized Brown realization interfaces and the two split-off modules; the original generic mate and exchange declarations remain recorded in the item node's route.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan does not provide a directly available declaration constructing the left open scalar isomorphism from the normalized right mate. The supplied interfaces expose the right mate and transport normalizations, but the invertibility and the representative transport calculation are separate obligations. They are therefore recorded as two strictly simpler nodes rather than left as an anonymous partial proof.

## New nodes

`lem-pur-etale-brown-open-scalar-transport-existence` records existence of the open scalar projection mate with its prescribed mate equation. `lem-pur-etale-brown-open-scalar-transport-square` records the displayed realization transport square for a supplied normalized mate.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleBrownOpenScalarTransport": "a07cc9b318fe5d943ad565f1e6108107f2528baf", "Sheaf.Paper.EtaleBrownOpenScalarTransportExistence": "98ffb4c0d6f3cecaa3196920246622a7c81283a4", "Sheaf.Paper.EtaleBrownOpenScalarTransportSquare": "7a8abd0fc6cad92a92fcf05c3c9fc0a36b984d58"}, "results": {}, "time": "2026-10-28T03:36:09+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
