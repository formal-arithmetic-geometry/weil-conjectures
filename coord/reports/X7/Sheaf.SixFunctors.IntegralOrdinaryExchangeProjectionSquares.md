## What changed

Restored `Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares` from quarantine and
proved its conjunction by composing two strictly smaller component theorems. Added
`Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare` for the exchange component and
`Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare` for the projection component.
Both new modules are imported privately by the restored theorem. The import-order
sandbox build compiles all three modules.

## Proved and sorry left

Closed the original hole in `WeilConjectures.IntegralSystemRealization.ordinaryExchangeProjectionSquares`.
Two component holes remain, each as a named public theorem with a complete source and
proof plan in its docstring:

- `ordinaryExchangeSquare` in `IntegralOrdinaryExchangeSquare.lean`.
- `ordinaryProjectionSquare` in `IntegralOrdinaryProjectionSquare.lean`.

Thus one original hole is closed and two strictly simpler holes are split off.

## No longer needed

No declared dependency was removed. The restored theorem still uses the ordinary
expression reduction definitions; the new component modules use the same dependency.
No unrelated module or import was pruned.

## Where the brief, the DAG or earlier work was wrong

The quarantined source had an unavailable public import of
`Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction` in the prior build snapshot,
which caused the recorded bad-import failure. The current shared source provides that
module, so the source was restored and compiled against it. The original conjunction
was too large to reduce directly in the available interface; splitting its exchange
and projection clauses gives independent strictly smaller obligations while
preserving the exact parent statement.

## New nodes

Added:

- `lem-sf-integral-ordinary-exchange-square`
- `lem-sf-integral-ordinary-projection-square`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares": "70262e517d2b5ef75dbd07b19bcac239bff5a686", "Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare": "9aae86f510494aa430d761ef64464cd224de7d11", "Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare": "96d7136f94136e13e6308b6012c9c5a2bd91b608"}, "results": {}, "time": "2026-10-28T00:39:50+0800", "transitive": 0, "version": 1}
```

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
