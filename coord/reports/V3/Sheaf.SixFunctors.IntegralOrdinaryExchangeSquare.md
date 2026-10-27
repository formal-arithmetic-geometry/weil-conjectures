## What changed

Added the named intermediate module `Sheaf.SixFunctors.OrdinaryBasicSquare`, whose
`ordinaryBasicSquare` theorem isolates the generic ordinary square for `BasicPair`.
The assigned `IntegralOrdinaryExchangeSquare` now closes its exchange case by applying
that intermediate to `BasicPair.exchange`. The proof-only import is private.

## Proved and sorry left

The assigned declaration `ordinaryExchangeSquare` is proved from
`ordinaryBasicSquare` and `BasicPair.exchange`.
The new declaration `ordinaryBasicSquare` remains as one split-off `sorry`; it is the
inductive basic-pair square needed by the exchange and the other generator cases.

## No longer needed

No existing proof-dependency imports were removed. The direct exchange proof does not
need to unfold the expression recursion or introduce separate exchange mate lemmas.

## Where the brief, the DAG or earlier work was wrong

The DAG's exchange proof step relies on the generic basic-pair square, but that helper
was private in `IntegralBasicGeneratorSquare`, a downstream module importing the
assigned exchange module. Importing it directly would create a cycle, so the helper is
split into a standalone upstream module.

## New nodes

`lem-sf-integral-ordinary-basic-square` records the split-off generic basic-pair square
and its proof plan.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare": "514cf43982b4846073cec74c6862a1a28f2df87b", "Sheaf.SixFunctors.OrdinaryBasicSquare": "59bc38b8a8dff86591e9984b26d8e85b65bd3a7f"}, "results": {}, "time": "2026-10-28T04:32:04+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
