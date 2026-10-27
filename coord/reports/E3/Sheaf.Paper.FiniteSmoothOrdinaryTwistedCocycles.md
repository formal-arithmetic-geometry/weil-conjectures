## What changed

Restored the quarantined item source and proved its public theorem by reducing the two
ordinary conclusions to two strictly smaller named theorem statements. Added
`FiniteSmoothOrdinaryTwistCocycle` for the ordered root-line tensor cocycle and
`FiniteSmoothPuritySourceCocycle` for the finiteLambda purity-source cocycle. The item
combines these two declarations with a real conjunction proof. Updated the item DAG node
to record the new proof dependencies and added DAG nodes for the two split statements.

## Proved and sorry left

The item declaration `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothOrdinaryTwistedCocycles`
is proved with no `sorry` remaining. The delivery adds exactly two named `sorry` theorems:
`ordinaryTwistCocycle` in `lem-pur-finite-smooth-ordinary-twist-cocycle` and
`puritySourceCocycle` in `lem-pur-finite-smooth-purity-source-cocycle`. These are strictly
smaller conclusions: respectively the first conjunct and the second conjunct of the item.

## No longer needed

No existing import is removed. The original plan's generic proof dependencies are replaced
in the item node by the two split theorem nodes, which are the only declarations used by
the completed item proof.

## Where the brief, the DAG or earlier work was wrong

The assigned module had been quarantined by the global build despite still being an active
stage-3 item; the exact quarantine source was restored. The original DAG bundled two
substantial ordinary coherence arguments into one proof step without separate declarations.
The delivery records those arguments as two strictly smaller stage-3 nodes so the parent
proof is complete and the remaining obligations are explicit.

## New nodes

`lem-pur-finite-smooth-ordinary-twist-cocycle`: root-line tensor cocycle statement and
module `Sheaf.Paper.FiniteSmoothOrdinaryTwistCocycle`.

`lem-pur-finite-smooth-purity-source-cocycle`: finiteLambda/finiteSource cocycle statement
and module `Sheaf.Paper.FiniteSmoothPuritySourceCocycle`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteSmoothOrdinaryTwistCocycle": "eab4e53b11d50438d9d4fad9f91f3a948ab72f1f", "Sheaf.Paper.FiniteSmoothOrdinaryTwistedCocycles": "682e723d4caeb2eb01015ad15bd6503584d239c8", "Sheaf.Paper.FiniteSmoothPuritySourceCocycle": "b1eeae463838d76e186a4e76106bf7b49bf0c11b"}, "results": {}, "time": "2026-10-28T00:41:10+0800", "transitive": 0, "version": 1}
```

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
