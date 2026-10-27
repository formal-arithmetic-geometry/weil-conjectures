## What changed

Proved `WeilConjectures.finiteScalarPullback_preservesRepresentatives` as supplied. The
chain-square theorem now reduces by `HomologicalComplex.hom_ext` to a named degreewise
component theorem. Added `Sheaf.Paper.FiniteScalarTensorPullbackChainSquareComponent`
for that component step and imported it privately. The parent DAG route records this
component dependency.

## Proved and sorry left

Closed the existing `finiteScalarTensorPullback_chain_square` proof by degreewise
extensionality. One strictly simpler component statement remains as
`finiteScalarTensorPullback_chain_square_component` in node
`lem-sf-finite-scalar-tensor-pullback-chain-square-component`.

## No longer needed

No imports from the original module were removed. No declared proof dependency was
pruned; the component theorem uses the ordinary comparison, complex tensor pullback,
representative realization, and ordinary pullback-law declarations.

## Where the brief, the DAG or earlier work was wrong

The planned proof step that says the ordinary pure-tensor square and its signed
-totalization are immediate has no existing Lean declaration combining those maps. The
missing degreewise equation therefore had to be split as a separate statement.

## New nodes

`lem-sf-finite-scalar-tensor-pullback-chain-square-component` records the degree-n
component equation used by the extensionality proof. Its proof is left for a later
worker because it requires the ordinary pure-tensor comparison and the signed-total
summand calculation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarTensorPullbackChainSquare": "19e302b571342f2bf1f671c15d5e9b18f894aa1f", "Sheaf.Paper.FiniteScalarTensorPullbackChainSquareComponent": "4fd76d7911c2dbcf900fd3f1c11f2690e0758201"}, "results": {"Sheaf.Paper.FiniteScalarTensorPullbackData": {"hash": "a12fb42f1f960365edde7388c170eedd0a134b1a", "status": "OK"}}, "seconds": 47, "time": "2026-10-28T06:58:36+0800", "transitive": 0, "version": 1}
```

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
