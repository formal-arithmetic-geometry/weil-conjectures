## What changed

Added `Sheaf.Paper.IntegralScalarPullbackChainTowerComponent`, isolating the degreewise
component of the scalar pullback chain tower identity, and imported it in
`Sheaf.Paper.IntegralScalarPullbackChainTower`. The parent theorem is proved by
`HomologicalComplex.hom_ext` from the degreewise statement. Added the corresponding DAG
node and updated the parent proof route to use it.

## Proved and sorry left

The parent declaration `WeilConjectures.integralScalarPullbackChainTower` is proved.
The split declaration `WeilConjectures.integralScalarPullbackChainTower_f` remains a
single `sorry`, with node
`lem-pur-integral-scalar-pullback-chain-tower-component`.

## No longer needed

No imports or declared proof dependencies were pruned beyond replacing the parent
proof's direct route with the degreewise component route.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires a substantial finite-level and Roos-coordinate
calculation. It was reduced to a degreewise component theorem so that the chain-map
assembly is explicit and mechanically checked.

## New nodes

`lem-pur-integral-scalar-pullback-chain-tower-component` records the strictly smaller
degreewise equality used by the parent theorem. Its Lean module is
`lean/Sheaf/Paper/IntegralScalarPullbackChainTowerComponent.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralScalarPullbackChainTower": "8cbfe392bd5c45c47f29d36c0d021c4c44d80fd3", "Sheaf.Paper.IntegralScalarPullbackChainTowerComponent": "823e3ae9cedd7bd06250ac7a892c6c072917f10e"}, "results": {}, "time": "2026-10-27T23:34:35+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
