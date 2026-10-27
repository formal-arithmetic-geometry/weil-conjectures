## What changed

The target module now imports two proof-only modules.  Its target theorem is
reduced to the strict quotient square and the normalized total-limit mate assembly, followed by cancellation of the scalar/pullback system isomorphism.
The strict square module states the generator-level equality, and the bridge
module states the independent representative/Roos normalization step.

## Proved and sorry left

The target declaration `scalarTowerPullbackLimitSquare` is proved from the two
named intermediate declarations.  Two strictly lower proof obligations remain:
`scalarTowerPullbackStrictSquare` in
`lean/Sheaf/Paper/ScalarTowerPullbackStrictSquare.lean` and
`scalarTowerPullbackLimitSquare_mate` in
`lean/Sheaf/Paper/ScalarTowerPullbackLimitBridge.lean`.

## No longer needed

No original proof-dependency import was removed.  The target's direct proof
route now uses only the two new split nodes in addition to the public statement
imports; the earlier broad planned dependencies are represented by the bridge's
K-flat and realization-normalization proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node treated the strict quotient generator calculation and the
whole-system normalized Roos assembly as one indivisible step.  They are
separate obligations: the first is a chain-level equality, while the second
uses representative localization and the realization normalizations.

## New nodes

`stage3-pur-scalar-pullback-strict-square` records the strict generator square.
`stage3-pur-scalar-pullback-limit-bridge` records the normalized total-limit
assembly from that square.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ScalarTowerPullbackLimitBridge": "793b9300ca052a4ceee735592ff857a0633c7f2d", "Sheaf.Paper.ScalarTowerPullbackLimitSquare": "e7007e0e38d8a34171ecf7e21a72e31fe3c3eb3c", "Sheaf.Paper.ScalarTowerPullbackStrictSquare": "7001903b1931cdbef61fcbd22cea5ae621c1753d"}, "results": {}, "time": "2026-10-28T02:38:08+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
