## What changed

Added two named intermediate obligations in the item module and replaced the core theorem's
`sorry` by a complete assembly proof. The intermediate obligations separate construction of
`Mates` and all `ReductionMates` from construction of each `SystemMates` witness.

## Proved and sorry left

`exceptionalIntegralScalarMates_core` is proved by applying the two strictly simpler named
construction theorems and assembling their existential data. `ramifiedRecovery` and
`exceptionalIntegralScalarMates` remain proved. Two split-off sorries remain:
`exceptionalIntegralScalarMates_data` and `exceptionalIntegralScalarMates_system`, recorded by
nodes `lem-sf-exceptional-integral-scalar-mates-data` and
`lem-sf-exceptional-integral-scalar-mates-system`.

## No longer needed

No imports or existing DAG dependencies were removed. The core proof now uses only the two new
split nodes; its previous unsplit proof plan is reduced to those obligations.

## Where the brief, the DAG or earlier work was wrong

The core node's ten-step construction was too large to close as one Lean proof from the available
interfaces. It has been decomposed into the mate/reduction construction and the independent
whole-system transport construction, while preserving the original conclusion unchanged.

## New nodes

`lem-sf-exceptional-integral-scalar-mates-data` records the finite and integral mate plus reduction
construction. `lem-sf-exceptional-integral-scalar-mates-system` records the normalized whole-system
mate construction from that data.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 2 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralScalarMates": "5567d283d70fbf3e0e2f71b8371c9fc0d220e30a"}, "results": {"Sheaf.Paper.ExceptionalRingOperationsExistence": {"hash": "112d99338de58cbb647fba5a8c32490772d4cf78", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCore": {"hash": "ed9fc7758aa9cc288ba28e9d6ed3fe66e0a9a88c", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportFamily": {"hash": "5960d42c061d3c3d87bda0f357d5137c36100426", "status": "INFRA"}}, "seconds": 85, "time": "2026-10-28T02:31:01+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
