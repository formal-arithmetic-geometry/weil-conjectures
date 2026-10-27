## What changed

The target module now imports two proof components and combines them with a real
existential construction. `strictTateTensorTower_data` supplies the tower, its
single-complex level isomorphisms, and the strict tower equality.  
`strictTateTensorTower_evaluation` supplies the displayed levelwise evaluation
identity for those data.  The target theorem introduces the data and applies the
second component at every level. Two new Lean modules and two corresponding DAG
nodes record the decomposition.

## Proved and sorry left

The target declaration `strictTateTensorTower_lift` is proved from the two named
component declarations. The delivery adds the strictly simpler declarations
`strictTateTensorTower_data` and `strictTateTensorTower_evaluation`; their proofs
remain `sorry` and are recorded by nodes
`lem-pur-strict-tate-tensor-tower-data` and
`lem-pur-strict-tate-tensor-tower-evaluation`. No `sorry` remains in the target
proof body, and no definition contains a `sorry`.

## No longer needed

The target's original direct proof dependency list is replaced by the two
component nodes. The former K-flat, derived-change-of-rings, and site-restriction
steps remain transitive dependencies of those component nodes; no imported module
was removed.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the strict tower construction and the exact evaluation
comparison into one unproved statement. The available API exposes these as two
independent proof obligations, so the DAG route was too coarse for a compiling
stage-3 reduction. The target statement and all existing declarations are
unchanged.

## New nodes

`lem-pur-strict-tate-tensor-tower-data` records construction of the strict
quotient tower and its single-complex levels in
`lean/Sheaf/Paper/StrictTateTensorTowerLiftData.lean`.

`lem-pur-strict-tate-tensor-tower-evaluation` records the exact
restriction/single and evaluation/single identity in
`lean/Sheaf/Paper/StrictTateTensorTowerLiftEvaluation.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.StrictTateTensorTowerLift": "c050e8e4fe4c948d6e64b1c42555249a89e7d96e", "Sheaf.Paper.StrictTateTensorTowerLiftData": "739a2951d5babb4277921ec7a72f301e0c3fd245", "Sheaf.Paper.StrictTateTensorTowerLiftEvaluation": "7ca15892d146ac5cdab7262b52727565a8d63773"}, "results": {}, "time": "2026-10-28T03:33:59+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
