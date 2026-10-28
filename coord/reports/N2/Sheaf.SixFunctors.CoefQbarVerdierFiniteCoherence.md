## What changed

Copied the quarantined item source into the sandbox. Added two strictly simpler split-off public
statements, `finite_unit_equation` and `finite_tower_equation`, and changed `finite_coherent`
to assemble them. The split-off files compile individually. The original item remains with its
single proof hole because the assembly currently exceeds the file compile timeout when those
new imports are enabled.

## Proved and sorry left

`finiteData_nonempty` is proved. `finite_coherent` remains sorry. Added `finite_unit_equation`
and `finite_tower_equation`, each with a documented proof plan and one sorry.

## No longer needed

No imports or DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The rational unit and composition APIs exist, but their dependent transport to the exact
`FiniteCoherent` stage equations requires additional normalization lemmas. Direct assembly in
the item exceeds the 60-second per-file limit, so the work was split into the two component
statements required by the stage-3 policy.

## New nodes

The sandbox contains split-off modules `Sheaf.SixFunctors.CoefQbarVerdierFiniteUnit` and
`Sheaf.SixFunctors.CoefQbarVerdierFiniteTower`. Their DAG node records are not yet generated;
the delivery tool will reject this packet until matching node JSON records are added.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence": "c3c8d8d407885b9ea4b4abcb382b0890909d5767", "Sheaf.SixFunctors.CoefQbarVerdierFiniteTower": "03dd0a26e5af398b0c345373ec854b9bcad68cf2", "Sheaf.SixFunctors.CoefQbarVerdierFiniteUnit": "20985e886b6977bc1923199b6b8b0092c2f1e0e2"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierCore": {"hash": "9e958454f1e189dec671106840380e92f3724fdc", "status": "OK"}}, "seconds": 109, "time": "2026-10-28T10:41:49+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
