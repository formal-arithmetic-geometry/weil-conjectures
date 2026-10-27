## What changed

Added `StrictTateTensorTowerPre`, its conversion to `AdicTower`, and two split-off
statement theorems for the quotient-linear pre-tower and its cocycle. The item
proof now obtains those components and assembles the final `AdicTower` with real
Lean code. Added proof-only imports for the two new modules.

## Proved and sorry left

Closed the original `strictTateTensorTower_data` hole by assembling the two
strictly simpler components.

Added two named statement holes:

- `strictTateTensorTower_pre` in node
  `lem-pur-strict-tate-tensor-tower-data-pre`.
- `strictTateTensorTower_pre_cocycle` in node
  `lem-pur-strict-tate-tensor-tower-data-cocycle`.

No definition contains `sorry`.

## No longer needed

No imports or declared dependencies were pruned. The parent proof uses exactly
the two new component nodes; the original direct proof dependencies are recorded
inside the pre-tower and cocycle nodes.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original proof plan combines construction of
the pre-tower and the cocycle in one large step; this delivery separates those
strictly simpler parts so the final `AdicTower` packaging is explicit and
checkable.

## New nodes

`lem-pur-strict-tate-tensor-tower-data-pre` records construction of all
pre-tower fields and level comparisons without the cocycle. Its Lean declaration
is in `StrictTateTensorTowerLiftPre.lean`.

`lem-pur-strict-tate-tensor-tower-data-cocycle` records the balancing cocycle for
a pre-tower. Its Lean declaration is in `StrictTateTensorTowerLiftCocycle.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.StrictTateTensorTowerLiftCocycle": "072b704d23eec348db8619e97abfbe3439328f96", "Sheaf.Paper.StrictTateTensorTowerLiftData": "0fa33403ed435124b3bee42c68a11bc8a929e150", "Sheaf.Paper.StrictTateTensorTowerLiftPre": "a392b21349ced12140bf8ab4f526623782cb0978"}, "results": {"Sheaf.Paper.StrictTateTensorTowerLift": {"hash": "c050e8e4fe4c948d6e64b1c42555249a89e7d96e", "status": "OK"}}, "seconds": 28, "time": "2026-10-28T07:18:02+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
