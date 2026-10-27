# Sheaf.Paper.SemilinearCompactSupportCoefficientTransport public imports

## Reason

The retained proof needs no declaration from BoundedConstructibleTower. Removing
its unused public import reduces the exposed dependency closure and import cost.
The duplicate normalized-square helper is separately replaced by proof access to
the already imported SemilinearProperOpenMatePasting module. Existing declaration
signatures and definition bodies are unchanged.

## Old

```lean
public import Sheaf.Paper.BoundedConstructibleTower
```

## New

The unused import is removed. All other public imports are retained.

## Users

`python3 tools/downstream.py Sheaf.Paper.SemilinearCompactSupportCoefficientTransport`
reports zero downstream modules on the current shared source. No consumer needs
adaptation, and no target signature or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | F1 | Remove unused import; public declarations unchanged |

## Status

landed 20261024T185128-L-3415620 2026-10-24 (merge of deliver/F1/Sheaf.Paper.SemilinearCompactSupportCoefficientTransport)
