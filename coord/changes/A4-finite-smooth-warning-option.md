# FiniteSmoothAdjunctionGeneralBase proof command

## Reason

Repair of returned delivery 54da2eda9. The source ledger classified the identifier
component `sorry` in the file-local option command as an unattributed proof hole at
line 33. Remove the redundant command. This changes only the warning configuration
while elaborating this file: every inherited declaration signature, definition body,
instance and public import is preserved. The module has no actual proof hole.
No tool, option parser or launcher is changed.

Preflight classifies the removal of a top-level command as a command-inventory change
and requires this record. Lean option state is file-local; importers do not inherit
this option command. No target statement or definition used by a target changes.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
universe u
```

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
```

## Users

The complete transitive consumer list was obtained with
`python3 tools/downstream.py Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase`.
No consumer is edited; their holders are not queried or changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Remove redundant warning option. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; not adapted | Identical interface and meaning. |
| Sheaf.Targets.PoincareUncurry | Not queried; not adapted | Identical interface and meaning. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; not adapted | Identical interface and meaning. |
| TargetsCheck | Not queried; not adapted | Identical interface and meaning. |
| WeilConjectures | Not queried; not adapted | Identical interface and meaning. |
| WeilConjectures.PoincareDuality.Poincare | Not queried; not adapted | Identical interface and meaning. |
| WeilConjectures.SmoothPurity.Defs | Not queried; not adapted | Identical interface and meaning. |
| WeilConjectures.TraceFormula.Slop.Correspondence | Not queried; not adapted | Identical interface and meaning. |
| WeilConjectures.TraceFormula.Slop.Dualizing | Not queried; not adapted | Identical interface and meaning. |
| WeilConjectures.TraceFormula.Slop.Main | Not queried; not adapted | Identical interface and meaning. |

All six delivery files compiled in dependency order during the repair dry run.
The local source-ledger scan finds zero holes in the parent and exactly three
named theorem holes in the packet, without unattributed markers. The unchanged
immediate consumer was previously checked against the same declaration bodies.

## Status

landed 20261020T051002-L-1519603 2026-10-20 (merge of deliver/A4/Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase)
