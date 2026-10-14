# moduleCup_pullback_cycle_step

## Reason

The current repository lacks the returned module. The sandbox restores the exact
module retained in coord/repair-notes/Sheaf.Paper.ModuleCupPullbackCycleStep.json.
This record documents restoration only; it does not claim to fix the import collision.

## Old

No module source exists in the current repository. The returned source declares
`moduleCup_pairing_exists` and `moduleCup_pullback_cycle_step`, with the signatures
retained verbatim in the sandbox restoration.

## New

Restore both declarations with their original signatures, visibility and proofs.
No definition, theorem statement, upstream instance or upstream module is changed.
The restored module compiles in module mode. The returned non-module import probe
still fails because two upstream local instances have the same generated name.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupPullbackCycleStep | Q3 | restores the returned source |

## Status

landed 20261014T043531-L-1335756 2026-10-14 (merge of deliver/Q3/Sheaf.Paper.ModuleCupPullbackCycleStep)
