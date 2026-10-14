# moduleCup_pullback_cycle_step

## Reason

Restore the returned delivery from the source retained in the repair record. The
current repository and initial repair sandbox omit the item entirely. Preserve both
public theorem signatures from the returned delivery. The pairing-existence module
is needed only by the proof and is imported nonpublicly.

## Old

No module source exists in the current repository. The returned delivery declares
`moduleCup_pairing_exists` and `moduleCup_pullback_cycle_step`; both signatures are
preserved verbatim in this restoration.

## New

Restore both declarations and their complete proofs from existing library theorems.
Change `public import Sheaf.Paper.ModuleCupPairingExists` to a proof-only import.
The reported upstream instance collision no longer reproduces with the current
compiled baseline: the restored item compiles and its dry-run axiom probe runs.
No upstream module, instance, definition, or theorem signature is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupPullbackCycleStep | V4 | restores returned signatures and proofs |

## Status

landed 20261014T025145-L-159082 2026-10-14 (merge of deliver/V4/Sheaf.Paper.ModuleCupPullbackCycleStep)
