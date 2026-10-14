# cupCech_signed_axis_pairing

## Reason

The delivery dry run fetched a newer server baseline in which the assigned
module and node are absent. Restore the independently reviewed theorem with
exactly the signature present when this second reading began, and its proved
homology descent. No definition or theorem of an existing module changes.

## Old

Sheaf.Paper.CechCupSignedAxisPairing and
lem-sc-cech-cup-signed-axis-pairing are absent from the fetched baseline.
The original assigned signature is preserved verbatim in the restored module
and in the node's lean.statement field.

## New

Restore cupCech_signed_axis_pairing with the original six component hypotheses
and both homology axis conclusions. Its proof uses the existing total cochain
pairing and proved private tensor-cycle descent and naturality helpers.
No new sorry or arbitrary chosen data is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechCupSignedAxisPairing | M2 | Restore reviewed interface with proof. |

No current source module imports this absent module. No consumer is adapted
and no target statement or definition used by a target changes.

## Status

landed 20261014T063819-L-2814352 2026-10-14 (merge of deliver/M2/Sheaf.Paper.CechCupSignedAxisPairing)
