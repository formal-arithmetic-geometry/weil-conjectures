# cupCechResolution_beta_class_pairing

## Reason

The assigned module is absent from the source checkout. Restore its previous interface
from the recorded repair diff and prove it from the existing total cochain pairing.
No existing signature, definition, visibility, or target statement is changed.

## Old

lean/Sheaf/Paper/CechCupResolutionBetaClassPairing.lean does not exist at the source base.
The former signature is recorded in
coord/repair-notes/Sheaf.Paper.CechCupResolutionBetaClassPairing.json.

## New

Restore the identical signature of
AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing, verbatim in the
delivered node's lean.statement. Both previous public imports are preserved. Its only
proof-only import is now Sheaf.Paper.CupCechTotalCochainPairing. Proved private helpers
supply tensor homology descent and both axis formulas. No sorry is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechCupResolutionBetaClassPairing | R1 | Restore assigned interface and prove it. |

A source search found no current importer of the absent assigned module. No existing
module requires adaptation. Sheaf.Paper.CechCupSignedAxisPairing is left untouched;
this proof no longer imports it.

## Status

landed 20261014T061029-L-2466864 2026-10-14 (merge of deliver/R1/Sheaf.Paper.CechCupResolutionBetaClassPairing)
