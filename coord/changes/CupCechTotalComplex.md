# cupCechAlpha / cupCechBeta source restoration

## Reason
The repair base no longer contains the imported `Sheaf.Paper.CupCechTotalComplex` source,
although the current pairing module imports and uses its definitions. Restoring that source is
required for the delivered module to compile.

## Old
The sheaf-dag checkout had no source file for `CupCechTotalComplex`; the previously delivered
pairing module therefore had an unresolved imported source in this repair checkout.

## New
Restore `lean/Sheaf/Paper/CupCechTotalComplex.lean` verbatim from the prior landed version,
with no declaration or proof changes.

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CupCechTotalCochainPairing | Y3 | required restored import |
| Sheaf.Paper.CupCechTotalCochainAxes | Y3, new in this delivery | required alpha/beta data |

There is no existing source interface to change in the current repair base. Other downstream
consumers retain the same alpha/beta definitions; no consumer adaptation is delivered.

## Status
landed 20261013T234516-L-2165020 2026-10-13 (merge of deliver/N2/Sheaf.Paper.CupCechTotalCochainPairing)
