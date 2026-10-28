# AlgebraicGeometry.Etale.etaleHomComparison_reversedExact_commShift

## Reason

The old statement omitted component equations for the arbitrary composite shifts. The corrected statement passes hPhi and hPsi, which are already supplied by shiftData.

## Old

The old signature allowed arbitrary chiPhi and chiPsi with only hA and hB.

## New

The signature includes hPhi and hPsi component equations.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.EtaleHomTransposeExact | unclaimed | passes hPhi and hPsi |

## Status

landed 20261028T072351-L-1937876 2026-10-28 (merge of deliver/C8/Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftCore)
