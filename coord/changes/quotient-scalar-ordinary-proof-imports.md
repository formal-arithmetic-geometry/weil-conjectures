# quotient scalar ordinary proof imports
## Reason
The assigned proof imports two strict intermediate theorem modules. This changes only the proof-facing imports and adds the declared intermediate interfaces.
## Old
The item imported only `Sheaf.Paper.QuotientSectionTensorData`.
## New
The item additionally imports `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedMap` and `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso`.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.QuotientScalarSectionComparisonExistence | unclaimed | imports the completed item |
## Status
landed 20261027T210307-L-1684758 2026-10-27 (merge of deliver/W3/Sheaf.Paper.QuotientScalarSectionOrdinaryComparisonExistence)
