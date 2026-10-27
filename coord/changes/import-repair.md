# import-repair

## Reason

The global build reported a bad import of `Sheaf.Paper.EtaleBrownProjectionRealization`. The item statement compiles from `Sheaf.Paper.StrictEtaleSystemInterfaces`, so the public import was repaired.

## Old

`public import Sheaf.Paper.EtaleBrownProjectionRealization`

## New

`public import Sheaf.Paper.StrictEtaleSystemInterfaces`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed | compiles against the repaired item |

## Status

landed 20261027T205815-L-1617955 2026-10-27 (merge of deliver/B8/Sheaf.Paper.EtaleBrownOpenSingletonEvaluation)
