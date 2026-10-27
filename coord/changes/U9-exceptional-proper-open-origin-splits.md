# Exceptional proper/open origin comparison decomposition

## Reason

The parent construction theorem combines two independent stages: constructing the
proper/open strict-system data and proving bounded-origin properties of supplied
data. The delivery records these stages as strictly simpler public statements.

## Old

The parent theorem had one `sorry` proving both stages at once.

## New

The parent theorem obtains `P` and `R` from
`exceptionalProperOpenOriginConstruction`, then obtains the required conjunction
from `exceptionalProperOpenOriginProperties`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalSystemTransport | unclaimed | imports the parent theorem; unchanged signature |
| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | unclaimed | imports the parent theorem; unchanged signature |

## Status

landed 20261027T180841-L-3908925 2026-10-27 (merge of deliver/U9/Sheaf.Paper.ExceptionalProperOpenOriginComparison)
