# etaleRestrictedSectionsComponentIso proof imports

## Reason

The proof requires two new intermediate statements and imports their modules privately.
The target statement and all existing signatures remain unchanged.

## Old

The target module imported only `Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsFactors`.

## New

The target module additionally imports the proof-only modules
`EtaleRestrictedSectionsComponentEpi` and `EtaleRestrictedSectionsInclusionMono`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparison | unclaimed | sees the proved target theorem; no signature change |

## Status

landed 20261012T225257-L-1800595 2026-10-12 (merge of deliver/B3/Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComponentIso)
