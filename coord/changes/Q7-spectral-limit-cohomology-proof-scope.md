# Sheaf.Topology.SpectralLimitCohomologyLaws proof scope

## Reason

The proof-local irreducibility attribute prevents the large cohomology f-map
construction from unfolding while applying its identity/composition API. It
changes no public definition, instance, signature or public import.

## Old

No local irreducibility attribute for `spectralLimitCohomologyMap`.

## New

```lean
attribute [local irreducible] spectralLimitCohomologyMap
```

## Users

The public theorem statement and all public imports stay verbatim. No consumer
needs adaptation. The new proof-only modules have no users outside this item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.SpectralLimitCohomologyLaws | Q7 | Proof reduced to f-map laws. |
| Sheaf.Topology.SpectralLimitCohomology | not adapted | Identical public API. |
| Sheaf.Topology.SpectralLimitCohomologyEventualZero | not adapted | Identical public API. |

## Status

landed 20261025T123600-L-1881416 2026-10-25 (merge of deliver/Q7/Sheaf.Topology.SpectralLimitCohomologyLaws)
