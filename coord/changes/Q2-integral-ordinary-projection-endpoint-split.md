# Integral ordinary projection endpoint split

## Reason

The existing endpoint comparison hole contains two independent steps: constructing source and target endpoint isomorphisms, and proving their pasted compatibility equation. The delivery names both steps as separate public statements so they can be proved independently while keeping the parent arrow theorem fully checked.

## Old

The parent endpoint theorem contained one unresolved proof of both endpoint construction and compatibility.

## New

`IntegralOrdinaryProjectionEndpointIsoData` introduces the endpoint data structure and its existence theorem. `IntegralOrdinaryProjectionEndpointCompatibility` states the compatibility equation for that data. The parent module imports these proof-only modules and combines them with `Arrow.isoMk`.

## Users

| module | effect |
| --- | --- |
| `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` | Uses the two strict endpoint steps to construct the arrow isomorphism. |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` | Uses the endpoint data structure. |

No existing target signature or source-library declaration was changed.

## Status

landed 20261027T210201-L-1668698 2026-10-27 (merge of deliver/Q2/Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison)
