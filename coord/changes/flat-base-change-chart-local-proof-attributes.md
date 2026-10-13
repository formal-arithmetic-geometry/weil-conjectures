# exists_flatBaseChange_chart_cohomology_transport

## Reason
The preflight conservatively treats added attribute commands as an interface change.
These attributes are explicitly local to this module and support the proof by preventing
unwanted unfolding of h-maps and pushforward comparisons. No existing declaration
signature or visibility changes, and no definition changes. No importer is affected.

## Old
```lean
attribute [local instance] enoughInjectives
```
The existing theorem signature is preserved verbatim in the delivered module and node.

## New
```lean
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap cohomologyOpenRestriction
  pushforwardComp pushforwardCongr pushforwardId
```
Private proved helpers and a theorem-scoped maxHeartbeats option are added. The two
backward transparency options were already in the module and remain unchanged.

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatBaseChangeChartCohomologyTransport | U1 | Local proof only |
| Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison | unclaimed | Unchanged signature and public imports; no adaptation |

The only direct declaration user is FlatBaseChangeModuleLerayComparison. All transitive
importers continue to see the same original theorem, definitions and public imports.
No original module fails against this change; no forced adaptation is delivered.

## Status
landed 20261013T190158-L-3222629 2026-10-13 (merge of deliver/U1/Sheaf.AlgebraicGeometry.FlatBaseChangeChartCohomologyTransport)
