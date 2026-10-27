# PrelogUnitPushoutPresentation data import

## Reason

Repair the maintainer return of delivery `511754fafaa` (2026-10-26 10:02 UTC).
The reported source import cycle was:

`PrelogLogificationEtaleConstruction -> PrelogPushoutLogAxiom ->
PrelogUnitPushoutPresentation -> ZariskiPrelogLogificationComparison ->
PrelogLogificationEtaleConstruction`.

The comparison theorem now consumes the pushout construction. Its presentation definitions
were already relocated unchanged into PrelogLogificationData in the returned packet. The
unit-pushout presentation only needs these definitions; its old import unnecessarily points
back to their consumer. Redirect that single public import to the data module. This is the
entire change to this existing module: all declaration signatures, attributes, visibility,
proofs and non-theorem bodies stay byte-for-byte identical. No source-library module changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationComparison
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PrelogLogificationData
```

This keeps the seventeen relocated definitions publicly available. The comparison theorem
is no longer exported by the presentation. No direct importer refers to that theorem;
source-graph and declaration-use searches confirm this. Any future consumer needing that
theorem must import its module explicitly. No target or mathematical definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PrelogUnitPushoutPresentation | none recorded locally | Adapted exactly at the import shown above; zero holes, all declarations unchanged. |
| Sheaf.AlgebraicGeometry.PrelogPushoutLogAxiom | none recorded locally | Direct proof importer, needs only the presentation API. Compiled current source unchanged against the repaired presentation (9.5 s). |
| Sheaf.AlgebraicGeometry.EtaleLogPresentationComparison | none recorded locally | Direct public importer. Does not mention the removed comparison theorem. Compiled unchanged against the repaired presentation (7.5 s). |
| Sheaf.AlgebraicGeometry.PrelogLogificationEtaleConstruction | G9 (new in packet) | Transitive user through PrelogPushoutLogAxiom. Same construction proof; cycle removed. |
| Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationComparison | G9 | Transitive user of the construction; original signature preserved. |

The actual sandbox-overlaid current source graph has no cycle in the assigned item's
415-module import closure. Both direct importers passed compilation from source in the same sandbox;
their unchanged temporary copies were removed after testing. No current direct consumer
requires an adaptation. This record complements prelog-logification-data-relocation.md.

## Status

landed 20261026T104432-L-819761 2026-10-26 (merge of deliver/G9/Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationComparison)
