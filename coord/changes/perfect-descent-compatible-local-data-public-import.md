# AlgebraicGeometry.perfect_descent_compatible_local_data

## Reason

Restore the quarantined module recorded in `coord/rework.tsv`. Its statement uses
`AlgebraicGeometry.PerfectDescentOnOpen`, whose authoritative definition moved to
`WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen`. The old Sheaf module is
now an empty withdrawn module. The source definition was available only through
a private proof import, so the archived public theorem failed to elaborate.

## Old

```lean
public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen
```

The theorem's signature, proof, attributes and docstring are identical to the
quarantined version. No definition or target meaning changes. The two proof
dependencies and the node's Lean attachment remain necessary and unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData
--allow-missing --uses AlgebraicGeometry.perfect_descent_compatible_local_data`
reports zero current library importers. A separate search of quarantined sources
finds the following consumer, which must remain attached to the DAG.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | E2 (assigned) | Restored with the correct public statement import; compiles cleanly. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed in local claim records; quarantined rework | Uses the same theorem signature. Its archived source also has its own stale PerfectDescentOnOpen import; correcting that import for a temporary consumer check verifies compatibility. No consumer adaptation is delivered. |

## Status

landed 20261024T014518-L-2209102 2026-10-24 (merge of deliver/E2/Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData)
