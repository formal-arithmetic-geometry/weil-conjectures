# AlgebraicGeometry.perfect_hom_open_restricted_maps_exists

## Reason

Restore the complete quarantined module listed in coord/rework.tsv. Its archived
private import of the retired Sheaf transport-square module no longer supplies
the theorem perfect_hom_open_transport_square. Before retirement, that dependency
also loaded a duplicate derivedPullback declaration, the recorded quarantine
failure. The same transport-square theorem is proved in the adopted source module
WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare, which is also the
current Lean attachment of lem-pc-perfect-hom-open-transport-square.

Only that private proof import changes. The public import, both declaration
signatures, complete proof bodies and all definitions used by the theorem are
identical to the quarantined source. No source-library file changes. No target
statement or meaning changes, and no semantic target review is reopened.

## Old

```lean
import Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare
```

The rest of quarantine/Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictedMaps.lean
is restored verbatim at its original lean/ path.

## Users

The live-only downstream.py command reports the module unknown because it is
quarantined. A source scan of lean/Sheaf, lean/WeilConjectures and
quarantine/Sheaf finds the direct archived consumer below; its archived consumer
is included as well. There are no live importers. Both archived consumers were
compiled unchanged against the repaired module with lcompile.py in a separate
consumer-check sandbox. The three files compiled in import order, each within
five seconds. These consumer copies are validation material, outside the
delivery's lean/ directory; they are not restored by this delivery. Neither
consumer has an active claim in the inspected coordination snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | Y2 | Restored with its proof import redirected; theorem unchanged. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore | unclaimed; quarantined | Direct consumer compiles unchanged against restoration. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists | unclaimed; quarantined | Indirect consumer compiles unchanged against restoration and the archived Core. |

No forced adaptations are included. The node retains its Lean attachment,
statement dependencies, proof steps, proof dependencies and unit route; its
proof-origin note records the import repair. Independent delivery review can
compare the restored theorem and proof against the quarantine archive.

## Status

landed 20261020T174926-L-822446 2026-10-20 (merge of deliver/Y2/Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps)
