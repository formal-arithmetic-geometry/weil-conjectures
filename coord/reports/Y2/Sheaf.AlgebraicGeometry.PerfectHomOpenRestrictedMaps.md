## What changed

Restored lean/Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictedMaps.lean from the
archive named in coord/rework.tsv. Replaced the private import
Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare by
WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare. This reuses the
current adopted theorem perfect_hom_open_transport_square and avoids the retired
duplicate dependency. The restored file otherwise matches the archive verbatim:
its public import, theorem statement and complete proof are unchanged.

The existing node new-perfect-hom-open-restricted-maps retains its attachment and
all dependency edges. Only its proof-origin note records this restoration.
Change record: coord/changes/Y2-perfect-hom-open-restricted-maps-import-repair.md.

Validation: the repaired module compiled alone (4.2 seconds). In an isolated
consumer-check directory, the same repaired module and unchanged archived
PerfectHomOpenRestrictedCore and PerfectHomOpenRestrictedDataExists compiled in
import order (4.5, 2.0 and 2.0 seconds). The import-direction check accepts the
new dependency. No consumer adaptation is needed or delivered.

## Proved and sorry left

This is the assigned zero-hole quarantine repair. The archive already has a
complete proof of AlgebraicGeometry.perfect_hom_open_restricted_maps_exists
(node new-perfect-hom-open-restricted-maps) and of its private helper
conjugated_map_natural. Both compile unchanged with the corrected import.

Original holes: 0. Holes closed: 0. Holes added: 0. Holes left in the item: 0.
No statements are split off and no definitions contain sorry. Existing
transitive dependencies are retained; no claim is made that all their proofs
are axiom-free merely because this module has no textual holes.

## No longer needed

Removed the private import of the retired duplicate
Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare. Its current source-library
replacement supplies the same required geometric theorem. No mathematical
proof-dependency node or unit step is pruned, and no declaration or module is
withdrawn. Every other explicit import supplies an interface or a theorem used
by the retained construction.

LeanFinder found only ordinary scheme pullback/restriction identities, not the
compatible derived Hom cocone construction. Loogle confirmed Iso.homCongr, which
the existing proof already uses. Searches of Mathlib and both project roots
confirmed the adopted transport-square theorem and no duplicate of this item.
The existing complete route therefore needs only the import correction.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an unfinished proof chain, but this assigned rework
item has zero sorry: it was quarantined after an upstream synchronization broke
its proof import. Its absence from lean/ is not a withdrawal. The current DAG
already points the transport-square dependency at the adopted source module;
the archived item's import had not followed that migration.

The live-only downstream script cannot inspect the missing module. Source scans
including quarantine identify the archived direct and indirect consumers, and
both pass unchanged compilation against this restoration. The complete original
proof, node attachment, source references and unit route are preserved.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
