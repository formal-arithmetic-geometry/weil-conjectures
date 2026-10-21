## What changed

Restored Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport from its
quarantine assignment as a public re-export of the already proved adopted
WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport theorem.
Preserved all three archived public imports. Replaced the private duplicate
Core and withdrawn RepresentativeData imports by the canonical transport
provider, avoiding both the missing theorem and duplicate declaration paths.
The historical module is functional, not an empty withdrawal. The quarantine
archive and every parent dependency remain intact. No adopted source file is
changed. Updated the item's node Lean attachment to the canonical provider;
its two proof dependencies, mathematical statement and unit route stay.

Change record: coord/changes/W6-open-restricted-comparison-reexport.md.

## Proved and sorry left

The archived item has zero holes. Closed: none (0 of 0). Added: none.
No sorry remains in the delivered item and no new theorem is split off.
AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport
is supplied by the existing complete upstream proof, whose construction combines
exists_open_restricted_representative_data with
exists_open_restricted_comparison_square.

Validation: the restored re-export compiles cleanly in 1.9 seconds. A probe
with exactly its public imports plus the unchanged upstream parent compiles
and proves the full archived signature by the adopted theorem, without changing
any argument. The two K-flat predicates are equal by rfl. The theorem prints
only propext, Classical.choice and Quot.sound as axioms. The redirected archived
proof also compiles in 8.2 seconds using the upstream RepresentativeData module.
Its mixed-import variant reproduces the duplicate-declaration error, while the
re-export signature probe loads both paths successfully. Scratch probes are
excluded from delivery.

## No longer needed

Removed the direct private imports
Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore and
Sheaf.AlgebraicGeometry.OpenRestrictedRepresentativeData from this historical
module. Their mathematical results are still used by the adopted source proof
through the canonical WeilConjectures modules. No mathematical dependency, DAG
node, parent or unit step is pruned. Neither Sheaf dependency is withdrawn by
this packet. The duplicate local implementation is replaced by the canonical
public re-export. No declarations are removed from WeilConjectures.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole quarantine repair, not an unfinished theorem: the archive
already contains a complete proof. Its RepresentativeData import points to a
withdrawn module. Its exact theorem now also exists upstream, using the
IsKFlatTensor spelling of the definitionally identical K-flat predicate. The
DAG item attachment was still the quarantined duplicate. Reattach it to the
actual upstream declaration and retain the historical module as a re-export.
No false statement or mathematical weakening was found.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
