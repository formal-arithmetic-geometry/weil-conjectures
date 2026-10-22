## What changed

Restored Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData from the
quarantine path in coord/rework.tsv. Redirected its obsolete Sheaf CoreBase import to
WeilConjectures CoreBase to eliminate the duplicate declaration import error. Replaced
its retired empty Sheaf PerfectHomTransport import with the source
PerfectHomTransportExtension API. Every other byte matches the archive.

The complete canonical comparison construction, definition
AlgebraicGeometry.perfectOverlapCoreOfDataStatement, theorem
AlgebraicGeometry.perfect_overlap_object_realization_core_of_data, and all three DAG
proof dependencies are preserved. No node route, signature or definition body changes.
The repair record is coord/changes/A4-perfect-overlap-core-of-data-restoration.md.
The module compiles cleanly through lcompile.py in 21.0 seconds.

## Proved and sorry left

This assigned restoration repair has zero original holes. Closed: none. Added: none.
Remaining: none. AlgebraicGeometry.perfect_overlap_object_realization_core_of_data
retains its complete proof; this is an import repair, not a new proof or decomposition.
All private helpers are proved and all definitions are real constructions.

## No longer needed

Removed direct imports of Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
and the retired empty Sheaf.AlgebraicGeometry.PerfectHomTransport, replacing them with
the adopted source APIs above. No mathematical dependency, DAG node or module is
withdrawn or pruned. The archived parent still needs this item, so its absence from
live Lean importers is not interpreted as permission to withdraw it.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantined restoration, not an unfinished proof. Its archived
base import conflicts with the source base now imported by the restored comparison
and transport modules. The archived theorem and its canonicality hypothesis remain
valid and compile unchanged after the import repair.

Library and Mathlib search found generic pullback and isomorphism tools, with no
replacement for this prescribed canonical seven-field construction; the existing
complete argument is retained. No new nodes or hypotheses were introduced.

The archived CoreData consumer has its own prior source-sync mismatch: its conclusion
applies perfectOverlapObjectRealizationCoreStatement to an obsolete hstage argument.
This item's two restored public declarations keep their archived signatures. The
parent remains quarantined and is not modified by this delivery. An explicit axiom
probe of the restored theorem reports only propext, Classical.choice and Quot.sound.
The scratch check also verifies the original CoreData packaging proof after removing
only that obsolete conclusion application: it compiles cleanly in 18.3 seconds,
and both theorem probes report the three standard axioms. The scratch file is excluded
from the delivery. The assigned source still differs from the archive in two imports only.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
