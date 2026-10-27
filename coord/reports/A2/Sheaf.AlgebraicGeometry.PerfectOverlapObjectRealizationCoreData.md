## What changed

Repaired the returned packet against the current library. The earlier A2
CoreOfData delivery already landed CoreData and the canonical-family node
attachments at landing 20261022T025311-L-1269528. Preserve those changes rather
than overwriting them from the retained pre-landing node copies.

The returned caller Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization is
currently absent from both the shared checkout and the project server. Its
current coord/rework.tsv row preserves it at
quarantine/Sheaf/AlgebraicGeometry/PerfectOverlapObjectRealization.lean. Restore
that complete source, redirecting its single obsolete public import from
Sheaf.AlgebraicGeometry.PerfectHomTransport to
WeilConjectures.AlgebraicGeometry.PerfectHomTransport. All caller declarations,
signatures, definition bodies and proofs remain identical to that source. This
repairs the caller's unavailable public perfectLimitMap name; it is not an empty
restoration or a rebase-only packet.

In the assigned CoreData theorem, eliminate the proved Nonempty core directly
into the required Nonempty dependent pair instead of invoking Classical.choice.
The explicitly constructed canonical family and its reflexive compatibility
proof remain the same. Update only the final packaging proof step and proof
origin in the current main node. The obsolete pointwise/family attachment edits from the earlier
packet are already landed and are not submitted again. Refresh the existing
caller node's Lean note to accompany its restored module; preserve its statement,
proof, dependencies and declaration attachment.

Change record: coord/changes/A2-perfect-overlap-core-data-restoration.md.

The current original caller fails at line 64 with Unknown identifier
perfectLimitMap; Lean explicitly requests the adopted public import above.
The one-line import correction is the only caller source difference.
The final two-file lcompile.py check passes: CoreData in 46.9 seconds and its
caller in 1.9 seconds. Both files have no literal holes or overlong lines.

## Proved and sorry left

The assigned module starts with zero literal holes. Its theorem
AlgebraicGeometry.perfect_overlap_object_realization_core_data remains completely
proved with the same signature. The restored caller's theorem
AlgebraicGeometry.perfect_overlap_object_realization and its private helpers also
have complete proofs.

Closed holes: none (0 of 0). Added holes: none. Remaining holes in either delivered
module: none. Split-offs: 0. No definition or data is taken from an unfinished
existence theorem. Both original and delivered caller sources have zero holes.

## No longer needed

No further imports, declarations or modules are pruned. The caller's retired
Sheaf PerfectHomTransport import is replaced with the adopted source API.
The earlier removal of three unused CoreData proof imports and the corrected
pointwise/family node attachments are already part of the current library.

CoreData still uses the explicit canonical-family constructor and the proved
core assembly theorem; it does not choose an arbitrary family from the family
existence theorem. The canonical constructor's mathematical dependencies and
the unit route are preserved. The superseded pointwise/family node copies removed from the sandbox are not
repository deletions: their current library nodes are retained. The restored
caller keeps its own existing DAG node and declaration attachment.

## Where the brief, the DAG or earlier work was wrong

The return at delivery head 4b30b5c01e2 concerns a caller created on sheaf-dag
after the old delivery base 5d0e6bc63. Re-read the current source and rework row:
the caller is again quarantined, while CoreData has already landed through the
separate CoreOfData packet. This delivery repairs the preserved current caller
source and retains the newer landed item and node metadata.

The K1 independently twisted transport counterexample is already excluded by
the current CoreOfData proposition's equality to the canonical family. The
assigned theorem supplies that family and proves the equality by rfl. No new
hypothesis or statement change is needed, and no disputed marker remains.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
