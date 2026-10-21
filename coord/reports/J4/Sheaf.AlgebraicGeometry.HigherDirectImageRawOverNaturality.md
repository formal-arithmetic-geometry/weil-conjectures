## What changed

Completed the explicit stage-3 retirement of
Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality listed in coord/queue.tsv
and coord/retire-items.tsv. The current file is a declaration-free public re-export
of its canonical upstream module. deleted.txt withdraws that redundant shim.

Updated only lean.note in the three existing nodes
sbc-lem-higher-image-raw-over-comparison,
sbc-lem-higher-image-raw-over-restriction and
sbc-lem-higher-image-raw-over-naturality to document retirement. Their upstream
attachments, statements, proofs and mathematical dependencies are preserved.

Change record: coord/changes/J4-retire-raw-over-naturality-shim.md.

## Proved and sorry left

This is a zero-hole retirement repair: the assigned module has no declarations
and zero sorry before retirement. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in a delivered Lean declaration and no new theorem is introduced.

The existing canonical upstream theorems
AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_comparison,
AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_restriction and
AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_toSheaf already have complete
proof bodies and are preserved. This delivery claims no new proof of them.

A scratch module importing only the canonical upstream module compiled through
lcompile.py in 4.1 seconds. It checked all three signatures and printed the axioms
of all three theorems: each uses only propext, Classical.choice and Quot.sound,
with no sorryAx. The scratch file is not part of the delivery.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality.
Its redundant public re-export of
WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality is removed
by retirement of the shim. No mathematical node or upstream proof dependency is pruned.
In particular the comparison and restriction components, the triangle restriction,
the raw transition-to-Hom theorem and coefficient compatibility remain needed.

Current lean/ and quarantine/ sources have no imports of this shim.
Both downstream.py queries report zero downstream modules. The historical six
consumer paths from the retirement inventory have already migrated to canonical
upstream modules or are themselves re-export shims. All live DAG parent dependencies
continue to name nodes attached to the canonical upstream declarations.
No quarantined source or dependency is withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished proof and previous splits, but
the assigned current queue row is `retire`. D2's reviewed 2026-10-20 canonicalization
already moved all declarations and all three Lean attachments upstream. Thus the
current assignment has zero local proof holes; inventing another proof or replacing
a proved upstream declaration would be unnecessary. The retirement inventory's six
consumer paths are historical: there are currently zero actual shim importers.
The explicit retirement request agrees with the current source and DAG.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
