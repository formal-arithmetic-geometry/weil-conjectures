## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphismEvaluation.lean
byte for byte from the archive specified by coord/rework.tsv. This restores the
actual complete implementation of
AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism_evaluation after the
2026-10-20 cluster-restore rollback. The archived file remains intact.

The proof uses the existing, proved
AlgebraicGeometry.Scheme.picardAdjunctionSectionEvaluation and the Mathlib
structure-sheaf transpose formula, then cancels the inverse comparison and the
adjunction Hom equivalence. The resulting evaluation is exactly the section-map
definition. No declaration signature, definition, import or unit route changes.
The node receives only a Lean restoration note.

The restored module compiled in 11.9 seconds without warnings or errors. A scan
including quarantined sources identifies the unchanged direct consumer
Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction and 15 total
consumers; the change record inventories them. A separate public-interface scratch consumer compiles in 2.9 seconds and
rewrites by the restored theorem as its archived parent does. The theorem
uses exactly propext, Classical.choice and Quot.sound, with no sorryAx. The
consumer check recompiled the restored module in 10.7 seconds. The full
quarantined parent is not part of this delivery or its compilation check.

Change record:
coord/changes/F1-picard-direct-image-unit-morphism-evaluation-restoration.md.

## Proved and sorry left

Assigned rework restoration: zero existing holes, zero holes closed, zero holes
added, zero holes remaining, zero split off.
AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism_evaluation already has a
complete proof in the archive and is restored with that complete proof. Its node
is lem-sc-picard-direct-image-unit-morphism-evaluation. This delivery claims a
restoration, not a new proof or decomposition.

## No longer needed

None. No import, node or module is pruned. Both imports are required: the public
unit-morphism module supplies the statement and construction; the private
adjunction-evaluation module supplies the proof lemma. Both declared proof
dependencies are used. The parent restriction node and its archived proof still
need this evaluation theorem. The unit route and all dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open hole, but this particular assignment
is a quarantined rework restoration with zero holes. Its absence from lean/ is
the recorded cluster-restore rollback, not evidence that the theorem is unused.
The existing declaration, proof and DAG route agree. There is no statement dispute
or mathematical correction, and no current return entry for this item was found
in coord/returns/F1.md.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
