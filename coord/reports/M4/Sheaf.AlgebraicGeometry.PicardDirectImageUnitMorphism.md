## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphism.lean byte for
byte from the quarantine archive named in coord/rework.tsv. This supplies the full
explicit definition AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism at its
missing live-library path. The assigned defect is the cluster-restore rollback;
the archived construction itself needs no mathematical change. Its signature,
shared derived-category parameter, public import, options and canonical data are
preserved. Updated only the existing node's Lean restoration metadata.

The definition builds the canonical derived base-change comparison with its
coefficient identification, takes degree-zero homology, applies the direct-image
comparison, then transposes through the ordinary module adjunction and the
invertible pullback comparison on the structure sheaf. This is the node's explicit
construction, using the existing proved tensor-pullback adjunction rather than
newly selected data. Checked Stacks 08HY and 0D5S in cohomology.tex and the ordinary
adjunction 0096 in sheaves.tex, and retained the theorem-of-the-cube unit route.

The restored item compiled cleanly in 10.3 seconds. A separate sandbox consumer
check recompiled it in 9.6 seconds and compiled the unchanged archived theorem
AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism_evaluation in 12.0 seconds.
That proof unfolds the definition and recovers the fixed section map, checking the
specified adjoint transpose against the consumer that directly computes it.
Consumer-check copies are scratch files, not additional delivered modules.

Change record:
coord/changes/M4-picard-direct-image-unit-morphism-restoration.md.
It includes all 21 downstream modules found in the union of live and quarantined
sources, the three direct public importers and the four DAG consumers. Each keeps
its original statement and dependencies, with no forced adaptations.

## Proved and sorry left

This is a zero-hole definition restoration. The archived module contains zero
sorry declarations, and the restored module contains zero. Holes closed: none
(0 of 0). Holes added: none. Split-off statements: none. No hole is hidden inside
the definition. The restored declaration is
AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism, attached to
node def-sc-picard-direct-image-unit-morphism. The downstream evaluation theorem
was used only as a compilation check; its restoration is a separate assignment.

## No longer needed

None. No import, node, module, declaration or dependency is removed. In particular,
Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap remains its public import,
and all existing statement dependencies and DAG consumers remain attached.
Withdrawal would be wrong: unfinished quarantined parents still require the node.

Searched for a shorter route using the required msearch.py tools. Lean Finder for
an adjoint transpose of a degree-zero direct-image morphism returned eight hits,
including pullbackObjUnitToUnit, unitHomEquiv and the ordinary adjunction formulas.
Loogle for SheafOfModules.pullbackObjUnitToUnit returned six declarations, and
grep for pullbackPushforwardAdjunction|unitHomEquiv returned 25 ingredient hits.
These are the existing ingredients of the archived construction. Searches of both
library roots found no other implementation of the fixed unit morphism. Since the
assigned item is restoration of this definition, its specified canonical data and
its consumers' definitional computations are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief assumes a hole; this assignment instead repairs the
quarantined zero-hole module listed in coord/rework.tsv. Its absence from lean/
is caused by the recorded rollback and is not evidence that the mathematics was
withdrawn. There is no current item-specific M4 return requiring a different
construction. The current DAG statement and archived definition agree.

The local claim snapshots do not identify current remote holders of the other
quarantined rework modules. Their ownership is not inferred or changed; none is
adapted. No target statement, unit route or source-library declaration is changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
