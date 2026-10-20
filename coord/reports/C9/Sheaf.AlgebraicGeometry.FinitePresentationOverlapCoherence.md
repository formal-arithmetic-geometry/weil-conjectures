## What changed

Retired Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence, explicitly
listed in coord/retire-items.tsv, by listing its path in deleted.txt. Reattached
lem-pc-fp-overlap-eventual-coherence to the existing upstream declaration
AlgebraicGeometry.exists_finitePresentation_overlap_eventual_coherence in
WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapCoherence.

The unchanged upstream local-overlap-models parent also compiles independently;
its printed axioms are the same three standard axioms.

The upstream signature differs only by omitting the unused Noetherian ring
instance. Its proof body is identical. The complete old statement compiles as a
scratch theorem proved by applying upstream. Printed axioms for the specialization
and upstream are exactly propext, Classical.choice, and Quot.sound.

tools/downstream.py reports zero downstream modules.
No consumer edit is needed: both library roots and quarantine have no imports
of the Sheaf module. The existing upstream local-overlap-models parent already
imports the upstream coherence module and applies its declaration. The DAG parent
keeps the same eventual-coherence dependency; the mathematical statement, proof
steps, proof dependencies, and unit route remain intact.

Change record: coord/changes/C9-retire-fp-overlap-coherence.md.

## Proved and sorry left

Zero holes initially; zero holes left. Holes closed: none. Holes added: none.
No split-off statements. This is duplicate retirement, not a new proof.
The existing upstream theorem is fully proved and its printed axioms are standard.

## No longer needed

Module Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence is retired.
Its duplicate private helper overlapLimitMap_stage_comp and duplicate theorem
body are removed with it. Its public imports LocalOverlapTransitions,
Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation, and
Mathlib.RingTheory.Noetherian.Basic, and its private imports
FinitePresentationOverlapChartEquations, OverlapComparisonRefinement, and
OverlapUniversalTestCoherence need no duplicate file to connect them.
The retained upstream module keeps all of these dependencies; no dependency node
or other module is pruned. No remaining consumer import needs changing.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof obligation, but the current item has zero
sorries and is explicitly listed for duplicate retirement. The node still pointed
to the duplicate Sheaf declaration after its parent had switched upstream.
The upstream signature omits an unused Noetherian hypothesis, so its complete
old-statement specialization was checked explicitly. The source Tag 01ZR first
proof and the unit sk-thm-picard-semicon route remain represented by the same
proved upstream argument. No mathematical error or new statement is asserted.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
