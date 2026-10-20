## What changed

Completed the assigned retirement repair: withdrew the duplicate
Sheaf.RingTheory.KoszulRegularSequenceDualComplex in favor of the existing source module.
Migrated the sole live Lean importer, Sheaf.TraceFormula.AlgebraicShriekCalculus, by
changing its private import. Retargeted all three existing DAG lean attachments to the
source module. No source-library file, target, consumer signature or proof is changed.
See coord/changes/S2-koszul-dual-complex-upstream-retirement.md for the full comparison,
consumer inventory and quarantine-restoration note.

## Proved and sorry left

The assigned module has zero sorry holes before retirement and zero afterward.
Holes closed: none. Holes added: none. Split off: none. This is duplicate retirement,
not a new proof or a decomposition. Every existing public result remains available in
WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex. The sole existing hole in the adapted
consumer is AlgebraicGeometry.nonempty_algebraicShriekCalculus; it is untouched.
This delivery changes only its import.

## No longer needed

Pruned module: Sheaf.RingTheory.KoszulRegularSequenceDualComplex.
Removed private import of that module from Sheaf.TraceFormula.AlgebraicShriekCalculus;
replaced it with the source module's private import. No mathematical dependency nodes
are pruned, since the replacement uses the same argument and dependencies. All three
attached nodes, all their parents and the unit route remain in the DAG.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes; this assignment is actually
listed as retire in coord/retire-items.tsv and has zero current holes. The listing's
DIFFERENT classification arises solely from an unused regularity hypothesis on g in
change_generators. The source proves the same equality without that hypothesis; all
other public statements match. The retire row's five-consumer list is stale: current
Lean sources contain one importer, with another preserved in quarantine. The archived
FlatLCICanonicalAdjunction must migrate its private import when restored; its node and
archive are preserved, and no parent mathematics is discarded.

Short-route searches ran through msearch.py: leanfinder for canonical Koszul duality
returned regular-sequence tools, loogle for exteriorPower.pairingDual returned the
pairing API, and grep for change_generators returned no Mathlib match. Direct source
comparison found the full adopted proof and makes re-proving or splitting unnecessary.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
