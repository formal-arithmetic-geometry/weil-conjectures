## What changed

Restored Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin from the archive
specified by coord/rework.tsv. Removed only derivedPullback from its local
irreducibility attribute, since the adopted definition is globally irreducible.
The archived version fails on that command; the repaired file compiles without
warnings in 9.0 seconds. Its complete theorem and private pasting proof are retained,
with all imports, declaration signatures and visibility unchanged.

Change record: coord/changes/G4-perfect-overlap-composite-object-pin-restoration.md.

## Proved and sorry left

This assigned repair starts with zero holes, closes zero holes and adds zero holes.
There are no sorries left in the delivered module. Both
AlgebraicGeometry.perfect_overlap_composite_object_pin and its private
object_pin_pasting helper retain their complete proofs. The theorem applies the
site component and projection component and pastes their equations on each Boolean
branch, exactly as the existing DAG plan states.

## No longer needed

None. Both private proof imports are used directly; the public statement import is
retained. No nodes, modules, declarations or dependency edges are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined build repair, not a remaining sorry. The archived local
attribute predates the adopted irreducible_def implementation of derivedPullback.
The current compiler rejects the redundant local status assignment. Restoring the
archive with this one entry removed repairs that failure without changing the
mathematics. The DAG statement, attachment, proof dependencies and unit route agree
with the retained proof and require no edits. The only archived consumer is
PerfectOverlapObjectRealizationCoreOfData; its theorem application is unchanged.

The unchanged archived consumer was also tested against the repaired module.
It stops at import line 6, before any theorem application, because its stale
Sheaf.PerfectOverlapObjectRealizationCoreBase import conflicts with the adopted
WeilConjectures version (duplicate perfectOverlapObjectRealizationCoreStatement
proof declaration). That consumer is separately quarantined and is not delivered
or modified here. This failure is independent of the local attribute repair.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
