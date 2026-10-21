## What changed

Retired the listed duplicate
Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract through
deleted.txt and attached lem-pc-localized-tensor-comparison-closure-retracts to
the already proved upstream theorem
ModuleCat.localizedTensorComparisonProperty_closure_retracts in
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetract.
The upstream signature omits only the former unused C-flatness hypothesis.
A scratch proof establishes the exact former statement from it. No upstream
module or consumer is edited. The change record is
coord/changes/J2-retire-localized-tensor-comparison-closure-retract.md.

The original module, the former-signature compatibility proof and the unchanged
source closure consumer were checked with lcompile.py. The upstream retract
theorem and compatibility proof use only propext, Classical.choice and
Quot.sound. The existing parent DAG dependencies and unit route remain intact.

## Proved and sorry left

This is a zero-hole retirement repair. Before: 0 direct sorry holes in
ModuleCat.localizedTensorComparisonProperty_closure_retracts. After: 0;
0 holes closed and 0 added, with 0 split off. The retained upstream theorem
is already fully proved with only the three permitted axioms. There are no
remaining sorry declarations in this delivery. This is pruning of a duplicate,
not a newly claimed proof or a decomposition.

## No longer needed

Pruned Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract only.
Its imports of WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty,
Mathlib.RingTheory.Flat.Basic and the proof-only upstream retract-core module
leave the withdrawn duplicate. The corresponding source modules remain needed
by the preserved source theorem and consumer; none is withdrawn or changed.
No DAG node or dependency is deleted, and no further module is claimed pruned.

There are no live or quarantined Lean importers to adapt. In particular the
parent closure theorem already imports the upstream retract module, and its
DAG edge continues to name the existing retract node under the new attachment.
The retract-core node's incoming statement reference is preserved as well.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a remaining obligation, but the current
module has zero direct holes and coord/retire-items.tsv explicitly lists it
as a duplicate retirement. The source theorem and core are already fully
proved; no fifth split is needed. The retirement table's old Sheaf closure
consumer is already absent and its node has migrated to the source consumer.
The old node attachment still named the duplicate with the unused flatness
hypothesis; this delivery corrects that attachment without changing its
mathematical statement, proof plan, dependencies, or the unit route.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
