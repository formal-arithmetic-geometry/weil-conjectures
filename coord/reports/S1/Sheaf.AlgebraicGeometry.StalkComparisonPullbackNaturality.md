## What changed

Replace the local duplicate implementation in
Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality by a public re-export
of WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality. Keep the
public Sheaf.Algebra.Homology.KFlat import so existing consumers can use the
original IsAcyclicTensorKFlat predicate spelling. The imported canonical theorem
uses the definitionally equal IsKFlatTensor predicate and the identical map.

The current file compiles alone but fails when its upstream twin is imported:
both declare comparisonIntoPullback_naturality. The new module fixes that exact
collision and keeps the historical import path usable. Reattach only the item's
DAG node to the proved upstream declaration and align its proof description with
the upstream implementation. All three mathematical proof dependencies and all
statement and unit-route fields remain unchanged. No upstream file is edited.

Change record: coord/changes/S1-stalk-pullback-upstream-reexport.md.

## Proved and sorry left

Zero-hole repair: 0 of 0 original holes closed, 0 holes added, 0 split off.
No declaration is left with sorry. Both
AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback and
AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality
are supplied by the existing complete upstream implementation. This delivery
does not count their prior proofs as newly closed holes.

The final shim compiles. A consumer probe repeats the entire original theorem
signature, including IsAcyclicTensorKFlat, and applies the canonical theorem
with unchanged arguments. A second probe checks equality of the entire old
map expression with the canonical definition by rfl. Both public declarations
print exactly propext, Classical.choice and Quot.sound as axioms.
A combined-import probe now compiles whereas the original module fails with
a duplicate-name import error. A further probe imports three current upstream
consumers alongside the shim successfully. Delivery preflight checks the packet.

## No longer needed

The local duplicate definition comparisonIntoPullback, duplicate theorem
comparisonIntoPullback_naturality, and private canonical_kflat,
conjugate_naturality and paste_naturality helpers are no longer needed; the same
public names are provided by the canonical upstream implementation. Remove the
direct public StalkComparisonSourceTransport import and private
StalkDerivedExtensionComparison import; these remain dependencies through the
canonical module. Keep the public KFlat import for source compatibility.
No mathematical node or proof dependency is pruned. No module is withdrawn,
no quarantined file is deleted, and no reduction of the global target import
closure is claimed. The ten archived consumers and their parent nodes remain.

## Where the brief, the DAG or earlier work was wrong

The rework row describes an import failure predating the already landed V4 and
P9 repairs. The assigned current module has zero holes, not a theorem awaiting
proof. The remaining concrete defect is coexistence of two modules declaring
the same names. The source theorem differs textually only in the K-flat
predicate name, whose defining formula is identical. Re-exporting the existing
proof removes the collision without weakening the statement or handing on any
obligation. The item's node was still attached to the duplicate implementation;
its attachment now records the canonical implementation and compatibility check.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
