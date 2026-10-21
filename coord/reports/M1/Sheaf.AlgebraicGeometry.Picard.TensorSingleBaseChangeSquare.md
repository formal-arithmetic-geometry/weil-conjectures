## What changed

Restored Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare from the
quarantine path in coord/rework.tsv. Repaired the conclusion's name resolution
by specifying AlgebraicGeometry.derivedPullback.{u, w} and the corresponding
canonical direct-image and derived direct-image universe arguments. The whole
existing proof is preserved: derive direct-image naturality, apply the ordinary
single-base-change comparison, and cancel only tensor-to-ordinary isomorphisms.
The existing node's Lean statement now matches the restored source verbatim.
Change record: coord/changes/M1-tensor-single-base-change-restoration.md.

The restored module compiles in 36.3 seconds without errors or warnings. A
separate #print axioms check of tensorSingleBaseChangeSquare reports exactly
propext, Classical.choice and Quot.sound. Searches via LeanFinder, Loogle and
Mathlib grep, plus rg in both library roots, found the existing ordinary
comparison as the shortest applicable route; no replacement theorem was needed.

## Proved and sorry left

AlgebraicGeometry.Scheme.Modules.tensorSingleBaseChangeSquare has a complete
proof. This is a zero-hole restoration repair: 0 original sorries, 0 closed,
0 added, 0 left, and 0 split off. Its node is
lem-sc-picard-tensor-single-base-change-square. No new declaration or hole is
introduced. The proof retains the arbitrary module and commutative square,
without flatness or invertibility assumptions.

## No longer needed

None. All original public imports are used by the statement; the private import
of Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison supplies the
ordinary comparison used in the proof. All existing proof dependencies and the
quarantined TensorDegreeZeroMateSquare parent's dependency on this item remain.
No node, library module or unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The rework item has zero sorries already; it needs restoration and interface
repair rather than a new decomposition. The archived unqualified derivedPullback
now resolves to the wrong functor after upstream added Scheme.Modules.derivedPullback.
Qualifying the original pinned functor recovers the node's intended arbitrary-w
statement. The ordinary comparison dependency had also been restored with this
qualification. Its current source was compiled unchanged as a sandbox dependency
for validation; it is not modified or included in this delivery.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
