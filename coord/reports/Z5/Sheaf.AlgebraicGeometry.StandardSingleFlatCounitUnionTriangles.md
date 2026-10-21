## What changed

Restored `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles` from
its rework quarantine. Replaced its two private Sheaf proof imports with
`WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit` and
`WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`.
The current source counit theorem requires `IsKFlatTensor`, which the current
source bounded-flat theorem supplies. All declaration signatures, proof bodies,
docstrings and public imports remain identical to the archive.

The change record is
`coord/changes/Z5-standard-single-union-triangles-upstream-proof-imports.md`.
The DAG attachment and mathematical proof dependencies are unchanged.

## Proved and sorry left

This is a zero-hole rework repair. The archive and the restored module each have
zero `sorry`s. Holes closed: none (0 of 0). Holes added: none. Split off: none.
`AlgebraicGeometry.standardSingleFlatCounitUnionTriangles` retains its complete
proof from the existing presentation, flatness, counit and triangle declarations.
All five private helper theorems also retain complete proofs. No new declaration
or axiom is introduced.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit` (withdrawn empty module).
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` (its project K-flat
  predicate does not match the adopted counit API).

The corresponding source modules replace these providers; no mathematical
dependency is pruned. No module is withdrawn, no DAG node is removed, and the
quarantined parent `StandardSingleFlatCounitUnionEquation` still needs the item.
LeanFinder, Loogle and grep confirm Mathlib's short-exact distinguished-triangle
API already used by the proof; no shorter geometric theorem was found.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned rework restoration with zero existing holes. Its archive
fails to compile because the Sheaf counit provider was withdrawn and the source
K-flat API changed. The first compile reproduced the unknown-identifier error
at line 75. This packet repairs the actual imports rather than delivering an
unchanged archive.

The bounded-flat node's current `lean.note` describes the adopted source API,
but its `lean.module` and displayed statement still name the project provider
and `IsAcyclicTensorKFlat`. The proof uses the existing source theorem with the
same mathematical bounded-flat statement and the required `IsKFlatTensor`
predicate. No new intermediate theory, statement change or unit-route change
is needed. The existing triangle transport proves the connecting square using
`DerivedCategory.triangleOfSES.map`, including empty or repeated opens.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
