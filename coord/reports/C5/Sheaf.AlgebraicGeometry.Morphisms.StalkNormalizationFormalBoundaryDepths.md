## What changed

Retired the duplicate module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths` using
`deleted.txt`. The adopted source module
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths`
already contains the complete theorem used by the upstream formal-splitting consumer. The DAG
node `lem-sbc-stalk-normalization-formal-boundary-depths` now records that canonical module and
its exact signature, which omits only the unused public `hs : s ∉ U` hypothesis. The change record is
`coord/changes/C5-retire-stalk-normalization-formal-boundary-depths.md`. No upstream file,
target statement, or surviving consumer is modified.

The direct project search and the existing source proof establish that this is the shortest route:
the complete upstream theorem is already present. msearch.py searches were run with LeanFinder,
Loogle, and grep; they found no Mathlib theorem that replaces this result.

## Proved and sorry left

This is a duplicate retirement. The assigned module had zero `sorry`s, and the canonical upstream
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths` is already fully
proved. Holes closed: 0. Holes added: 0. Holes split off: 0. No delivered Lean module retains a
`sorry`.

## No longer needed

The duplicate Sheaf module and its private helper `depth_le_of_flat_stalk` are no longer needed;
the module is listed in `deleted.txt`. No surviving module imported it, so no import line is
removed or adapted. The upstream theorem and all of its imports remain in use. No proof-dependency
node or unit step is pruned: the existing boundary-depth node is reattached to the canonical
upstream declaration, and the formal-splitting route still uses the same result.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a possible open proof, but the current assignment is explicitly
listed as a retirement. The Sheaf copy is already sorry-free, while the adopted source tree now
contains the complete theorem. Reproving it or adding intermediate statements would duplicate the
canonical declaration. The stale DAG Lean attachment pointed to the duplicate and included the
unused `hs` binder; this delivery corrects only that attachment while retaining the node's
mathematical statement and proof route.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
