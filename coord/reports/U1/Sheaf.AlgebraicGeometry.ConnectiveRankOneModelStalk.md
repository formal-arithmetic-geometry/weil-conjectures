## What changed

Restored `Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk` from its current
quarantine archive. Replaced its empty withdrawn public import
`Sheaf.AlgebraicGeometry.DerivedPullback` by
`WeilConjectures.AlgebraicGeometry.DerivedPullback`.

Preserved the public theorem and all three private helpers, including
`strictlyPerfect_single_restricted_unit`, which the quarantined
`PerfectDegreeZeroFibreCriterion` imports with `import all`. Made the mapped
isomorphism and epimorphism evidence explicit to avoid typeclass timeouts without
increasing any limits. The existing maxHeartbeats setting is unchanged.

The DAG retains the same statement, attachment and three proof dependencies.
Only its proof-origin repair note is updated. Change record:
`coord/changes/U1-connective-rank-one-model-stalk-canonical-pullback.md`.

## Proved and sorry left

This is a zero-hole restoration and import repair, not new sorry-ledger progress.
The archive already had zero textual holes. Holes closed: none (0 of 0).
Holes added: none. Sorries left in every delivered module: none.

The complete proof of
`AlgebraicGeometry.surjective_stalk_homology_of_connective_rank_one_model`
and its three private helpers is retained and compiles. No result is split off.
The final delivery probe checks every restored declaration for nonstandard axioms.

## No longer needed

The withdrawn import `Sheaf.AlgebraicGeometry.DerivedPullback` is replaced by its
canonical adopted source module. This is import migration, not mathematical
pruning. No DAG node, dependency, consumer, or other module is pruned.
All three declared dependencies remain used: affine chain representatives,
the residue component isomorphism, and localized homology-stalk comparison.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from live `lean/` but preserved in quarantine by
the current rework row. Its complete source must be restored, not withdrawn.
Its archived derived-pullback public import no longer exports the declaration
used in its signature. No mathematical statement or proof-plan error was found.

The current residue-component source compiles, but the initial published artifact
still imported the pre-migration `Sheaf.AlgebraicGeometry.PerfectComplex`, causing
an import collision with the adopted `WeilConjectures` declaration. No change to
that dependency is part of this delivery.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
