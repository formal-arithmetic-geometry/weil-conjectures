## What changed

Restored `Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent` from its
quarantine archive. Replaced the withdrawn public
`Sheaf.AlgebraicGeometry.DerivedPullback` import with
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, and the withdrawn private
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` import with
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`.
Every other byte, including the complete theorem signature and proof, is unchanged.
Change record: `coord/changes/FilteredCartesianPerfectDescent-adopted-imports.md`.
The proof already realizes the node's four steps; no DAG changes are needed.
A server compile of the unmodified archive reproduces the unknown-identifier
errors for `derivedPullback` and `exists_derivedPullbackComposition` in 3.0 seconds.
The repaired module compiles successfully through `lcompile.py` in 9.3 seconds,
with no compiler diagnostics or warnings.

## Proved and sorry left

The restored theorem `AlgebraicGeometry.filtered_cartesian_perfect_descent`
(node `lem-pc-filtered-cartesian-perfect-descent`) has a complete proof from its
existing dependencies. The archive contained zero holes; this is a restoration
and import repair, not a new hole closure. Holes closed: none (0 of 0).
Holes added: none. Sorries left in the item or added elsewhere: none.
No result is split off.

## No longer needed

The withdrawn empty modules `Sheaf.AlgebraicGeometry.DerivedPullback` and
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` are replaced by their adopted
source modules. No mathematical node or proof dependency is pruned; all four
listed dependencies are used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole repair. Its absence from `lean/` did not mean
withdrawal. The archived imports had become stale after adoption of the source
APIs; the DAG already records the correct adopted declarations. The quarantined
`NoetherianApproximationData` remains a consumer both in Lean and in the DAG.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
