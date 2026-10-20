## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectLowestMatrixCharts.lean` from its
quarantine copy. Replaced the proof-only import of the withdrawn duplicate
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` with the canonical
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`, which provides
the same `exists_derivedPullbackComposition` declaration. The theorem
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts` and its public
interface are unchanged. The restored module compiles cleanly.

## Proved and sorry left

The module's existing theorem was already fully proved and remains fully proved:
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts` (node
`lem-sc-perfect-lowest-matrix-charts`). This repair adds zero `sorry`s and
leaves zero `sorry`s in the item module.

## No longer needed

The withdrawn duplicate module `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
is no longer imported. No DAG proof dependency is removed: the canonical
upstream module supplies the same existing declaration, so the node's proof
route and dependencies remain unchanged. No other imports or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery retained a proof-only import from the Sheaf duplicate
module after that module was withdrawn during upstream synchronization. The
canonical source module `WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`
contains the required declaration and resolves the repair without changing the
statement or proof.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
