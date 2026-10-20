## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus` and
kept its theorem statement unchanged. The proof constructs the source-open restriction
comparison for derived homology, establishes restriction stability and source locality of
finite locally free rank, then applies the existing local matrix charts and the upstream
generic closed-locus gluing theorem. Because the Sheaf bridge modules for derived pullback
composition and open-pullback homology were withdrawn during the sync, the proof imports
their unchanged declarations from `WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`
and `WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology`.

## Proved and sorry left

Closed the module's original theorem hole:
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixClosedLocus`.
The module has no remaining `sorry` declarations and adds no new holes.

## No longer needed

No proof dependency or public import was removed. The restored proof uses the existing
`PerfectLowestMatrixCharts` module and the upstream
`AlgebraicGeometry.Scheme.exists_closedLocus_of_local_charts`; no new node or module is
introduced.

## Where the brief, the DAG or earlier work was wrong

The module was quarantined by the upstream-sync rework after the prior delivery. Its
proof remains valid against the current source tree, but its former proof-only imports
named withdrawn Sheaf bridge modules. Those imports had to point to the corresponding
adopted `WeilConjectures` modules so the restored module compiles. No statement, unit
route, or DAG dependency is changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
