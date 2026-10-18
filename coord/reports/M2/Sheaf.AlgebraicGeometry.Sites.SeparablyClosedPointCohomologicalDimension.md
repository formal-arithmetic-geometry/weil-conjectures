## What changed

Proved `AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension_eq_zero_of_isSepClosed` in
`Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`. The proof unfolds the
`sInf` definition, applies `ENat.sInf_eq_zero`, and supplies the zero bound from
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`.
Added the proof-only import of `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`.
Removed the unused proof import of `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`.
Updated the existing node's proof, proof dependencies, and proof origin to record this route.
The module compiles cleanly with lcompile.py.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension_eq_zero_of_isSepClosed`
(node `lem-kun-cd-sep-closed-point`).

Holes left in the item: zero. Holes added: zero. Split-offs: zero.
The proof uses the existing declaration
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`
(node `lem-sf-separably-closed-torsion-cd`), whose proof is an accepted dependency.

## No longer needed

The old `lem-kun-03qu-sep-closed` proof dependency is not used directly: its stronger torsion
bound is supplied by the existing `lem-sf-separably-closed-torsion-cd` declaration. The former
`WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport` proof import is removed. No other nodes or
modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The imported plan expanded the zero-dimensional case into direct cohomology vanishing. The library
already states the required torsion bound in `lem-sf-separably-closed-torsion-cd`, and the current
`torsionEtaleCohomologicalDimension` definition exposes the equality through `ENat.sInf_eq_zero`,
so the direct reduction is sufficient. No statement or definition was changed.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
