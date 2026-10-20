## What changed

Restored `Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange` from its
quarantine copy and repaired it for the synchronized upstream API. The proof
now imports `WeilConjectures.AlgebraicGeometry.DerivedPullback`,
`WeilConjectures.Algebra.Homology.KFlatResolution`, and
`WeilConjectures.Algebra.Homology.KFlatPullback`, avoiding the retired duplicate
Sheaf derived-pullback module. The K-flat predicate was updated from the retired
`IsAcyclicTensorKFlat` name to the live `IsKFlatTensor` name. The theorem
statement and mathematical proof are unchanged.

Validation: the restored K-flat stalk dependency and this module compile in
sandbox import order with `lcompile.py --all`; the module has no remaining
`sorry` declarations.

## Proved and sorry left

`AlgebraicGeometry.Scheme.derivedFiberCohomology_baseChange_iso` is proved.
Holes closed: 1 of 1. Holes added: 0. Holes left: 0.

## No longer needed

The duplicate Sheaf derived-pullback and withdrawn Sheaf K-flat-pullback
imports are no longer needed and were replaced by their live
`WeilConjectures` source modules. No mathematical dependency node is removed;
the existing proof dependencies remain represented in the DAG.

## Where the brief, the DAG or earlier work was wrong

The upstream synchronization retired/changed the APIs used by the quarantined
file: importing the Sheaf derived-pullback copy now conflicts with the adopted
`WeilConjectures` declaration, and `IsAcyclicTensorKFlat` was renamed to
`IsKFlatTensor`. The quarantine error only reported the missing compiled K-flat
stalk object; after compiling that dependency in sandbox order, these API
repairs were required for the module to compile. The target theorem statement is
unchanged.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
