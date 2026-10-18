## What changed
Added the adjacent-degree intermediate theorem and reduced the original theorem to it plus the complex-shape zero cases. Removed the unused TensorProductOfUniverses import.

## Proved and sorry left
The nonadjacent branch of `ringHomExtension_differential` is proved from `ComplexShape.up` and the parent theorem is reduced to `ringHomExtension_differential_adjacent`. The adjacent theorem remains one named `sorry` because its pure-tensor calculation exceeds the available compile window in this session.

## No longer needed
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses` is no longer imported. No other stated dependencies were used.

## Where the brief, the DAG or earlier work was wrong
The DAG plan omits a separately named adjacent-degree calculation; it is strictly smaller than the full all-degree theorem and is recorded as a new node.

## New nodes
`lem-pc-ring-hom-extension-differential-adjacent` records the remaining adjacent-degree calculation.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
