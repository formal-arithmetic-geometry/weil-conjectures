## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleOpenStalkArrow.lean` from its
quarantined source and retained the complete proof of
`AlgebraicGeometry.standardSingle_open_stalk_arrow`. The proof constructs the
restriction stalk comparison as a natural linear isomorphism, applies the
proved derived open-arrow square, and transports it through degree-n homology.
The only upstream import spelling is the current
`WeilConjectures.Algebra.Homology.ModuleStalkFunctor` import. No declaration
signature or public statement changed.

## Proved and sorry left

The sole declaration in the item,
`AlgebraicGeometry.standardSingle_open_stalk_arrow` (node
`lem-pc-standard-single-open-stalk-arrow`), is proved. No `sorry` remains and
no new `sorry` is added.

## No longer needed

No imports are removed. The proof uses the existing
`StandardSingleOpenDerivedArrow`, `StandardSingleBaseChangeMap`, module stalk
functor, and exact-functor homology comparison imports. No DAG nodes or modules
are pruned.

## Where the brief, the DAG or earlier work was wrong

The live source had been quarantined by the upstream-sync rework after the
previous landing was dropped; the quarantined file is a complete compiling
proof. The current source library exposes the module stalk functor under the
`WeilConjectures` namespace, so the quarantined import is retained as written.

## New nodes

None.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
