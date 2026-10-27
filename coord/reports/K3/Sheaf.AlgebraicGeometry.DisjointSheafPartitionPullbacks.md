## What changed

Proved `AlgebraicGeometry.Scheme.FppfPartition.disjoint_sheaf_partition_pullbacks`
without changing its signature or any existing definition. Nine proved private helpers
implement the existing six-step argument: the fppf sheaf axiom on open covers and empty
schemes, gluing, restriction, pointwise image containment, partition uniqueness, and
factorization through an open summand. The pullback assertion uses Mathlib's pointwise
pullback criterion for functors and its explicit criterion in Type.

Added proof-only imports of
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` and
`Mathlib.CategoryTheory.Limits.Types.Pullbacks`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.FppfPartition.disjoint_sheaf_partition_pullbacks`
(node `lem-trf-disjoint-sheaf-partition-pullbacks`).
There are zero remaining holes and zero added holes; no split-off statements.
The module compiles through lcompile.py. The theorem signature was compared verbatim
against the shared source. All new helpers are private and fully proved.

## No longer needed

Removed the unused proof import `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
Mathlib already supplies Flat and LocallyOfFinitePresentation instances for open
immersions through the existing fppf imports. No nodes or modules are withdrawn.
All existing public imports are retained. The original DAG argument and dependencies
are retained; there is no departure from the unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The uniqueness argument can reuse pointwise
image containment instead of separately constructing both intersection comparisons.
The empty-index and empty-piece cases are covered by the same sheaf-axiom proof,
without choosing an index or assuming any piece is inhabited.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
