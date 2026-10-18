## What changed

Filled the proof of `CategoryTheory.Functor.preserves_sequentialHomotopyColimit`
in `Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit`, without
changing its signature, documentation, or imports. The proof follows all five
steps of `lem-kun-functor-preserves-hocolim`: use the coproduct comparison
isomorphism, check the successor square on coprojections, subtract it from the
identity square using additivity, apply TR3, and apply two-out-of-three to every
completion. Finally transport the distinguished image triangle using the
coproduct comparison on its first two objects and the identity on its third.
The last arrow explicitly includes the specified shift comparison and the
inverse of the shifted coproduct comparison.

Mathlib supplies the stated dependency declarations directly:
`Limits.instIsIsoSigmaComparison`, `Functor.map_distinguished`,
`Pretriangulated.complete_distinguished_triangle_morphism`,
`Pretriangulated.isIso₃_of_isIso₁₂`, and
`Pretriangulated.isomorphic_distinguished`. The coprojection calculation is
proved in the module using `Sigma.hom_ext` and the coproduct equations.
No new declarations, definitions, nodes, or change records are needed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.preserves_sequentialHomotopyColimit`
(node `lem-kun-functor-preserves-hocolim`). All four conjuncts are proved.
Holes closed: 1. Holes added: 0. Split off: 0. Sorries left: none.

## No longer needed

None. All existing imports are needed by the statement or proof. All four
planned dependency nodes remain used: `def-kun-truncations`,
`def-weil-triangulated-category`, `def-weil-pbc-category-colimit`, and
`lem-sf-triangle-morphism-iso`. There is no change to the unit route or DAG plan.
The LeanFinder, Loogle, and grep searches found the constituent Mathlib facts,
with no whole-item replacement.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The existing statement correctly
quantifies over triangle completions without claiming uniqueness, as required
by Stacks Tags 090Z and 014A. The proof preserves the exact stated shift maps.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
