## What changed

Proved `groupCohomology.resolution_inflation_comparison`, retaining its original
signature and docstring. Private helpers construct the restriction/precomposition
cochain map and the bar-resolution map on free generators, verify augmentation
and cochain formulas, and identify the canonical comparison using Mathlib's
`isoLeftDerivedObj_inv_naturality`.

`ModuleCat.augmented_lift_homotopy` compares the two augmented maps into the
restricted bar resolution. Restriction preserves exactness; projectivity is
needed only for the source. Applying linear Yoneda to the homotopy and passing
to homology completes the inflation square. The given cochain map has exactly
the required formula in every degree.

The inherited proof attempt was repaired by giving explicit arguments to
free-generator and homology-composition rewrites. This avoids expanding an
unrelated cochain map during rewrite matching. No file splitting, increased
time limit, or heartbeat override is used.

## Proved and sorry left

Closed 1 of 1 original holes:
`groupCohomology.resolution_inflation_comparison`
(node `lem-sfb-resolution-inflation-comparison`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The final single-file compile succeeded without warnings in 17.2 seconds. An explicit axiom
check reports only `propext`, `Classical.choice`, and `Quot.sound`. The delivery
dry run also checks compilation and the axioms of all added declarations.

## No longer needed

None. No imports, nodes, or modules are pruned. The existing declared dependencies
are used through Mathlib's bar resolution and canonical projective-resolution
comparison, and the project's augmented exact-target homotopy theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or DAG-plan error was found. The argument actually
works for every group homomorphism; the stated surjectivity hypothesis is retained
unchanged. The earlier sandbox attempt had unresolved elaboration bottlenecks,
which are fixed by explicit rewrite arguments. All work is in the item module;
no public interface, definition used by another module, or target was changed.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
