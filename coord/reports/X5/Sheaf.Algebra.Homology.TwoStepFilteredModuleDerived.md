## What changed

Completed the two proofs in
`Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived`, with all existing declaration
signatures, definitions, visibility and imports unchanged.

`CochainComplex.twoStepGraded_homotopy` constructs the actual homotopies on the two
graded complexes. On the subcomplex, the specified factorizations give the
homotopy components; cancellation of the target inclusion proves their vanishing
and homotopy equations. On the quotient, evaluation preserves the cokernel, so
the total homotopy components descend degreewise. Cancellation of the source
cokernel projection proves the same equations. Naturality of the cokernel
projection identifies the endpoint maps. Mathlib's
`DerivedCategory.Q_map_eq_of_homotopy` gives the required derived equalities.

`CochainComplex.twoStepGraded_inverts` selects the chain representative already
present in the definition of a filtered quasi-isomorphism. The quotient lift's
map on this representative reduces to the ordinary derived image of its graded
map. Mathlib's `DerivedCategory.isIso_Q_map_iff_quasiIso` finishes.

The proofs implement the existing docstring argument and the node's existing
well-definedness clauses. No route change, new node or intermediate assumption
is required. Sources read: Stacks `trace.tex`, definition of the filtered derived
category in the section on filtered complexes, and the blueprint
`prop-trf-trace-formal-laws.proof.md`, clause (2).

## Proved and sorry left

Closed both original holes (node `def-trf-two-step-filtered-module-derived`):

- `CochainComplex.twoStepGraded_homotopy`.
- `CochainComplex.twoStepGraded_inverts`.

There are zero remaining `sorry`s in the item and zero holes added or split off.
No definitions or theorem statements were changed.

## No longer needed

None. No proof imports were added, and the existing public imports and statement
dependencies are unchanged. The proof does not introduce dependencies on the
filtered projective model or comparison modules, which are consumers of this
construction.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The node has no numbered proof steps, but
its statement and the two theorem docstrings specify exactly the restriction,
cokernel descent and quasi-isomorphism inversion arguments implemented here.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
