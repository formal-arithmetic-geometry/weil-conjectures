## What changed

Filled `WeilConjectures.FixProjectionCompactification.finiteCompactificationProjection` without
changing its statement or public imports. The proof unfolds the positive level, obtains the
refinement-law family from `ProjectionRefinementDescent.finite_descent`, and applies the new
intermediate assembly theorem. The item has no textual `sorry`.

Added proof-only import `Sheaf.Paper.FiniteProjectionFromDescent`. No existing module or public
definition was changed. The archived quarantined source was restored into the item sandbox with
its original declaration and target signature.

## Proved and sorry left

Closed 1 of 1 item holes:
`WeilConjectures.FixProjectionCompactification.finiteCompactificationProjection`.

Added 1 split hole:
`WeilConjectures.FixProjectionCompactification.finiteProjectionFromDescent` in
`Sheaf.Paper.FiniteProjectionFromDescent`. It is a strictly smaller assembly statement: it
assumes the refinement-law clause for every compactification and returns the positive-level
`finiteLaw`; the parent only supplies that clause from `finite_descent`. Its docstring records
the blueprint source and the categorical cancellation proof required.

## No longer needed

The direct private cancellation helpers and their imports are no longer needed in the parent;
their work is represented by the split intermediate theorem. The parent uses only the
refinement-law clause of `finite_descent`; its existential tensor-domain, cocycle, and descended
transformation clauses are not needed by this route. No dependency node is removed, because the
intermediate theorem and its source still use `lem-sf-projection-refinement-descent`.

## Where the brief, the DAG or earlier work was wrong

The item source was quarantined in `coord/rework.tsv`; this delivery uses the archived source and
preserves its target declaration. The initial direct proof reached the desired categorical square
but exceeded the compile limit during definitional conversion between fixed-scalar coefficient
presentations. The conversion is now isolated in a named intermediate statement, leaving a small
parent proof that compiles within the delivery workflow. No mathematical statement was changed.

Mathlib searches found no matching projection/refinement theorem. The applicable existing result
is `ProjectionRefinementDescent.finite_descent`.

## New nodes

`lem-sf-finite-projection-compactification-square-specialization`, attached to
`Sheaf.Paper.FiniteProjectionFromDescent` and declaration
`WeilConjectures.FixProjectionCompactification.finiteProjectionFromDescent`.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
