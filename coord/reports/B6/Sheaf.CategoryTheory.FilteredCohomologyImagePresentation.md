## What changed

Retire the assigned duplicate `Sheaf.CategoryTheory.FilteredCohomologyImagePresentation`
in favor of the existing proved upstream theorem in
`WeilConjectures.CategoryTheory.FilteredCohomologyImagePresentation`.
The complete theorem, including its proof, matches modulo whitespace.
Change the sole direct consumer, `Sheaf.CategoryTheory.FilteredStableSubquotient`,
by replacing one private proof import. Reattach the existing DAG node to the
upstream declaration without changing its statement or proof dependencies.

Change record: `coord/changes/B6-retire-filtered-cohomology-image-presentation.md`.
The source-library tree is untouched.

## Proved and sorry left

The current assigned module has 0 sorries. Holes closed: 0. Holes added: 0.
No split-off statements; no sorry remains in any delivered module.
`CategoryTheory.DecreasingFiltration.cohomologyImage_graded_presentation`
continues to have its complete upstream proof with exactly its original signature.
The adapted `stableSubquotient_at_bounds` proof is unchanged.
An explicit example checks the upstream theorem against the original signature;
`#print axioms` checks its permitted-axiom proof, and the adapted consumer compiles.

## No longer needed

Withdraw `Sheaf.CategoryTheory.FilteredCohomologyImagePresentation` using
`deleted.txt`. Its sole direct consumer replaces the Sheaf proof import with
the upstream import. All mathematical dependency nodes remain needed and are
preserved: the normalized cohomology-image and stationary-quotient theorems
still supply the upstream proof. No upstream declaration or dependency is pruned.
The theorem's DAG node is reattached, never deleted, and its parent still uses it.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished theorem, but the assigned
queue entry is a retirement and the current module already has zero holes.
The PROOFDIFF_UNSAFE inventory reflects obsolete parallel dependency providers;
current source inspection and compilation verify the upstream family can now
replace the duplicate without overlapping declarations. No mathematical
statement, target definition, unit route, or proof plan requires correction.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
