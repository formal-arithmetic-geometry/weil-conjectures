## What changed

Filled `AlgebraicGeometry.etaleBrownProperSingletonEvaluation` in
`Sheaf.Paper.EtaleBrownProperSingletonEvaluation`, preserving its statement and all
existing public imports. Added private proof imports of
`Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison` and
`Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`.

Four proved private helpers identify the package's below-level comparison with
the normalized derived transition mate, record its Hom transpose, compute the
scalar transpose of the geometric projection mate, and compute the singleton
transpose of the canonical insertion mate. The final argument pastes these
identities using `directTransition` and naturality of `restrictedDirect`.
The node's proof and proof dependencies now describe this argument.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.etaleBrownProperSingletonEvaluation`
(node `lem-pur-etale-brown-proper-singleton-evaluation`).
No holes added or split off; no `sorry` remains in the delivered Lean module.

## No longer needed

No existing public import was removed. The proof needs neither the separate
`Sheaf.CategoryTheory.SystemSingleDerivedEvaluation` model nor its node
`lem-pur-system-single-derived-evaluation`: the supplied package's comparison is
identified directly by the universal property of scalar left derivation.
The existence theorem `coefficientSystemDerivedComparison` (old proof dependency
`lem-pur-coefficient-system-derived-comparison`) is also unnecessary as a proof
step: the input already supplies its normalized image data. Its module remains
transitively publicly imported through the unchanged interfaces; this delivery
makes no whole-module withdrawal or claim that it leaves the target closure.
The needed counit, tensor-mate and transition equations are cited at the more
precise node `def-pur-coefficient-system-image-data`.

## Where the brief, the DAG or earlier work was wrong

The recorded K-flat representative calculation is not necessary here. The package
already records universal left derivation and the representative equations, so
`derivedMate_comparison` and `leftDerived_ext` prove the required identification
without choosing another K-flat resolution or another evaluation package.
No statement or definition was changed. The proof uses no regularity, finiteness,
nonzero-coefficient or singleton-invertibility assumption, and handles m = n with
the same equations. The unit record has no realized steps to bypass.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
