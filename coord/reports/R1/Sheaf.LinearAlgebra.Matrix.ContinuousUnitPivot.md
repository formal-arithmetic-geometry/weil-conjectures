## What changed

Proved `Matrix.continuous_unitPivot_schur_formula` in
`Sheaf.LinearAlgebra.Matrix.ContinuousUnitPivot` with its statement, five definitions,
and public import unchanged. The proof follows the elementary unit-pivot calculation:
a local lower triangular matrix and its multiplication formula give explicit inverse
factors; finite sums and four entry cases give the Schur block identity; the explicit
inverse formulas give continuity of the actual `Ring.inverse` matrices.

Updated the existing node's proof and proof origin to describe the Lean calculation.
No new imports, definitions, public declarations, axioms, or nodes were added.

The final single-file compile passed without errors or warnings (6.0 seconds).
LeanFinder, Loogle and grep searches found generic matrix and inverse lemmas but no
complete continuous rectangular pivot theorem. The proof uses the generic Mathlib
finite-sum, unit-inverse, transpose and continuity APIs already available from the
existing import. Zero reduced dimensions, empty parameter spaces, and the zero ring
remain covered without additional hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`Matrix.continuous_unitPivot_schur_formula`
(node `lem-sfb-unit-pivot-schur-formula`).

Holes added: 0. Split-offs: 0. Sorries left: none.
This is a complete proof from Mathlib, not a decomposition into new obligations.

## No longer needed

None. No imports were removed. The sole conceptual dependency `def-weil-matrix`
remains; no declared proof dependencies or modules have been bypassed. All auxiliary
matrix formulas are local to the proof and fully proved.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or definition was found. The existing node's source-place
wording says HRS uses this matrix identity as a standard calculation; the existing
module documentation and the node's previous review correctly qualify the formula as
an agent-written elementary calculation motivated by HRS. The updated proof origin
preserves that distinction; maintainer-owned source fields were not changed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
