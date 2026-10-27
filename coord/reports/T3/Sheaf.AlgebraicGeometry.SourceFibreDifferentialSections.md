## What changed

Added the proof-only auxiliary module `Sheaf.AlgebraicGeometry.SourceFibreDifferentialSectionsAux`.
The source-fibre theorem now composes two named intermediate theorems: one supplies the
normalized differential comparison formula and one supplies injectivity from that formula.
Updated the item node's proof and dependencies and added DAG nodes for both intermediate
statements.

## Proved and sorry left

The target declaration `AlgebraicGeometry.exists_source_fibre_differential_sections` is
proved from the two auxiliary declarations. The two auxiliary declarations remain named
`sorry` statements: `exists_source_fibre_differential_formula` and
`source_fibre_differential_injective_of_formula`. Thus 0 of 1 original hole is closed by
full proof and 2 strictly smaller holes are split off; no definition contains `sorry`.

## No longer needed

None. The original public imports and all declared geometric dependencies remain relevant;
the auxiliary import is proof-only.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the differential comparison and its injectivity argument in
one theorem. They are independent stages: finite-free section comparison establishes the
formula, while spanning of local differentials establishes injectivity. The split records
these as separate, strictly smaller statements without changing the target signature.

## New nodes

`lem-zl-source-fibre-differential-formula` records the comparison map and its formula.
`lem-zl-source-fibre-differential-injective` records the injectivity argument for a map
satisfying that formula.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
