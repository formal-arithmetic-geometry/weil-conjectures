## What changed

Proved `LinearEquiv.exists_flag_finite_coefficients` with its existing signature. Private proved helpers implement coordinate descent of an arbitrary basis, flags of a triangular automorphism, quotient coordinate equivalences and the scalar-extension comparisons. No new public declarations or definitions. Replaced the private categorical descent import by `Mathlib.RingTheory.Flat.Basic` to use the direct tensor exactness APIs. The node proof now describes this construction. The complete file compiled without holes or warnings in 46.2 seconds. Local abstraction of the chosen field and bases, followed by clearing unused existential witnesses, prevents repeated unfolding during tensor-instance comparison.

## Proved and sorry left

Closed the one original hole: `LinearEquiv.exists_flag_finite_coefficients` (node `lem-zl-automorphism-flag-finite-coefficients`). Holes added: zero. Holes left: zero. No statements split off.

## No longer needed

Removed private import `Mathlib.Algebra.Category.ModuleCat.Descent`: direct linear-map tensor exactness suffices. All six declared proof dependencies remain used mathematically. No nodes or modules are withdrawn. Separately adjoining inverse basis matrices, operator matrices or diagonal scalars is unnecessary: adjoining basis coordinates alone gives a descended basis by independence and dimension, and all those further data are constructed over that field. Public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's simultaneous-coordinate adjunction plan is valid but redundant. Only the adapted-basis coordinates must be adjoined. The empty-dimensional case is covered by the same finite-range construction and all quotient-indexed requirements are vacuous; no special branch is needed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
