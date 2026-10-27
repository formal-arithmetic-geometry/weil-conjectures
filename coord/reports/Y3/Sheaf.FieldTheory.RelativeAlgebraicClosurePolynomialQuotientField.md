## What changed

Completed `Polynomial.irreducible_map_and_isField_quotient_of_isAlgebraic_mem` in
`Sheaf.FieldTheory.RelativeAlgebraicClosurePolynomialQuotientField`, preserving its signature.
Added the proof-only import `Mathlib.Algebra.Polynomial.Lifts`.

Mathlib's `Polynomial.irreducible_of_monic` reduces irreducibility to monic
factorizations. For each factor, `Polynomial.isIntegral_coeff_of_dvd` gives integral,
hence algebraic, coefficients. The hypothesis puts each coefficient in the image
of the base field; `lifts_iff_coeff_lifts` and `mem_lifts` produce its polynomial
preimage. Injectivity descends the factorization, and irreducibility over the base
field makes a descended factor a unit. Its image is a unit, so the corresponding
monic factor is one. The principal-ideal-ring maximality theorem then makes the
literal polynomial quotient a field. Mathlib's field spectrum instances give
uniqueness and irreducibility of its spectrum.

This implements the existing node's five-step argument, with normalization and
finite-support bookkeeping supplied by proved Mathlib lemmas. The unit route and
all dependency nodes are retained.

## Proved and sorry left

Closed 1 of 1 original holes:
`Polynomial.irreducible_map_and_isField_quotient_of_isAlgebraic_mem`
(node `lem-zl-relative-algebraic-closure-polynomial-quotient-field`).
No holes remain in the item; no holes were added or split off. All proof inputs
are proved Mathlib declarations. The final item compiled cleanly through
`lcompile.py` in 2.7 seconds, without warnings.

## No longer needed

None. No imports were removed and no nodes or modules were pruned. Each declared
proof dependency is used through its existing Mathlib realization.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Read the coefficient-descent argument in
Stacks Algebra, Tag 037P (`lemma-field-extension-geometrically-irreducible`), and
its coefficient-integrality input Tag 00H6. The argument applies without
separability or finite generation, as the assigned statement requires.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
