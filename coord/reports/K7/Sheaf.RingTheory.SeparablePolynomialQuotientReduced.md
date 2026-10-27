## What changed

Proved `Polynomial.isReduced_quotient_of_separable` in
`Sheaf.RingTheory.SeparablePolynomialQuotientReduced`, preserving its statement and imports.
The proof follows the existing two-step DAG argument: `Polynomial.Separable.squarefree`
provides squarefreeness, `Squarefree.dvd_pow_iff_dvd` removes the positive power, and
`Ideal.mem_span_singleton` converts ideal membership to divisibility in both directions.
The hypothesis `1 ≤ m` supplies the required `m ≠ 0`. All ingredients are already available
through the existing public import `Mathlib.FieldTheory.Separable`.

## Proved and sorry left

Closed the sole hole: `Polynomial.isReduced_quotient_of_separable`
(node `lem-weil-pbc-separable-polynomial-quotient-reduced`).
Holes closed: 1. Holes added: 0. Sorries left: none. No split-off statements.

## No longer needed

None. No imports removed, no dependencies pruned, and no modules withdrawn.
The existing Mathlib leaf `lem-weil-pbc-squarefree-polynomial-divides-power` is used
through its recorded declaration `Squarefree.dvd_pow_iff_dvd`. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib already proves the squarefreeness calculation described in the DAG,
so no separate derivative calculation or new intermediate statement is necessary.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
