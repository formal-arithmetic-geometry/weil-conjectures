## What changed

Proved `complete_toric_monomial_factor` in
`Sheaf.TraceFormula.CompleteToricMonomialFactors` with its signature unchanged.
A proved private helper `monomial_factor_of_recognition` implements the elementary
localization calculation once for an arbitrary commutative ring and monoid chart.
`IsLocalization.map_units` makes the chart monomial a unit; after rewriting the
factorization, `isUnit_of_mul_isUnit_left` makes the first factor a unit in the
localization. The recognition equality then supplies a unit times a chart monomial.
The main theorem applies this helper to the field and Cohen quotient clauses of
`complete_toric_kato_recognition`, converting the multiplicative exponent back to
its additive tag. This follows the existing DAG proof and preserves the unit route.
No imports, statements, definitions, or DAG dependencies changed.

Validation: the complete module compiled through `lcompile.py` (exit 0, 9.6 seconds).
The helper makes no nonzero, nontriviality, positive-exponent, or positive-dimension
assumption, so the same calculation covers exponent zero, the trivial monoid,
and zero parameters.

## Proved and sorry left

Closed 1 of 1 original holes: `complete_toric_monomial_factor`
(node `lem-trf-complete-toric-monomial-factors`).
Added 0 holes; split off 0 statements; 0 holes remain in the delivered module.
The private helper is proved without `sorry`.
The existing dependency `complete_toric_kato_recognition`
(node `lem-trf-complete-toric-kato-recognition`) remains an imported theorem with
its own unfinished proof; this delivery neither changes nor duplicates it.

## No longer needed

None. The sole original public import,
`Sheaf.TraceFormula.CompleteToricKatoRecognition`, is needed for the statements'
charts and rings and the proof's recognition equality. The sole planned proof
dependency `lem-trf-complete-toric-kato-recognition` is used. No modules or nodes
are pruned, and no unused proof imports were added.

## Where the brief, the DAG or earlier work was wrong

None for the mathematical argument. The stated recognition theorem fits both
coefficient cases exactly. The explicit inverse calculation is discharged using
Mathlib's general localization-unit and product-unit lemmas.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
