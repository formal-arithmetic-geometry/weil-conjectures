## What changed

Replaced the single hole in
`IsDiscreteValuationRing.exists_uniformizer_polynomial_presentation` with a proof
using only Mathlib and two proved private helpers in the item module.
The statement and all public imports are preserved.

Residue surjectivity gives finite expansions in powers of the chosen uniformizer.
Nakayama makes the first n powers span the finite normalization. Mathlib's
`IsIntegralClosure.rank` and `basisOfTopLeSpanOfCardEqFinrank` then make these
powers a basis. The basis polynomial has lower coefficients equal to -pi times
the coordinates of the unit v in t^n = pi*v. If its constant coefficient were
in (pi^2), all terms of the coordinate expansion of v would lie in the maximal
ideal, a contradiction. `AdjoinRoot.equiv'` gives the integral evaluation
presentation. Localizing the same basis gives the field evaluation presentation,
with the mapped polynomial identified by its coordinates.

Updated the item's DAG proof to follow this argument, reusing the existing
Mathlib leaf `lem-sfb-integral-closure-rank`. No other existing module is changed.

Validation: the final item module compiled through `lcompile.py` in 8.8 seconds
with no errors or warnings. Its original theorem signature and public-import
list were checked byte-for-byte; no delivered Lean line exceeds 100 columns.

## Proved and sorry left

Closed the one original hole:
`IsDiscreteValuationRing.exists_uniformizer_polynomial_presentation`.
Added zero holes. No sorry remains in the delivery; both private helpers are
proved: `span_uniformizer_powers` (finite residue expansion and Nakayama) and
`powerBasis_coeff` (the coefficient formula). No decomposition or split-off
statement is used.

## No longer needed

The node `lem-weil-pbc-dvr-unit-times-uniformizer-power` is removed from this
item's proof dependencies. The proof needs neither the distinct-valuation-order
argument for linear independence nor the denominator argument using DVR
factorization: rank and basis localization replace them. This node is a Mathlib
leaf, so no Sheaf module is withdrawn or claimed globally unnecessary.

The original direct private imports `Mathlib.RingTheory.PrincipalIdealDomain`,
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, and
`Mathlib.RingTheory.Localization.Integral` are redundant through
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`. All statement imports remain.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's valuation-order independence and
coefficient argument can be replaced by the shorter coordinate argument above.
The completeness assumption and injectivity half of the residue-field hypothesis
are not needed by this proof, but the original theorem retains both unchanged.
The same reasoning covers n=1 and arbitrary uniformizer choices.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
