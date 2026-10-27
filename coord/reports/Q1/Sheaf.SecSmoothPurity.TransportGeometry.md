## What changed

Filled `AlgebraicGeometry.ProEtale.PurityTransport.primeUnit` in
`Sheaf.SecSmoothPurity.TransportGeometry`; all signatures, definitions, docstrings,
imports and file options are unchanged. Mathlib's `charP_of_card_eq_prime_pow`
identifies the characteristic of the finite base field from its cardinality.
`CharP.cast_ne_zero_of_ne_of_prime` makes the distinct prime nonzero there,
hence a unit; mapping along `algebraMap D.k₀ D.k` proves the requested unit statement.

The node `def-pur-transport-geometric-indices` has no numbered proof dependencies;
this implements the existing declaration's proof in words without changing the
unit route. LeanFinder and Loogle confirmed the Mathlib lemmas; local searches
also found `WeilConjectures.finiteFieldDatumPrimeUnit` in
`Sheaf.Paper.DirectImagesConstructible`. The direct Mathlib argument avoids
importing that unrelated direct-image theory and uses the existing imports.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.PurityTransport.primeUnit`
(node `def-pur-transport-geometric-indices`). Added 0 holes. No sorry remains
in the delivered module. No statements were split off. The server compiled the proof in 8.9 seconds;
the reported local-instance style warnings were corrected before delivery.

## No longer needed

None: no imports removed, and no DAG nodes or modules withdrawn. The existing
statement imports supply the geometric structures and restricted adjunctions;
`Mathlib.Algebra.CharP.CharAndCard` supplies the cardinality lemma used by the proof.
No extra proof-dependency imports are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The proof works for every prime distinct
from `D.p`, including characteristic two, and for every permitted base exponent;
it does not require a chosen presentation of either field or an algebraic-closure
characteristic instance. No return or rework entry for this item was present.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
