## What changed

Proved `RingHom.exists_finite_span_awayMap_of_finite_fiber_minimalPrime` in
`Sheaf.RingTheory.MinimalPrimeFiniteTypeFiniteAwayAux`, with its signature unchanged.
Added two proved private helpers: integrality from a finite quotient by a nil ideal,
and integrality after localization at the given minimal prime. Added private Mathlib
imports for the fibre correspondence, dimension-zero local rings, localization of
integral elements, and finite-type base change.

The fibre quotient is first viewed as a finite module over the prime localization,
which avoids a separate lift of residue-field polynomial coefficients. Mathlib's two
integrality denominator-clearing lemmas then supply integral multiples of each algebra
generator. Inverting their product makes the generators integral; finite adjoin gives
the spanning family. Updated the existing node's proof to describe this implementation.

## Proved and sorry left

Closed the single original hole:
`RingHom.exists_finite_span_awayMap_of_finite_fiber_minimalPrime`
(node `lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux`).
No holes remain in the item, and no holes were added or split off.
Both private helpers have complete proofs. The full module compiled successfully
in 5.9 seconds; the two local-instance style warnings were then corrected.
The delivery runs the final compilation and axiom probes.

## No longer needed

None. All five declared proof dependencies are used. No imports, nodes, modules,
or source-library declarations were removed. The finite-type finite-spectrum theorem
is retained as the fibre-finiteness input. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. A separate residue-field coefficient-lifting step is
unnecessary: restriction of scalars makes the fibre quotient finite directly over
`Localization.AtPrime p`, and its monic annihilating equations lift integrality
across the nil kernel by taking powers.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
