## What changed

Completed the interrupted worker's two prime-unit proofs in
`Sheaf.SixFunctors.FrobeniusPointTransport`. Both now prove the coefficient unit
from Mathlib rather than the unproved `finiteFieldDatumPrimeUnit`.
The cardinality of the base field gives characteristic `D.p` by
`charP_of_card_eq_prime_pow`. Distinct primes do not divide one another, so
`CharP.isUnit_natCast_iff` makes `l` a unit in the base field. Map this unit into
its algebraic closure, then into the stalk or residue field. Naturality of natural
number casts identifies the images with the required elements.
Added proof-only imports `Mathlib.Algebra.CharP.CharAndCard` and
`Mathlib.Algebra.CharP.Invertible`.
All existing signatures, definitions and public imports are unchanged.

## Proved and sorry left

Closed two of the item's five holes:
`WeilConjectures.frobeniusPointPrimeUnit` and
`WeilConjectures.frobeniusPointPrimeResidueUnit`.
Their proofs use only Mathlib and the finite-field datum's hypotheses.
No holes were added and no theorems were split off.

Three existing holes remain, all attached to
`def-weil-frobenius-point-transport`:

- `WeilConjectures.frobeniusPointFiniteSigma_existsUnique`.
- `WeilConjectures.frobeniusPointIntegralSigma_existsUnique`.
- `WeilConjectures.frobeniusPointTransportIntegral_existsUnique`.

## No longer needed

Removed the interrupted sandbox's proof import
`Sheaf.Paper.DirectImagesConstructible`: the characteristic argument closes both
prime-unit holes without its unproved `finiteFieldDatumPrimeUnit`.
This import was absent from the repository version; no existing library import,
node or module is pruned. All original public imports support existing statements
or definitions.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt had no report or completed delivery. Its approach of
transporting coefficient units through canonical ring maps was retained, and the
coefficient unit itself is now proved directly. The node has no numbered proof
plan. No statement error was found or signature changed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
