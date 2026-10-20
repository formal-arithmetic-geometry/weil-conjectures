## What changed

Withdraw the already-retired duplicate module
`lean/Sheaf/RingTheory/PowerSeriesRingSubfields.lean` using `deleted.txt`.
The retained declaration is the complete upstream theorem
`WeilConjectures.RingTheory.iInter_frobenius_subfields_mvPolynomial_mvPowerSeries`.
This item has no remaining Lean declaration or proof hole.

## Proved and sorry left

This is a retirement repair with zero original holes and zero remaining holes.
Holes closed: none (0 of 0). Holes added: none. Split off: none.

## No longer needed

The Sheaf duplicate and its declaration are no longer needed. The upstream module and
upstream theorem remain in use by existing consumers. No proof dependency or target
statement is changed.

## Where the brief, the DAG or earlier work was wrong

The current queue still lists this item as `retire` even though the human-authorized
retirement was already landed and the Sheaf module is an empty withdrawn stub. The DAG
attachment points to the retained upstream theorem; no new proof is required.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
