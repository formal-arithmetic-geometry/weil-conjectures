## What changed

Proved `Algebra.normal_ring_of_normal_tensor_field` by the node's local faithfully flat
argument from Stacks Project Tag 033G. A private, fully proved helper carries its
fraction-field and principal-ideal contraction steps. The scalar extension is faithfully
flat by Mathlib's vector-space freeness and base-change instances. For every source prime,
Mathlib supplies a prime above it and a flat local map of prime localizations. Faithful
flatness makes this map injective, so its source is a domain. Integral fractions map to
integral fractions in the normal target; contracting the denominator's principal ideal
then puts the original fraction in the source.

Validation: the required `deliver3.py --no-push` dry run passed as `AUTO`, including
compilation of the final module and the axiom audit. No new axiom or `sorry` is used.

## Proved and sorry left

Closed `Algebra.normal_ring_of_normal_tensor_field` (1 original hole).
Added no holes; no `sorry` remains in the delivery.

## No longer needed

No DAG dependency is pruned: all seven planned dependencies are used through their Mathlib
matches, including the inline normality definition. No other Sheaf or WeilConjectures
module is imported or needed. Removed the redundant proof-only import
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`; the retained `Algebra` module imports it.
The public imports and existing theorem signature are unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The proof uses prime-local flat maps directly as planned; it neither assumes that
`B` is a domain nor adds nontriviality, Noetherianity, finiteness or separability assumptions.
The zero ring case remains vacuous because the conclusion ranges over prime ideals.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
