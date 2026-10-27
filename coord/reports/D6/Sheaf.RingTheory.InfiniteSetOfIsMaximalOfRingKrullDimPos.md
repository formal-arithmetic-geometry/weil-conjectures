## What changed

Proved `Algebra.FiniteType.infinite_setOf_isMaximal_of_ringKrullDim_pos` in
`Sheaf.RingTheory.InfiniteSetOfIsMaximalOfRingKrullDimPos`, preserving its full signature
and both public imports. Added proof-only imports `Mathlib.RingTheory.Jacobson.Ring`
and `Mathlib.RingTheory.KrullDimension.Field`.

The finite-type algebra is Jacobson, so zero is the intersection of its maximal ideals.
If that family were finite, `Ideal.eq_inf_of_isPrime_inf` would make zero one of its
members, because zero is prime in a domain. Then `Ring.isField_iff_maximal_bot` makes
the ring a field and `ringKrullDim_eq_zero_of_isField` contradicts positive dimension.
Updated the existing node's proof, proof dependencies and proof origin to this route.
The unit's statement and route are preserved; this node is below the unit realization.

Validation: the complete module compiled through `lcompile.py` in 2.1 seconds,
without errors or warnings. The delivery also runs the required compiler/axiom probe.
All newly added imports are used. No statement, definition or public interface changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.FiniteType.infinite_setOf_isMaximal_of_ringKrullDim_pos`
(node `lem-sc-fg-domain-positive-dimension-infinite-maximals`).
Zero holes remain in the item; zero holes added; zero split off.
The proof uses only proved Mathlib declarations.

## No longer needed

Removed the proof dependency `lem-weil-pbc-proper-ideal-contained-in-maximal` from
this node. The finite-prime-infimum lemma supplies a member even when the initial
family might be empty, so no separate invocation of `Ideal.exists_le_maximal` is needed.
This is a Mathlib leaf, with no project module to withdraw. No Lean imports removed,
no project modules withdrawn, and no other dependencies pruned.

The explicit choices of nonzero elements and their product in the original plan are
subsumed by Mathlib's proved finite-intersection/primality lemma. The Jacobson
finite-type dependency remains needed and used through its recorded Mathlib match.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The original plan was longer than necessary:
Mathlib already provides the finite-intersection argument, including the empty case.
No new statements or nodes, no repairs, and no consumer adaptations were required.
The field case has dimension zero, so cannot satisfy the hypothesis; the argument
requires no assumption that the ground field is infinite or algebraically closed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
