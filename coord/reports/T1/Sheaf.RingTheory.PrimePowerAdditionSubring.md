## What changed

Proved `Subring.exists_prime_pow_add_mem` in
`Sheaf.RingTheory.PrimePowerAdditionSubring`, with its signature and public imports unchanged.
The proof realizes the four-step argument of Stacks Project, Algebra, Tag 0545,
`lemma-help-with-powers`, using the existing Mathlib leaves `add_pow` and
`WittVector.map_frobeniusPoly.key₁`.

Two completely proved private helpers handle remainder-weighted monomial membership and
binomial divisibility when the index has a nonzero remainder. Added the proof-only import
`Mathlib.Tactic.Ring` for the commutative-ring identities. The node's proof now records the
slightly looser bound `D ≤ n*p^n + m*p^m`, sufficient for the same chosen exponent.
Its proof dependencies and source remain the same.

## Proved and sorry left

Closed the sole original hole: `Subring.exists_prime_pow_add_mem`
(node `lem-pur-prime-power-addition-subring`). Proved 1 of 1 original sorries.
Added zero holes; no sorries remain in the delivery, and no intermediate obligation is
split off. The private helpers `Subring.pow_mod_mul_mem` and
`Subring.pow_dvd_choose_of_mod_ne_zero` are also completely proved.

The module compiled cleanly through `lcompile.py` in 2.1 seconds. The proof uses no
cancellation or nontriviality assumption on the ambient commutative ring. A nonzero
remainder excludes index zero before applying the divisibility lemma; the simultaneous
zero-remainder case handles the endpoint terms directly. The monomial helper also works
at exponent zero (and even when the modulus is zero). Delivery preflight checks axioms.

## No longer needed

None. Both declared proof-dependency nodes remain used:
`lem-pur-commutative-ring-binomial-expansion` (`Mathlib.Data.Nat.Choose.Sum`) and
`lem-pur-prime-power-binomial-divisibility`
(`Mathlib.RingTheory.WittVector.Frobenius`). No original imports, nodes, or modules are pruned.
Both public imports still provide the unchanged statement's types and primality predicate;
the new proof-only tactic import is used by the ring identities.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original plan suffices without any new public statement,
new node, statement change, definition change, or consumer adaptation. The unit record
`sk-prop-sf-cbc` has no realized statement or steps affected by this local arithmetic proof.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
