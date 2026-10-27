## What changed

Proved `Polynomial.existsUnique_monic_factorization_of_locally_nilpotent` in
`Sheaf.RingTheory.FactorizationLocallyNilpotent`, with its statement unchanged.
The proof first constructs the `HenselianRing A J` proof by finite Newton iteration,
then applies the existing proved `henselianRing_iff_factorization_criterion`.
For uniqueness it lifts Bezout coefficients, observes that their error polynomial
is nilpotent coefficientwise, and inverts the resulting unit. Coprimality then gives
divisibility, monic degree comparison gives equality, and monic cancellation finishes.
The zero ring is handled by `nontriviality A`; properness of J supplies the
nontrivial quotient needed for monic degree comparison.

Added the private proof import `Mathlib.Dynamics.Newton` and removed the redundant
private import `WeilConjectures.Mathlib.RingTheory.Henselian`. Updated the theorem's
proof docstring and its existing DAG node to describe the actual proof.
No signatures, definitions, public imports, or consumer modules change.
Server compilation passed cleanly (4.5 seconds). A temporary `#print axioms` check
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the diagnostic
command was removed before delivery.

Searches: LeanFinder found the universal coprime factorization ring and the
root-lifting predicate, but no direct factorization-lifting theorem. Loogle found
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le`. The search wrapper and local `rg`
confirmed Newton iteration, coefficientwise polynomial nilpotence, monic regularity,
and coprime divisibility as the shortest applicable existing ingredients.

## Proved and sorry left

Closed 1 of 1 original holes:
`Polynomial.existsUnique_monic_factorization_of_locally_nilpotent`
(node `lem-weil-pbc-henselian-factorization-locally-nilpotent`).
No `sorry` remains in the item. Added 0 holes and split off 0 statements.

## No longer needed

Removed private import `WeilConjectures.Mathlib.RingTheory.Henselian`: the factorization
criterion already exposes the required henselian interface.

The item's direct proof no longer needs these declared dependencies:

- `lem-weil-pbc-locally-nilpotent-extension`: finite Newton iteration works in A itself.
- `lem-weil-pbc-lift-idempotents-locally-nilpotent`: the simple-root definition is proved directly.
- `lem-weil-pbc-monic-quotient-free`: uniqueness uses polynomial nilpotence and Bezout.
- `lem-weil-pbc-nakayama-jacobson`: the Bezout error is nilpotent, so its sum with 1 is a unit.

These four nodes were removed from this node's `proof_deps` and proof-step `uses`.
They are Mathlib leaves, not modules being withdrawn. The retained factorization
criterion may still use monic quotient constructions transitively; no claim is made
that those constructions disappear from the whole targets' closure. No Lean module
is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original proof plan passed through finite-algebra
idempotents to establish henselianity, although the recorded Lean notion is the
simple-root predicate. Finite Newton iteration proves that predicate directly while
retaining congruence modulo J at each step. Merely using the theorem that supplies a
root with nilpotent difference would not ensure membership in an arbitrary nil ideal;
the iterate congruence induction is essential.

The Nakayama step of the old uniqueness plan is valid but unnecessary under the
stronger nil-ideal hypothesis here. Coefficientwise nilpotence gives a shorter
Bezout proof. The unit route is preserved: no realized unit statement or step is bypassed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
