## What changed

Proved `AddMonoidAlgebra.positiveMonoid_convolution_length` without changing its
statement or public imports. All added helpers are private to the item module.
The weight bounds give a greatest attained decomposition length. Closure induction
expresses each exponent as a finite word of generator indices, and Mathlib's finite
sets of bounded-length words prove both sublevel finiteness assertions. Nonnegative
weights then bound every component of a pair or triple decomposition.

The convolution ring is constructed explicitly with coefficientwise additive
operations, finite convolution multiplication, and natural and integer constants
supported at zero. A bijection between the two nested pair-index sigma types proves
associativity. Single-coefficient calculations prove the unit, constant ring map,
monomial products, and both shift formulas. Cancellation proves shift uniqueness.
The item's DAG proof now records the finite-word and sigma-bijection implementation.
Proof-only imports were added for `Mathlib.Data.Set.Finite.List`, `Mathlib.Data.Nat.SuccPred`,
`Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Order.SuccPred.Archimedean`,
`Mathlib.Tactic.Choose`, and `Mathlib.Tactic.Linarith`.

## Proved and sorry left

Closed the one original hole in
`AddMonoidAlgebra.positiveMonoid_convolution_length`
(node `lem-trf-positive-monoid-convolution-length`).
No holes added, none split off, and no `sorry` remains in the delivery.

## No longer needed

No existing imports, dependency nodes, or modules were removed. The original node
had no proof dependencies; the proof uses Mathlib directly. Finite generator words
replace the planned multiplicity boxes, so no separate multiplicity representation
or coordinate-bound lemmas are needed. The ambient freeness and finite-rank
hypotheses are preserved verbatim, although the elementary argument does not need
them. No unit statement or unit proof route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. ILO VI 1.6(i)--(ii), printed p. 70, supplies the
formal monoid models, and the elementary coefficient proof is attributed to the
agent-supplied DAG argument, as before. The construction covers an empty generator
list, the trivial monoid, zero decomposition length, and the zero coefficient ring.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
