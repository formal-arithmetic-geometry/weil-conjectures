## What changed

Proved `Ideal.regularSequence_gradedPolynomial` with its original statement and
canonical map unchanged. Retained and checked the earlier attempt's monomial
formula, coefficient lifts, homogeneous projections, bijectivity, grading and
unique-expansion proofs. Completed the outstanding coefficient argument in
`Sheaf.RingTheory.RegularSequenceHigherRelations`: its public theorem
`Ideal.regularSequence_homogeneous_relation` now covers every length and degree.
The proof follows Stacks 00LN (1), with simultaneous induction on sequence length
and the greatest exponent of the last variable. Private proved helpers expand
ideal powers, raise the prefix degree, cancel the last generator modulo the
prefix ideal, and lower its exponent. No statement or definition in the existing
library was changed.

## Proved and sorry left

Closed the one original hole `Ideal.regularSequence_gradedPolynomial`
(node `lem-pur-regular-sequence-graded-polynomial`). Also proved the earlier
attempt's pending split, now `Ideal.regularSequence_homogeneous_relation`
(node `lem-pur-regular-sequence-higher-homogeneous-relations`). There are zero
`sorry` declarations in either delivered module: one original hole closed,
zero holes added, zero split off. Every private helper is proved.

Both modules compile through `lcompile.py --all` without errors or warnings.
`#print axioms` for both public theorems reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The proof includes the empty sequence, the zero polynomial and degree zero;
no nonempty-sequence or positive-degree hypothesis is added.

## No longer needed

Removed the original proof-only import
`Sheaf.RingTheory.AssociatedGradedRingStructure`, a retired duplicate/re-export.
Also removed the redundant direct proof import
`WeilConjectures.RingTheory.AssociatedGradedRing`: the retained public import
`Sheaf.RingTheory.AssociatedGradedRing` already exposes that source module.
The associated-graded structure node remains needed through
`Sheaf.RingTheory.AssociatedGradedRing` and its source library: its multiplication,
unit and scalar formulas are used explicitly. No original mathematical node is
pruned. The earlier attempt's extra proof dependency
`lem-weil-pbc-regular-sequence-conormal-free` and its import
`Sheaf.RingTheory.RegularSequenceConormal` are also unnecessary: the proved
coefficient induction already handles degree one. Removed the separate degree-zero,
empty-sequence, one-generator and linear-relation helpers and their case split.
The free-module statement dependency remains, since the theorem asserts the
unique finite basis-expansion criterion. Mathlib's
`Ideal.mem_span_pow_iff_exists_isHomogeneous` supplies ideal-power spanning;
no further spanning lemma or node is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had reduced the coefficient assertion to a new hole only
for lengths and degrees at least two. Its induction proof also works in the
excluded cases, so the new public helper is proved uniformly instead. The
original dependencies describe the needed constructions but do not themselves
state this coefficient induction; it is now formalized from Mathlib and the
source argument. No statement is disputed. Scratch experiments are retained
under `scratchpad` and excluded from delivery. No definitions or existing public
signatures changed, so no consumer adaptation or change record is required.

## New nodes

`lem-pur-regular-sequence-higher-homogeneous-relations`, despite its inherited id,
now states the fully proved homogeneous zero-relation coefficient assertion
in all lengths and degrees. It is strictly the injectivity part of the
associated-graded theorem; it does not assume or restate that theorem. Its
module is `Sheaf.RingTheory.RegularSequenceHigherRelations`, and its declaration
is `Ideal.regularSequence_homogeneous_relation`. Its source is Stacks 00LN (1).
The DAG records the two inductions and the final zero-relation specialization.
No arbitrary data is chosen from an unproved existence theorem.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
