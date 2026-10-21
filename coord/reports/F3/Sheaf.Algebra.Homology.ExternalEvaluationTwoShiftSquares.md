## What changed

Completed the componentwise construction and seven-step argument in
`Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares` using private helpers.
The construction extends the signed formula through the sheaf tensor and the
coefficient tensor universal properties, checks the Hom differential, builds the
Hom and balancing shift isomorphisms, and proves both squares by evaluating on
homogeneous pure tensors. The original theorem signature is unchanged.

A local tensor-totalization instance avoids repeated searches; the generic
section insertion and naturality API controls elaboration of the constant functor.

The proof reuses Mathlib's bifunctor shift comparisons and Hom-complex cochain
API. A private `import all Sheaf.SecSmoothPurity.CochainInverseComparison`
provides the already-proved pure-section tensor API, with independent site
universes. Additional private imports provide the sectionwise scalar map and
integer sign arithmetic. Three proved public instances expose termwise shift compatibility and the two
existing tensor-totalization instances: `underlyingCommShift`, `complexHasTensor`,
and `coefficientHasTensor`, in namespace `CategoryTheory.ExternalEvaluation`.
They select the existing constructions. No new module is added.

The three complex/functor aliases and four shift comparisons now use `def`
instead of `abbrev`, with the same types and construction terms, to control eager unfolding. See
`coord/changes/external-evaluation-shift-transparency.md`. The required consumer
search found zero downstream Lean modules, so no forced adaptations are needed.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ExternalEvaluation.external_evaluation_two_shift_squares`
(node `lem-pur-external-evaluation-two-shift-squares`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the item
module or is added elsewhere by this delivery. All auxiliary theorems are
private and proved; every isomorphism and pairing is a concrete construction.

## No longer needed

Removed the private import `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
this is a computation with ordinary cochain complexes, and the Hom and tensor
shift APIs already supply the operations used here.

No DAG dependency or module is withdrawn. The proof follows all seven steps of
the existing node and preserves the blueprint unit's route. It needs neither
boundedness nor flatness nor injectivity, and does not use the distinct internal
sheaf Hom complex in place of the stated global Hom complex.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The existing direct-sum
tensor and Hom-complex conventions give exactly the two advertised exponents,
`s*q+s` and `s*q+q+r`, in arbitrary integer degrees. The transparency change
above repairs elaboration cost only and changes no mathematical object.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
