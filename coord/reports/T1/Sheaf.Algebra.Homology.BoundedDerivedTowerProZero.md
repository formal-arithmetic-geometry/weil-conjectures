## What changed

Proved `DerivedCategory.tower_proZero_of_bounded_homology_proZero` with its exact original
signature. The proof inducts on `(b - a).toNat`, uses the functorial truncation triangle,
and applies the existing `CategoryTheory.Pretriangulated.proZero_middle_of_distinguished_tower`.
Five proved private helpers provide single-degree detection of zero maps and the homology
monomorphism/epimorphism cancellation needed to transfer zero transitions through truncations.
Added only the proof import `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.
Updated the existing node's proof and proof origin to describe the actual induction.
All public imports, definitions, signatures, and visibility are unchanged.

Validation: launcher compilation succeeds without warnings (3.5 seconds before final cleanup).
The single-degree case includes arbitrary integer degree and zero objects. The successor case
uses only the original uniform bounds and the original degreewise pro-zero condition; it
introduces no compatibility or boundedness assumptions. The declared proof dependencies
are all used, and the unit route is retained.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.tower_proZero_of_bounded_homology_proZero`
(node `lem-weil-pbc-bounded-derived-tower-pro-zero`).

No `sorry` remains in the delivered module. No holes added; no split-offs and no new modules.
The proof uses the existing stated theorem
`CategoryTheory.Pretriangulated.proZero_middle_of_distinguished_tower`
(node `lem-weil-pbc-essentially-constant-zero-triangle`), whose proof is still `sorry` in the
shared library. Consequently this delivery closes this module's hole from the intended
stated dependency; it does not claim that all its transitive axioms have been discharged.

## No longer needed

No imports, declared dependency nodes, or modules are pruned. All three original proof
dependencies remain used. The preliminary simultaneous choice of indices for every degree
in `[a,b]` is unnecessary: the induction needs only degree a for the lower truncation, and
combines the two outer-tower indices with `max`. This removes an elementary step, not a node.
The added FullyFaithful import is necessary: removing it makes the singleFunctor fullness
instance unavailable, as checked by launcher compilation.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original finite-degree simultaneous
vanishing step was redundant for the stated truncation induction; the updated node omits it.
The original declaration docstring is preserved. No statement or definition repair was needed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
