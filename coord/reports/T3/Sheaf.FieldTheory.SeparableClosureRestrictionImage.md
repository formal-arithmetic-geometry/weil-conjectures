## What changed

Proved `IntermediateField.separableClosure_restriction_image` in
`Sheaf.FieldTheory.SeparableClosureRestrictionImage`, with its signature unchanged.
Restriction is continuous because each finite intermediate field has finitely many
field generators and their images generate a finite extension of L. Compactness
then gives a closed range. The fixed field of this range is identified elementwise
with the preimage of L, and Mathlib's closed-subgroup Galois correspondence gives
the asserted image equality. Updated the item's node to record this route.

Added the private proof import
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra` for finite field generators.
The proof uses only Mathlib, with no admitted intermediate statements.
Validation: the final module compiled through `lcompile.py` in 2.6 seconds,
with no errors or warnings.

## Proved and sorry left

Closed the one original hole:
`IntermediateField.separableClosure_restriction_image`
(node `lem-per-galois-restriction-image`). Holes closed: 1; holes added: 0;
holes remaining in the delivery: 0. No split-off statements.

## No longer needed

Removed these private proof imports:

- `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`: already supplied by
  the required Galois profinite module.
- `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`: the specialized
  finite algebraic field-adjoin API handles the finite extension directly.
- `Mathlib.Topology.Algebra.ClopenNhdofOne`: the closed-subgroup Galois
  correspondence gives the image without an intersection of open subgroups.

Removed proof dependencies and their obsolete top-level tool-use entries:

- `lem-sc-finite-generated-integral-subring`: replaced by the existing Mathlib
  theorem `IntermediateField.finiteDimensional_adjoin`; no separate subalgebra
  or inverse construction is needed.
- `lem-wf-profinite-closed-subgroup-intersection-open`: replaced by the
  closed-subgroup identity `InfiniteGalois.fixingSubgroup_fixedField` already
  recorded in the retained Galois-correspondence dependency.

No project module was withdrawn. The retained profinite-limit dependencies
supply Mathlib's compact Galois group instance. The unit's statement and steps
are untouched; this is only a shorter implementation of the node's field theory.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original six-step argument was correct, but
its explicit finite integral subring construction and final open-overgroup
intersection are unnecessary given Mathlib's existing APIs. The statement
continues to allow transcendental and inseparable L/K. The proof also handles
K=L and a separably closed base without additional assumptions.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
