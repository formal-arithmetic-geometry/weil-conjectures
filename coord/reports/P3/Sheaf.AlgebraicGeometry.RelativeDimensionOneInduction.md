## What changed

Proved `AlgebraicGeometry.Etale.universalBaseChangeProperty_relativeDimensionOne_induction`
in `Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction`, with its original signature and
public imports unchanged. The proof follows the unit's failure-witness/curve-test contradiction.
A proved private helper transports the affine integral normal base to the spectrum of its global
sections, transports its normal stalks, identifies its fraction field and geometric generic map,
and applies the existing ring-based vanishing theorem. The main proof establishes base-change
permanence, divisor invertibility, the contradiction, and the cumulative degree bound.

Updated the existing node's proof to describe the affine-coordinate translation and the field
embedding already supplied by the failure witness. All five declared proof dependencies remain
used. No definitions, public statements, or other modules changed. Remote single-file compilation
passed without warnings after import pruning.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.universalBaseChangeProperty_relativeDimensionOne_induction`
(node `sbc-lem-rel-dim-one-induction`). Added 0 holes; split off 0 statements. No `sorry` remains
in the delivered module. The private helper `isZero_curveTest_affine` is fully proved.
The two existing dependency theorems (failure datum and universal curve-test vanishing) are used
as stated; this delivery does not claim to close their own holes or the transitive axiom closure.

The case q = 1 uses precisely degree zero from the cumulative hypothesis. The argument does not
assume the original base is affine or nonempty. The witness base is nonempty because it is
integral; this supplies the nonempty top open needed for its fraction-field algebra. Empty total
spaces are allowed. Divisor invertibility follows from d dividing the invertible n, without adding
a positivity hypothesis on d or changing coefficients.

## No longer needed

Removed the direct proof imports `Mathlib.AlgebraicGeometry.Morphisms.Separated` and
`Mathlib.AlgebraicGeometry.Limits`: the proof uses neither separatedness nor the finite coproduct
construction. The Cartesian-square APIs are available from the existing dependency imports.
No declared dependency node or Sheaf/WeilConjectures module was pruned: the proof uses
`sbc-lem-bc-universal-test`, `sbc-thm-universal-test-vanishing`,
`lem-weil-pbc-affine-morphism-permanence`,
`lem-sbc-smooth-relative-dimension-permanence`, and `sbc-def-base-change-property`.
The source library's induction theorem was inspected, but the delivered proof directly uses the
assigned cyclic abelian failure and vanishing interfaces and retains the prescribed unit route.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The failure-datum declaration already supplies the field embedding
and generic-point factorization that the original node's first step proposed constructing.
The vanishing declaration takes an explicit ring spectrum, whereas the failure declaration gives
an abstract affine scheme; the private helper supplies this translation with Mathlib isomorphisms.
No new node, definition repair, or forced consumer adaptation is needed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
