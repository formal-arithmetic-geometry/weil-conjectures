## What changed

Proved `AlgebraicGeometry.geometricallyReduced_iff_isReduced_pullback_algebraicClosure`
in `Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest` with its exact
original signature. Added the private proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
The reverse direction uses its already proved `GeometricallyReduced.of_perfectField`
over the chosen closure, embeds that closure into `AlgebraicClosure K` for each
extension K/k, compares the iterated pullbacks, and descends reducedness along
the quasi-compact scheme-theoretically dominant projection to X_K.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
No definition, public import, declaration signature or existing docstring changed.

Single-file compilation passed (8.9 seconds in the verification with the axiom
probe). `#print axioms` for the completed theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The probe was removed from the delivery.
The proof allows arbitrary schemes and field extensions, including the empty
scheme, and uses no finite-type or quasi-compactness assumption on X.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.geometricallyReduced_iff_isReduced_pullback_algebraicClosure`
(node `lem-trf-geometric-reducedness-algebraic-closure-test`).
Added 0 holes; split off 0 statements; 0 sorry declarations remain in the item
or are added by this delivery. This is a complete proof from sorry-free results,
not a decomposition.

## No longer needed

Removed the private imports `Mathlib.RingTheory.Nilpotent.GeometricallyReduced`
and `Sheaf.TraceFormula.ReducednessTensorChosenAlgebraicClosure`.
Removed the redundant direct private import `Mathlib.AlgebraicGeometry.Pullbacks`;
the required pullback API is provided by the new proved-source import.

The proof no longer uses `lem-trf-reducedness-tensor-chosen-algebraic-closure`
or its module `Sheaf.TraceFormula.ReducednessTensorChosenAlgebraicClosure`.
It also no longer uses `lem-trf-affine-geometric-reducedness-criterion`.
Both nodes were removed from this item's proof dependencies. This does not
assert that other consumers can drop them, and no module is withdrawn.
The three original affine-cover/tensor-spectrum/reduced-affine nodes remain
as dependencies because they occur inside the reused perfect-field proof.

## Where the brief, the DAG or earlier work was wrong

The recorded Mathlib match for `lem-trf-affine-geometric-reducedness-criterion`
uses an older theorem name and overstates what the pinned library supplies.
The current `Algebra.isGeometricallyReduced_field_iff` characterizes Mathlib's
algebraic-closure-based algebra predicate; arbitrary field extensions are an
explicit TODO in that file, while its reduced tensor-product instance assumes
an algebraic extension. Thus the old step 3 was not justified by its stated
Mathlib leaf. We avoid that gap completely through the already proved general
perfect-field scheme theorem, Stacks Tag 020I, and descent (081I/056B).
The item's statement remains true and unchanged; no dependency statement was
modified. The original declaration docstring's historical proof plan is retained;
the updated DAG records the proof implemented here. The unit's realized list is
empty for this auxiliary node, and no unit statement or step is bypassed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
