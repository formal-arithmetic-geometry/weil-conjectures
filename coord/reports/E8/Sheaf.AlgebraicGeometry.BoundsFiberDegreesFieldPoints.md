## What changed

Proved `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_iff_fieldPoints` in
`Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`, preserving its complete signature
and public imports. Added the private proof import
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. Retained the used proof import
`WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange`.

For a field-valued point, construct the canonical isomorphism from the field to the
scheme residue field using `Ideal.algEquivResidueFieldOfField` and
`Scheme.Spec.residueFieldIso`. Its spectrum is exactly `fromSpecResidueField`.
The first projection of the fibre is then an isomorphism. Apply
`finite_fiber_degree_pullback`, transport finiteness by composing finite maps, and
transport dimension with the already proved `finrankΓ_eq_of_iso`. The reverse
implication is the definitional residue-field specialization.

Updated the item's DAG proof and proof dependencies to describe this argument. The
unit's statement and route are preserved. No definition, statement, or consumer changed.
The source read was Stacks `morphisms.tex`, Tag 03J5, statement and first two sentences
of its proof; the current blueprint unit and its DAG realization were also read.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_iff_fieldPoints`
(node `lem-weil-pbc-fibre-degree-bound-field-points`).
Added 0 holes. No `sorry` remains in the item or elsewhere in this delivery.
No new intermediate theorems or modules were added.

Validation: the final file compiled cleanly through `lcompile.py` in 3.6 seconds.
The delivery preflight will additionally check every introduced constant and its axioms.

The proof covers n=0 and empty fibres without extra hypotheses. The field isomorphism
uses the canonical residue map, so no identity or algebraic-closure assumption on the
field is made. Both the dimension comparison and the hypothesis use exactly the
structure morphisms in `finrankΓ`.

## No longer needed

- `lem-weil-pbc-finite-field-degree-isomorphism-transport`, module
  `Sheaf.AlgebraicGeometry.FiniteFieldDegreeIsomorphismTransport`: its full semilinear
  map and basis clauses are unnecessary. The dimension clause is supplied by the proved
  source-library `finrankΓ_eq_of_iso`, and Mathlib's finite-isomorphism/composition
  instances supply the finiteness clause.
- `lem-weil-pbc-field-base-point-fibre-isomorphism`, module
  `Sheaf.AlgebraicGeometry.FieldBasePointFibreIsomorphism`: the needed field isomorphism
  is constructed directly with Mathlib, and the fibre projection is invertible by the
  pullback-of-isomorphism instance. The additional comparison of every pullback
  presentation is unnecessary because the library's chosen fibre is used throughout.

These modules are not imported by the delivered file; the corresponding edges were
removed from its DAG proof dependencies. No existing import was removed and no module
was withdrawn. Other users, if any, remain entitled to use those declarations.

## Where the brief, the DAG or earlier work was wrong

No statement error. The DAG's proposed auxiliary theorems are substantially stronger
than this proof needs. Existing Mathlib and source-library APIs provide the required
parts directly. LeanFinder found finite-pullback ingredients but no equivalence;
Loogle did not index the project's `finrankΓ`; local source searches found the proved
`finrankΓ_eq_of_iso` and the field residue equivalence used here.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
