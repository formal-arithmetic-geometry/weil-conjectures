## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_coordinate_chart_finite_dimension_witness`
without changing its signature. The proof selects a generic point of a support
component, transports maximality through flat maps, and uses coheight to compare
stalk dimensions with fibre stalk dimensions. It retains the explicit polynomial
origin model required by the statement.

Added `Sheaf.AlgebraicGeometry.CoordinateSubspaceGenericStalk`, proving the separate
ambient coordinate-subspace stalk calculation. Its proof identifies affine-space
fibres with affine spaces over the base residue field, computes the coordinate
prime through `AffineSpace.SpecIso`, and applies polynomial localization and
transitivity of prime localization. All other supporting lemmas are proved private
helpers in the two delivered modules. The new proof imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` supply the existing
coheight theorem and smooth affine-space projection instance.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Hom.exists_coordinate_chart_finite_dimension_witness`
(node `lem-pur-coordinate-chart-finite-dimension-witness`).

Added no holes. The new theorem
`AlgebraicGeometry.coordinate_subspace_generic_fiber_stalk`
(node `lem-pur-coordinate-subspace-generic-stalk`) and all private helpers are proved.
The delivery contains zero `sorry` proofs. Both modules compile without warnings.

## No longer needed

Removed proof imports of
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`WeilConjectures.RingTheory.Etale.LocalDimension` and
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`.

The proof no longer uses these planned dependencies:

- `lem-weil-pbc-prime-contains-minimal-prime`: a generic support-component point
  maps to a minimal base point by flatness, so no polynomial-prime selection is
  needed.
- `lem-weil-pbc-etale-morphism-open-map`: the proof uses flatness and lifting of
  generalizations. Affine-space fibre irreducibility uses the projection's own
  open-map theorem.
- `lem-sc-etale-local-dimension`: replaced by the proved scheme-level
  `Scheme.Hom.coheight_apply_of_flat`.
- `lem-sbc-scheme-fibre-stalk-quotient`: replaced by equality of coheights through
  the fibre embedding over a maximal point of the specialization order.

Removed the obsolete `tool_uses` approvals for
`lem-sc-etale-local-dimension` and `lem-sbc-scheme-fibre-stalk-quotient`; retained
the polynomial-origin approval.

No upstream declaration or module is removed. These are dependencies pruned from
this proof, and may remain needed by other parts of the project.

## Where the brief, the DAG or earlier work was wrong

The theorem and its edge cases are correct. The DAG's steps marked elementary
hide substantial polynomial-localization and scheme-fibre comparison code.
The explicit ambient stalk calculation is a genuine separate result, now proved
in its own module. Its statement does not require the base prime to be minimal.

The supplied nine-step route is longer than necessary for the dimension transfer:
a fibre embedding over a maximal point of the specialization order contains all
generalizations, so its coheight agrees with that in the total space. This avoids
nil-ideal calculations and the fibre-stalk quotient theorem. Neither the unit's
statement nor its route changes.

## New nodes

`lem-pur-coordinate-subspace-generic-stalk`, in `sec-smooth-purity`, records the
proved ambient affine-space fibre stalk at a generic coordinate-subspace point.
It realizes steps 3--4 of the original witness argument, with no dimension claims
and no minimal-prime hypothesis. The calculation covers `a = 0` and `b = 0` by the
same polynomial and localization APIs. There are no change records because no
existing public statement or definition is changed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
