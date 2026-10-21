## What changed

Filled the proof of
`AlgebraicGeometry.exists_proper_geometricFibre_torsion_cohomology_bound` in
`Sheaf.AlgebraicGeometry.Sites.ProperGeometricFibreTorsionBound`, preserving its
signature and following all four steps of the existing DAG plan.

Choose the uniform ordinary-fibre dimension bound `e` from
`exists_fibre_dimension_bound` and take `c = 2 * e`. Factor each field-valued
point through its residue field using `Scheme.SpecToEquivOfField`. The iterated
pullback isomorphism and the field-extension clause of
`topologicalKrullDim_fieldExtension_and_denseOpen` transfer the bound to its
geometric fibre. For a nonempty fibre, its dimension is a natural number `d ≤ e`;
apply the existing finite-type torsion cohomological-dimension theorem with field
bound zero. Sectionwise torsion implies `Sheaf.IsTorsion` using
`isOfFinAddOrder_iff_zsmul_eq_zero` and
`Sheaf.IsTorsion.of_forall_isAddTorsion`. The positive integer degree is converted
to its natural-number value. For an empty fibre, use
`Scheme.Etale.isZero_sheaf_of_isEmpty` and preservation of zero objects by the
single-degree embedding and cohomology.

Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive`
for the zero-object argument. All public imports and existing declarations remain
unchanged. No definitions, statements, other modules or DAG routes changed.

Validation: the complete proof compiled cleanly through `lcompile.py` in 3.4 seconds
before import cleanup; the final reduced import list is checked by the delivery
compile. The empty base requires no point choice, empty fibres use the zero-sheaf
argument, and the dimension-zero case and section-dependent signed nonzero
annihilators are included without extra hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_proper_geometricFibre_torsion_cohomology_bound`
(node `lem-sfb-proper-geometric-fibre-torsion-bound`).

No `sorry` remains in the item. Added holes: zero. Split-off statements: zero.
The existing finite-type cohomological-dimension theorem is used as an input;
this report does not claim that all its transitive dependencies are proved.

## No longer needed

Removed the redundant private imports `Mathlib.Topology.KrullDimension` and
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`: both APIs are already
publicly exported by the retained proof dependencies.

No planned dependency node or module is pruned. Every mathematical ingredient of
the existing four-step DAG proof is used. The dense-open clause of
`lem-kun-dimension-extension` is unused, as the original plan specifies; its
field-extension clause is retained.

## Where the brief, the DAG or earlier work was wrong

None. The stated proof dependencies suffice; the empty-site argument is already
available as the proved theorem `Scheme.Etale.isZero_sheaf_of_isEmpty`.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
