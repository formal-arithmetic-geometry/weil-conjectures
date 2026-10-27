## What changed

Proved `AlgebraicGeometry.ProEtale.GaloisContinuousSection.section_naturality` in
`Sheaf.Paper.GaloisContinuousSectionNaturality`, preserving its statement, both section-ring
abbreviations, and the public import. Added only proof imports and private proved helpers.
The three equivalences are actual constructions normalized by the existing canonical comparison.
Coefficient compatibility follows from equality of adjuncts. All simplex maps are handled
by vertex projections and a telescoping product identity, including the moved base vertex.
The pullback clause uses the existing canonical monoidal comparison instances.

Updated the item's DAG proof and proof dependencies to match these constructions.
`CondensedRing.reconstructedRingIso` is used as a generic tool from
`def-weil-pbc-continuous-coefficient-module-encoding`: it merely converts the already constructed
internal ring morphism into its sectionwise ring equivalence and does not replace the unit route.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.GaloisContinuousSection.section_naturality`
(node `lem-sfb-galois-continuous-section-naturality`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the delivered module.
All private helpers, including the locally constant pushout and the simplex-coordinate
calculation, are proved. This is a proof from the existing library declarations; it does not
claim that the transitive dependencies of the library have no remaining holes.

## No longer needed

The proof does not need `lem-weil-pbc-finite-affine-coproduct-spectrum` or
`lem-weil-pbc-spec-small-colimit-limit`: a direct pushout universal property identifies the
profinite field test scheme with the locally constant spectrum.
It does not invoke `lem-sfb-separable-cover-finite-coordinates` or
`lem-weil-pbc-weakly-etale-composition-base-change`: the statement already supplies the
actual nerve objects and their coordinates.
The proof does not call `FieldSeparableCech.coordinates`,
`FieldSeparableCech.face_coordinates`, or `FieldSeparableCech.section_coordinates`.
In particular no proof edge to the parent `lem-sfb-field-separable-cech-coordinates` is added.
These declarations and modules remain available for other consumers; none is withdrawn.

The former direct import of
`WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant` is replaced by its
`LocallyConstantHom` extension, whose actual map and extensionality lemmas are used.
Removed the redundant direct imports `Mathlib.AlgebraicGeometry.Limits`,
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, and
`Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`. The actual pullback and limit API is
already publicly supplied by the existing statement imports.
No module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The finite-partition construction in the DAG is longer than necessary with the existing
`LocallyConstant.liftPrimeSpectrum` and `ringHom_ext_of_specMap` API.
Calling the parent's `FieldSeparableCech.face_coordinates` would introduce a proof dependency
back to a node already depending on this item. The delivery instead derives that equation
privately from the vertex-coordinate hypothesis, preserving the unit route.

Validation: the full proof compiled in 30.1 seconds. The sole style warning was removed
before the delivery compile and its declaration/axiom preflight.

The sandbox contained an unfinished proof draft on resumption. It was checked and repaired
against the current sources; no prior delivery was repeated.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
