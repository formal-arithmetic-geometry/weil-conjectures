## What changed

Replaced the hole in `difference_coordinate_section_identifications` by an assembly
of the two input equations and the normalized output composition equation. The general output
composition law is isolated as `normalizedE_comp_congr`, whose proof plan specializes
the existing Cartesian-tower comparison and transports its identity composites.
Pullback and comparison inverse image carry that arrow equality to the stated
small pro-etale equation. The two independent input calculations are new named statements
in their own modules. Their statements are stronger etale-origin arrow equalities,
before comparison inverse image, and each excludes the other input and the output.

Moved `normalizedE` verbatim into the first-input module to avoid an import cycle and
publicly reexported it. All original public imports and the main theorem signature are retained.
`Statement` now reads the identical geometry facts through conjunction projections
instead of a nested match, avoiding generated auxiliary proof names. Its arrow
formulas and hypotheses are unchanged. Change records:
`coord/changes/Y7-difference-coordinate-comparison-relocation.md` and
`coord/changes/Y7-difference-coordinate-statement-projections.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.difference_coordinate_section_identifications`
by decomposition. Added three holes, each the complete proof of a public theorem:

- `AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.difference_first_input_restriction`
  (`lem-pur-difference-first-input-restriction`): the projection-pasting and first input calculation.
- `AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.difference_second_input_restriction`
  (`lem-pur-difference-second-input-restriction`): restriction of normalized source base change for g.

- `AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.normalizedE_comp_congr`
  (`lem-pur-normalized-etale-comparison-composition`): the general normalized etale composition law.

Thus 1 original hole is reduced to 3 strict component holes; this is a decomposition,
not a net hole reduction. No hole remains in the item module. The three functorial assembly steps have complete proofs from the named component
statements. The generic composition lemma has no affine charts, sections, diagonals
or input equations in its hypotheses.
No data is chosen from a new existence assertion, and no definition contains a hole.

## No longer needed

Removed proof-only imports `Sheaf.Paper.DualizingSigmaCocycleLocality`,
`Sheaf.Paper.ExchangeFunctoriality`, `Sheaf.Paper.CohomologicalSmoothnessTheorem`,
`Sheaf.Paper.EtaleCartesianTowerTensorComparison`, and `Mathlib.CategoryTheory.Adjunction.Mates` from the assembly module. Their work is
not bypassed mathematically: the two input nodes retain the appropriate locality,
exchange, mate-pasting and smoothness proof dependencies. The assembly no longer needs
direct proof edges to `def-pur-co-smoothness`, `fix-lem-exchanges`,
`lem-weil-pbc-mate-pasting`, `thm-pur-cohomological-smoothness`, or
`lem-pur-dualizing-sigma-cocycle-locality`; those needed for the inputs move into their
respective proof dependencies. Removed the assembly's obsolete `fix-lem-exchanges`
tool-use approval. Its original generic exchange-tool use is retained mathematically
in the first-input node, at the same source step. No module is withdrawn or claimed globally unnecessary, and the
unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The Statement definition has a projection-only
refactor, recorded separately, because its original dependent match hid the
factorization proof behind an unstable generated name. The existing Cartesian-tower theorem applies with identity
projections, but using its composite-E clause directly still requires a calculation of
the exceptional congruences for identity composites. That calculation is isolated in
the general normalized composition law. The first input still needs projection mate pasting,
and the second still needs normalized source base change followed by section restriction;
those are recorded separately rather than hidden in a partial proof.

The edge cases are retained: zero d or e does not force the translated etale maps to
be identities, and no step asserts z_e P_e=id. Empty affine schemes use the same
polynomial and pullback equations. No orientation or Tate trivialization is selected.

## New nodes

`lem-pur-difference-first-input-restriction` isolates refinement Steps 2--4:
projection base-change pasting, normalized source locality and restriction along Delta_f.
Its docstring and node give the complete argument in words. The normalized comparison
definition is relocated verbatim to the same module.

`lem-pur-difference-second-input-restriction` isolates refinement Step 5:
normalized source base change for G_g, pulled along s with the actual translated square.
Both nodes use the original composition-coherence Step 1 source, retain empty and zero
block cases, and record LeanSearch, LeanFinder and source/blueprint searches.

`lem-pur-normalized-etale-comparison-composition` isolates the general output
composition calculation, before any diagonal restriction. Its proof follows normalized
rho composition and exceptional mate pasting, or the identity-projection specialization
of the existing Cartesian-tower theorem. It has no dependence on either input equation.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
