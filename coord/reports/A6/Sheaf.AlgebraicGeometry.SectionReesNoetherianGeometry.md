## What changed

Completed all four proofs in `Sheaf.AlgebraicGeometry.SectionReesNoetherianGeometry` without changing any existing declaration signature, definition, or public import. Added only proved private augmentation, etale-composition, open-Noetherianity and compactification helpers, plus private proof imports. Updated the existing node's proof and proof dependencies to describe the implemented route.

`geometry` uses the stated centred-coordinate theorem for the conormal rank and canonical symmetric comparison. It maps that comparison through the actual relative-Spec anti-equivalence and composes with the normalized Rees comparison; counit naturality and uniqueness of the symmetric augmentation prove compatibility with the specified zero sections. The completed source-library deformation API supplies smoothness and the three fibre pullbacks. Finite-type permanence gives Noetherian spaces, and Nagata gives compactifications. The bundle projection is transported from the zero-fibre projection along the canonical isomorphism. The punctured section is a pullback lift with all three equations proved.

`affine_chart` uses the existing etale Rees theorem for the tensor map and coordinate equations. Etale algebra base change proves the unlifted chart map etale; polynomial Noetherianity and Nagata handle its structural composites and all stated open restrictions. The actual deformation open is identified with its Rees spectrum by the published gluing cocone.

`chart_cover` lifts each point outside the punctured locus to the zero fibre. Its projection factors through the section, and the stated centred-coordinate cover supplies the required ambient chart. `chart_compactifications` applies the geometry theorem, permanence under composition, Noetherianity of opens, and Nagata.

The remote delivery compiler checked all four proof bodies in 17.6 seconds; a subsequent delivery compile and axiom probe passed without warnings. Preflight then flagged helper-only `variable` commands as visible interface changes. Their binders were moved into the individual private helper declarations, removing those commands and preserving the module interface.

The generic symmetric-algebra universal property (`lem-weil-pbc-quasi-coherent-symmetric-algebra-core`) is used as a tool for equality of the two canonical augmentations; it supplies no new geometric hypothesis. The generic affine gluing leaf (`lem-weil-pbc-relative-glueing-affine-opens`) records the existing chart API. The unit route is preserved.

## Proved and sorry left

Closed four holes, by declaration name:

- `AlgebraicGeometry.SectionReesNoetherianGeometry.geometry`
- `AlgebraicGeometry.SectionReesNoetherianGeometry.affine_chart`
- `AlgebraicGeometry.SectionReesNoetherianGeometry.chart_cover`
- `AlgebraicGeometry.SectionReesNoetherianGeometry.chart_compactifications`

Zero holes remain in the item, zero holes were added, and zero statements were split off. The existing centred-coordinate theorem is used as its declared dependency, as required by stage 3.

## No longer needed

Removed the direct proof imports of `Sheaf.AlgebraicGeometry.CoherentFiniteType`, `Sheaf.RingTheory.ReesAssociatedGradedChart`, and `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`. Their nodes `pqf-def-coherent`, `lem-pur-rees-associated-graded-chart`, and `lem-weil-pbc-relative-spec-base-change` are no longer direct dependencies of this proof: the published deformation and normalized comparison APIs already provide the needed geometric maps and identities. No globally unused declaration or source module is withdrawn; these results may remain needed by those APIs or other consumers.

Removed redundant direct imports of `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`, `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `Mathlib.RingTheory.Noetherian.Defs`, and `WeilConjectures.Compactification.NagataCompactification`; the retained public imports already provide their used declarations and instances.

The local polynomial-trivialization argument for the bundle's finite-type and Noetherian properties is unnecessary: the zero-fibre pullback and the canonical bundle isomorphism transport them directly. The affine-space smoothness instance is retained for the affine line.

The source import-graph comparison removes three modules from this item’s closure and, at the checked repository snapshot, from the targets’ closure: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`, and its dependency `Sheaf.AlgebraicGeometry.StructureAlgebraPullbackTransport`. `ReesAssociatedGradedChart` remains reachable through the normalized comparison API. These modules are pruned by import removal, not withdrawn from the library.

## Where the brief, the DAG or earlier work was wrong

The old plan substantially repeated geometry already proved in `WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`: `smoothOfRelativeDimension_deformationSpaceProj`, the separated and quasi-compact instances, the fibre pullbacks, and the section compatibility equations. Reusing those completed proofs shortens the argument without altering any source declaration or the unit route. No mathematical statement repair was necessary.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
