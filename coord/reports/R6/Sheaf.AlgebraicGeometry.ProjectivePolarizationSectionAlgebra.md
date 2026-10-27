## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.projectivePolarizationSectionAlgebra` with a proof of its unchanged statement. All helpers are private and proved in the item module. Additional namespace and notation openings are scoped to those private declarations; the public command interface is unchanged. No source-library declaration, public import, definition, statement, or consumer changes.

Finite generation uses the coordinate evaluation map onto L^r, Serre vanishing of its coherent kernel, and induction on degree. Low-degree pieces are finite-dimensional by the source library's projective coherent finiteness theorem. The scalar map is constructed explicitly through the structure map in degree zero. Affineness follows from the source library's affine-complement theorem after passing to common powers. The coefficient-hom and localization-bijectivity theorems give the precise fraction equivalence. Restriction surjectivity uses the closed-immersion unit-kernel theorem, Serre vanishing, and uniqueness of adjunctions to reach the normalized unit.

Updated the node proof, proof dependencies, and proof origin to match this route. No new modules. Added one DAG node attached to an existing proved source-library theorem.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Scheme.Modules.projectivePolarizationSectionAlgebra` (node `lem-sfb-projective-polarization-section-algebra`). All four clauses are proved. Holes closed: 1. Holes added: 0. Sorries left in delivered Lean files: none. Split off: none.

The complete module compiled without warnings through `lcompile.py` in 35.3 seconds. The geometric, recurrence, algebra and restriction helpers were also checked separately during diagnosis. The final delivery script performs its own compile, preflight and axiom checks. No test or supporting module is part of the delivery.

## No longer needed

The residue-class comparison with polynomial Proj, and the canonical map X→Proj(S) with its proper/open/closed-immersion argument, are unnecessary. Finite generation instead follows from the coordinate-evaluation kernel; affineness uses the existing affine-complement theorem directly, and the localization result fixes the same fraction formula. This prunes the following direct proof dependencies of this item (other library users may still need them):

- `lem-sfb-standard-proj-coherent-section-finiteness`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-pc-closed-immersion-coherent-cohomology`
- `lem-pc-twist-tensor`
- `lem-weil-pbc-invertible-pullback-tensor`
- `def-weil-pbc-proj-twisting-sheaf`
- `lem-pc-projective-space-coherent-finiteness`
- `lem-weil-pbc-proj-polynomial-twist-chart`
- `def-weil-pbc-ample-invertible-module`
- `lem-sc-ample-proj-local-chart`
- `def-weil-open-immersion`
- `def-nagata-affine-proj`
- `lem-sc-ample-proj-canonical-map`
- `lem-trf-proj-separated`
- `lem-weil-pbc-separated-cancellation`
- `lem-weil-pbc-proper-over-separated`
- `lem-weil-pbc-proper-immersion-closed`
- `def-pc-proj`
- `def-weil-closed-immersion`
- `lem-weil-pbc-coherent-serre-vanishing`
- `lem-weil-pbc-scheme-modules-enough-injectives`
- `lem-sc-global-sections-left-exact`

Removed proof imports:

- `Sheaf.AlgebraicGeometry.StandardProjCoherentSectionFiniteness`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`
- `WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart`
- `Sheaf.AlgebraicGeometry.AmpleProjLocalChart`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`
- `WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`
- `WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing`
- `WeilConjectures.AlgebraicGeometry.Modules.Ext`
- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`

Removed obsolete top-level `tool_uses` approvals for the corresponding pruned nodes: `lem-pc-closed-immersion-coherent-cohomology`, `lem-pc-twist-tensor`, `lem-weil-pbc-invertible-pullback-tensor`, `lem-pc-projective-space-coherent-finiteness`, `lem-weil-pbc-proj-polynomial-twist-chart`, `lem-sc-ample-proj-local-chart`, `lem-sc-ample-proj-canonical-map`, `lem-trf-proj-separated`, `lem-weil-pbc-separated-cancellation`, `lem-weil-pbc-proper-over-separated`, `lem-weil-pbc-coherent-serre-vanishing`, `lem-weil-pbc-scheme-modules-enough-injectives`, `lem-sc-global-sections-left-exact`, and `pqf-lem-coherent-ft-locnoeth`. The surviving approvals retain their original order.

The unused `polarization_ample` helper was also removed. No existing source-library declaration was deleted or replaced by a hole. The unit's realized statement/step fields are empty, and no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original planned route is substantially longer than necessary in the current source library: Serre vanishing already proves the needed multiplication recurrence, and the existing affine-complement and localization theorems avoid gluing a canonical Proj morphism. The given tensor-pullback polarization and restriction maps require explicit adjunction-uniqueness comparisons with the source library's ordinary pullback convention; these are included.

Edge cases were checked in the argument: an empty coordinate index forces an empty scheme and the epi/finite-sum argument remains valid; the affine-complement and coefficient statements cover zero sections, nilpotent sections, empty opens and zero localizations; no equality S_0=k, reducedness, connectedness, or r=1 is assumed. For an arbitrary positive r, subtraction in the recurrence strictly decreases degree and all finitely many residue classes are handled by the low-degree bound.


The launcher pause/resume reset the sandbox reference clock: the original `.budget.start` was 1792749696.3218505, while the resumed attempt uses 1792775817.0635858. This was launcher metadata; the worker did not edit it. Work and the original item were preserved across the interruption.

## New nodes

`lem-sfb-section-affine-complement-cover` records the exact general affine-complement theorem already proved as `AlgebraicGeometry.Scheme.Modules.isAffineOpen_compl_support_zeroLocus` in `WeilConjectures.AlgebraicGeometry.Modules.AffineComplement`. It is attached to that source declaration, without creating a duplicate module or statement or editing the source library. Its existing reciprocal-cover proof and Mathlib searches are recorded. The effective-Cartier-divisor lemma `lem-sc-ample-complement-affine` does not apply to arbitrary sections on nonreduced schemes, so it is not used as a substitute. Blueprint searches for affine nonvanishing loci found no matching blueprint statement. No change records are needed.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
