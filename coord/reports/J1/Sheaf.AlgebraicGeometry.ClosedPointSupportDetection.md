## What changed

Proved `AlgebraicGeometry.Etale.isZero_iff_cohomology_of_support_closedPoints` with its signature unchanged. Four proved private helpers implement support transfer along etale maps, an affine covering by compact objects, the ordinary/derived cohomology convention comparison, and zero detection for globally generated sheaves. The proof follows Stacks 0F1G's general unbounded argument using the existing acyclic-basis, closed-support vanishing, and global-generation theorems. The unit route is preserved.

Added proof imports:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`
- `WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation`

Updated the existing node's proof and dependencies to match the implementation. No statement or definition changes and no consumer adaptations. Single-file server compilation passed cleanly (4.4 seconds in the latest check before whitespace-only cleanup). No declaration in this delivery contains `sorry`; the imported existing theorems remain separate proof obligations.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.isZero_iff_cohomology_of_support_closedPoints` (node `lem-kun-0f1g`). Holes added: zero. Holes left in the item module: zero. Split off: zero. All four private helpers are proved.

## No longer needed

Removed proof imports (some Mathlib APIs remain available through retained imports):

- `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.RingTheory.Unramified.LocalRing`
- `Mathlib.RingTheory.Unramified.Locus`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Sheaf.AlgebraicGeometry.ClosedPointField`
- `Sheaf.AlgebraicGeometry.EtaleGloballyGenerated`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`

Pruned from this node's explicit proof dependencies:

- `lem-kun-stalks-of-cohomology`
- `lem-kun-etale-lfp`
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-kun-stalk-as-pullback`
- `lem-weil-pbc-etale-algebra-residue-field-separable`
- `lem-kun-closed-point-field`

The geometric-stalk/cohomology comparison is unnecessary because complex support is defined as the union of homology-sheaf supports. The derived geometric-stalk-as-pullback theorem and residue-field argument are replaced by the proved sheaf pullback/stalk isomorphism and discrete closed fibres. Affine compactness, etale composition, and locally finite-type composition use Mathlib instances directly. The unbounded basis theorem already takes inverse image as restriction. The identity inverse-image comparison remains used through upperStarId.

These are local dependency/import removals; no claim is made that the named modules are globally unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original proof's affine residue-field calculations were longer than necessary: Mathlib's discrete-fibre theorem and closedness of the fibre over a closed point imply closedness of each point in that fibre. The ordinary Sheaf.H/derived cohomology convention bridge also required the existing node `new-sheaf-cohomology-derived-evaluation`, now recorded.

The proof applies to unbounded complexes, including zero sheaves, empty support, and empty schemes: the cover and comparison arguments impose no nonemptiness or boundedness conditions. No target signature, hypothesis or conclusion changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
