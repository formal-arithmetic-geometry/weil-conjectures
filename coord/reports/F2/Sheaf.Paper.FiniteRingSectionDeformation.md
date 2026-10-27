## What changed

The delivery proves eight original holes in Sheaf.Paper.FiniteRingSectionDeformation.
Geometry uses centred coordinates and the existing Rees geometry; the cone specification
uses its fixed comparison. The line and normalization proofs use local dualizing
comparisons and normalized shifted-line descent. Base-change and etale compatibility
follow from the canonical fibre squares and uniqueness. The bundle adjunct is invertible
by the proved unit integration adjunct theorem and functoriality at the zero section.

Repeated scalar-unit constructions have been replaced with existing canonical definitions
and explicit ordinaryFiniteUnit objects. The change is described in
coord/changes/F2-section-deformation-units.md. The consumers are checked unchanged against
the revised definitions; no forced adaptation is included.
The eight-proof module compiled in 39.7 seconds with the original VectorBundlePurity
module; the exploratory lower-shriek alias repair is not included.

## Proved and sorry left

Original holes: 11. Closed: 8. Added: 0. Split off: 0.
All names below are in AlgebraicGeometry.Etale.FiniteRingSectionDeformation.

Proved: geometry, coneBundleIso_spec, lines_and_fibres, existsUnique_normalized,
baseChange_compatibility, etaleNormalMap_spec, etale_compatibility, bundleAdjoint_isIso.

The original named statements coordinate_normalization, bundleOrientation_frames, and
bundleOrientation_purity still have their original sorry bodies. Their node is
lem-trf-finite-ring-section-deformation. No new hole is introduced elsewhere.

## No longer needed

No mathematical node or module is withdrawn. The coordinate-counit and bundle-orientation
dependencies remain in the DAG for the three unfinished original clauses, but unused
proof imports are removed from the delivered module. The unit route is preserved. Low-level
arguments already supplied by the stated dependencies are used through their interfaces.
The following original direct proof imports are redundant through the imports now used:

- Sheaf.AlgebraicGeometry.EtaleReesChart
- Sheaf.CategoryTheory.SiteConstantModuleHom
- Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
- Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
- Mathlib.AlgebraicGeometry.Morphisms.Smooth
- Mathlib.AlgebraicGeometry.Morphisms.Etale
- WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
- Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
- Mathlib.RingTheory.Noetherian.Defs
- Sheaf.AlgebraicGeometry.VectorBundleZeroSection
- WeilConjectures.Compactification.NagataCompactification
- Sheaf.AlgebraicGeometry.SmoothTensorDuality
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
- Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
- Sheaf.Paper.RingedTopoiDerivedTensorPullback
- Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
- Sheaf.AlgebraicGeometry.AffineSpaceTopTrace

The exploratory imports Sheaf.Paper.SectionCoordinateCounitNormalization and
WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit were also removed because
the delivered proofs do not use them.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing library already proves general-coefficient local
comparison, line-shape and normalization helpers inside NoetherianEtaleSectionSpecialization;
import all allows these proved helpers to be reused without duplicating their construction.
The original explicit scalar-unit expressions caused expensive definitional equality checks.
Writing the same coefficient unit explicitly and aliasing canonical maps resolves that
problem without changing their mathematical meaning. No source-library declaration is
changed, and no data is chosen from an arbitrary existence theorem.

The unfinished coordinate clause needs compatibility of the ordered coefficient descent
with the specified affine trace base change and its one-fibre normalization. The frame and
purity clauses were explored via adjunction naturality and the existing projection-unit
law, but those experimental proofs do not yet compile within the module limit and are
not included. Their original named statements and proof plans remain intact.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
