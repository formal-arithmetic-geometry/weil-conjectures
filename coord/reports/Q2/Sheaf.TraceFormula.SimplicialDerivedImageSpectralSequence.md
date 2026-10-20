## What changed

Restored the quarantined module for its assigned rework import failure. Replaced the
broad DoubleComplexTotal public import with CanonicalFiltration and explicitly imported
Mathlib.Algebra.Homology.SpectralSequence.Basic. Removed unused private proof imports.
All definitions and theorem signatures are preserved from the archive.

Proved AlgebraicGeometry.simplicial_etale_augmentation_component by installing restriction's
injective-preservation consequence and applying rightDerivedFunctorPlusCompIso and its
unit equation. No intermediate statement was added.

Change record: coord/changes/Q2-simplicial-derived-image-import-repair.md.

## Proved and sorry left

Original archive: nine holes. Closed one:
AlgebraicGeometry.simplicial_etale_augmentation_component.
Added zero holes; split off zero statements. Eight original holes remain, all attached
to lem-trf-simplicial-derived-image-spectral-sequence:

- AlgebraicGeometry.simplicial_etale_restriction_exact
- AlgebraicGeometry.simplicial_etale_morphism_direct_image
- AlgebraicGeometry.simplicial_etale_derived_component
- AlgebraicGeometry.simplicial_derived_image_spectral_sequence
- AlgebraicGeometry.simplicial_etale_direct_image_composition
- AlgebraicGeometry.simplicial_etale_composite_adjunction_normalization
- AlgebraicGeometry.simplicial_etale_augmented_diagram_comparison
- AlgebraicGeometry.simplicial_etale_augmented_adjunction_normalization

This delivery repairs the assigned quarantined import failure; the eight remaining
proofs are unchanged. The component comparison is proved relative to the existing
restriction theorem, whose original hole remains in the list above.

## No longer needed

Removed imports:

- Sheaf.CategoryTheory.DoubleComplexTotal
- Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
- WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Sheaf.CategoryTheory.KInjectiveComputes
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
- WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
- Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite
- Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
- Sheaf.CategoryTheory.RingedSiteModules
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

These imports provide no declaration used by the retained proof or statements.
No modules are withdrawn and no DAG nodes are deleted or declared mathematically
unnecessary: the unchanged proof plans for the original remaining holes still describe
their dependencies. The unit route and item attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The item was absent from lean/ because it was quarantined, not withdrawn. Restored its
complete archive. The rework error was reproduced before editing, then eliminated by
the canonical filtration import. The old broad import also supplied spectral-sequence
notation indirectly; the required Mathlib import is now explicit.

Validation: the repaired item compiled cleanly on the server (5.1 seconds); its proved
comparison also compiled in a two-module consumer check (8.4 seconds). The sole archived
consumer was compiled in that same dependency-ordered check. It failed on a separate
pre-existing collision between Sheaf.Algebra.Homology.DerivedInternalHom and
WeilConjectures.Algebra.Homology.DerivedInternalHom, before elaborating its declaration.
That consumer mentions no removed double-complex declaration. Its archive is untouched;
this packet does not claim that unrelated quarantine repair or a clean consumer build.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
