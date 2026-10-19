## What changed

`etaleInternalHomTensorShift_naturality` is proved from the existing
`CommShift₂` naturality of the derived tensor bifunctor. The proof also
establishes the generic adjunction transport and opposite-shift naturality
needed for `etaleInternalHomFlipShiftComponent_naturality`, which is now
proved. The raw opposite-shift component uses an explicit `eqToIso` transport;
the definition repair is recorded in
`coord/changes/etaleInternalHomFlipRawShiftComponent.md`.

The proof-only Sheaf/cochain imports from the original file were removed:
the completed proofs use only the existing derived tensor, adjunction, shift,
and opposite-category declarations already in the public imports.

## Proved and sorry left

Closed two of the five original holes:

- `AlgebraicGeometry.Etale.etaleInternalHomTensorShift_naturality`.
- `AlgebraicGeometry.Etale.etaleInternalHomFlipShiftComponent_naturality`.

Three original holes remain, with no new holes added:

- `AlgebraicGeometry.Etale.etaleInternalHomFlipShiftIso_zero`.
- `AlgebraicGeometry.Etale.etaleInternalHomFlipShiftIso_add`.
- `AlgebraicGeometry.Etale.etale_internalHom_pullback_triangle`.

## No longer needed

The following proof-only imports are no longer needed by the delivered
proofs and were removed from the module:

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SfHomTriangulated`
- `Sheaf.SixFunctors.EtaleHomComplexPullback`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

No DAG node or library module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly treated the compile service as unavailable;
the current candidate compiles successfully. The generic source-library
declarations provide tensor and adjunction shift naturality, but they do not
directly provide the two explicit coherence equalities for this repaired raw
component. The final triangle proof additionally needs the model-level
Hom-complex pullback argument described in the node; that interface is not
available in the current public imports.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
