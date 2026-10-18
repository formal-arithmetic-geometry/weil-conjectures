## What changed

Proved `AlgebraicGeometry.finite_over_projective_affineLocally` with its existing signature
unchanged. The existing, fully proved source theorem
`ProjectiveSpace.exists_isClosedImmersion_of_isFinite` already implements the blueprint's
coordinate-section argument over an affine base. A private proved helper normalizes its
finite coordinate type: use `ProjectiveSpace.exists_finite_index_iso` for a nonempty type;
for an empty coordinate type the source scheme is empty and its unique map to projective
zero-space is a closed immersion. Properness supplies the quasi-compactness field of
`IsProjective` through `IsHProjective.isProjective`.

For each affine open, `ProjectiveSpace.isPullback_liftBaseChange` transports the original
closed embedding to the restricted base. Finiteness restricts, and `morphismRestrict_comp`
identifies the composite. The affine-base global clause applies the helper directly.
The empty affine open, empty source and empty coordinate type are included. Neither
Noetherianity nor compactness is needed by the source theorem, but the original binders
are preserved.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism` and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso`. Updated the item's DAG
proof, proof dependencies and origin to record reuse, normalization and restriction. The
finite-index theorem is a proved tool in another unit; no unit statement or step is
bypassed (this unit's `realized.statement` and `realized.steps` are empty).

Validation: remote single-file compilation passed without warnings (3.1 seconds).
A separate remote probe passed (5.0 seconds) and `#print axioms` for the delivered theorem,
the existing finite-cover theorem, and the finite-index theorem each listed exactly
`propext`, `Classical.choice`, and `Quot.sound`. No consumer adaptations or definition
changes are required; all public imports and existing signatures remain unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.finite_over_projective_affineLocally`
(node `lem-fin-finite-over-projective`).

Added holes: 0. Remaining holes in the delivered module: 0. Split-offs: 0.
The private helper `finite_over_projective_embedding_affine` is fully proved.
This is a proof, not a decomposition, and its axiom audit has no `sorryAx`.

## No longer needed

Removed direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`
- `Sheaf.AlgebraicGeometry.Ample`
- `Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase`
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.Ample`
- `WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`

The following existing DAG proof dependencies and their top-level tool approvals are
removed because the native coordinate-section theorem needs neither the relative-Proj
interface nor the absolute `IsAmple` interface:

- `def-nagata-relative-projective-space`
- `lem-weil-pbc-invertible-pullback-tensor`
- `def-weil-pbc-ample-invertible-module`
- `lem-weil-pbc-ample-very-ample-immersion-affine-base`

The native source theorem still uses twisting modules, affine charts and the properness
argument internally; those corresponding dependencies remain recorded. Direct imports of
Mathlib properness and native projective space/twist are redundant with the new imports.
No global claim is made that another target branch ceases using these modules.

For completeness, the source-level import closure of this item loses these project
modules (computed by traversing every local library import before and after the change):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
- `Sheaf.AlgebraicGeometry.AffineCapSectionOpen`
- `Sheaf.AlgebraicGeometry.AffineCapSectionOpenAlgebra`
- `Sheaf.AlgebraicGeometry.AffineCapSectionOpenDictionary`
- `Sheaf.AlgebraicGeometry.AffineLocalizationSheafification`
- `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf`
- `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification`
- `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalization`
- `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalizationZero`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.AffineOpenSectionFractionLocalization`
- `Sheaf.AlgebraicGeometry.AffineSectionLocalization`
- `Sheaf.AlgebraicGeometry.Ample`
- `Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase`
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero`
- `Sheaf.AlgebraicGeometry.CohomologyFractionPresentation`
- `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing`
- `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux`
- `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`
- `Sheaf.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing`
- `Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators`
- `Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion`
- `Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization`
- `Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`
- `Sheaf.AlgebraicGeometry.InvertSCOhomology`
- `Sheaf.AlgebraicGeometry.InvertibleSectionLocalization`
- `Sheaf.AlgebraicGeometry.LocalUniformHigherDirectImageBound`
- `Sheaf.AlgebraicGeometry.LocalizingPrincipalCoverGluing`
- `Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology`
- `Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison`
- `Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus`
- `Sheaf.AlgebraicGeometry.NonvanishingLocusRestrict`
- `Sheaf.AlgebraicGeometry.OpenCohomologyFractionZeroComparison`
- `Sheaf.AlgebraicGeometry.OpenCohomologyZeroRestriction`
- `Sheaf.AlgebraicGeometry.OpenCohomologyZeroSections`
- `Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison`
- `Sheaf.AlgebraicGeometry.OpenSectionFractionPresentation`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersectionProperty`
- `Sheaf.AlgebraicGeometry.RelativeProjData`
- `Sheaf.AlgebraicGeometry.RelativeProjExists`
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`
- `Sheaf.AlgebraicGeometry.ResolutionOpenComparisonMap`
- `Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionCore`
- `Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionNatural`
- `Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison`
- `Sheaf.AlgebraicGeometry.ResolutionOpenScalarCore`
- `Sheaf.AlgebraicGeometry.ResolutionSectionsHomologyScalar`
- `Sheaf.AlgebraicGeometry.ResolutionUnitTwistComparison`
- `Sheaf.AlgebraicGeometry.RestrictedResolutionSectionsExist`
- `Sheaf.AlgebraicGeometry.RingSheafificationRestrictedStalks`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.SectionClearingDenominatorsQCQS`
- `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalDenominators`
- `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization`
- `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalTorsion`
- `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons`
- `Sheaf.AlgebraicGeometry.SectionCohomologyUntwistedComparisons`
- `Sheaf.AlgebraicGeometry.SectionFractionPresentation`
- `Sheaf.AlgebraicGeometry.SectionFractionRestrictionMap`
- `Sheaf.AlgebraicGeometry.SectionRestrictionSTorsion`
- `Sheaf.AlgebraicGeometry.SeparatedOpenInduction`
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonMap`
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonStalks`
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison`
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`
- `Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition`
- `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction`
- `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN`
- `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionT`
- `Sheaf.AlgebraicGeometry.TensorUnitPowerScalar`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryExact`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryNaturality`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundarySquareNaturality`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`
- `Sheaf.Paper.CohomologyFractionComparison`
- `Sheaf.Paper.CohomologyFractionMayerVietorisExact`
- `Sheaf.Paper.CohomologyFractionMayerVietorisSquares`
- `Sheaf.Paper.CohomologySectionDivision`
- `Sheaf.Paper.DerivedHomMayerVietoris`
- `Sheaf.Paper.HigherDirectImagePresheaf`
- `Sheaf.Paper.LocalizedCohomologyMayerVietoris`
- `Sheaf.Paper.NonvanishingSectionTrivializes`
- `Sheaf.Paper.PQFCohomology`
- `Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership`
- `Sheaf.RingTheory.FreePrimeMembership`
- `Sheaf.RingTheory.SymmetricAlgebraBaseChange`
- `Sheaf.Topology.ModuleMayerVietoris`
- `Sheaf.Topology.OpenModuleCohomology`
- `Sheaf.Topology.OpenModuleCohomologyLocalIso`
- `Sheaf.Topology.PresheafModuleStalkFunctor`
- `Sheaf.Topology.RestrictInjectiveResolution`
- `Sheaf.Topology.RingedSpaceModuleCohomology`
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRingsPresheaf`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`
- `WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside`
- `WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitEpi`
- `WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitFaithful`
- `WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso`
- `WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitMono`
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`
- `WeilConjectures.Algebra.Homology.OpenCoverAdjunctionTriangle`
- `WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact`
- `WeilConjectures.Algebra.Homology.OpenCoverMateModuleShortExact`
- `WeilConjectures.Algebra.Homology.OpenCoverMateModuleShortExactCore`
- `WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation`
- `WeilConjectures.Algebra.Homology.OpenExtensionCounitStalk`
- `WeilConjectures.Algebra.Homology.OpenHomTriangleRealization`
- `WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`
- `WeilConjectures.AlgebraicGeometry.Ample`
- `WeilConjectures.AlgebraicGeometry.AmpleFinitePowerCover`
- `WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase`
- `WeilConjectures.AlgebraicGeometry.AmpleSeparated`
- `WeilConjectures.AlgebraicGeometry.Coherent`
- `WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Field`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MayerVietoris`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.ProjectionFormula`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Restrict`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Exact`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Flasque`
- `WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Leray`
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`
- `WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero`
- `WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Restriction`
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`
- `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`
- `WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices`
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`
- `WeilConjectures.AlgebraicGeometry.ModuleCechVanishingCriterion`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`
- `WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`
- `WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSectionsBijective`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic`
- `WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveCechVanishing`
- `WeilConjectures.AlgebraicGeometry.ModuleSectionsAcyclicOfCohomologyVanishing`
- `WeilConjectures.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.AlgebraicGeometry.Modules.AffineComplement`
- `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`
- `WeilConjectures.AlgebraicGeometry.Modules.Ext`
- `WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction`
- `WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula`
- `WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroInside`
- `WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroOutside`
- `WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroUnitStalks`
- `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`
- `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor`
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic`
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free`
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree`
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Presheaf`
- `WeilConjectures.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
- `WeilConjectures.AlgebraicGeometry.Modules.QcqsSections`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
- `WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber`
- `WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward`
- `WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`
- `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
- `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso`
- `WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen`
- `WeilConjectures.AlgebraicGeometry.NonvanishingCommonDegree`
- `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`
- `WeilConjectures.AlgebraicGeometry.NonvanishingTransitionFunctions`
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`
- `WeilConjectures.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Affine`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.ChartBaseChange`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.GradedAlgebraData`
- `WeilConjectures.AlgebraicGeometry.ResolutionSectionsHomologyScalar`
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`
- `WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus`
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`
- `WeilConjectures.AlgebraicTopology.SetCechNerveFreeResolution`
- `WeilConjectures.CategoryTheory.Abelian.DimensionShifting`
- `WeilConjectures.CategoryTheory.Abelian.ExtEpiEffacement`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeDefectFactorization`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeDegreewiseMap`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeHomotopyCorrection`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLift`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedRows`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.CategoryTheory.DeltaFunctor`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
- `WeilConjectures.CategoryTheory.EffaceableDeltaFunctorSuccessor`
- `WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal`
- `WeilConjectures.CategoryTheory.EffacingSequenceComparison`
- `WeilConjectures.CategoryTheory.EffacingSequencePushout`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.AcyclicSwallowing`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGenerated`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGeneratedCover`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeCardinal`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeEnlargement`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeGeneratingSet`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeSmallObject`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Subcomplex`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.CategoryTheory.InjectiveModulePresheaf`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`
- `WeilConjectures.CategoryTheory.PresheafChangeOfRingsAdjunction`
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.SiteCechComplex`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroExact`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation`
- `WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`
- `WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechComplex`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechExtEdgeInjective`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechExtEdgeKernel`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechSheafAugmentationExact`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechSheafHomComparison`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechSheafPositiveExact`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechSheafResolution`
- `WeilConjectures.CategoryTheory.Sites.PresheafCechVanishingCriterion`
- `WeilConjectures.CategoryTheory.Sites.PresheafFreeExtLocalKilling`
- `WeilConjectures.CategoryTheory.Sites.PresheafFreeNerveComparison`
- `WeilConjectures.CategoryTheory.Sites.PresheafFreeNerveExact`
- `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`
- `WeilConjectures.CategoryTheory.SpectralSequence.LowDegree`
- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`
- `WeilConjectures.FromJoel.Algebra.Homology.Double`
- `WeilConjectures.FromJoel.Algebra.Homology.DoubleHomology`
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`
- `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv`
- `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexLimits`
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`
- `WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex`
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim`
- `WeilConjectures.FromJoel.CategoryTheory.GradedObject.Bifunctor`
- `WeilConjectures.FromJoel.CategoryTheory.GradedObject.Colimits`
- `WeilConjectures.FromJoel.CategoryTheory.Limits.ExactFunctor`
- `WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism`
- `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts`
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`
- `WeilConjectures.Mathlib.Algebra.Category.Grp.Preadditive`
- `WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.Algebra.Homology.Double`
- `WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend`
- `WeilConjectures.Mathlib.Algebra.Homology.ExactSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian`
- `WeilConjectures.Mathlib.Algebra.Homology.HomologySequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Ab`
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`
- `WeilConjectures.Mathlib.Algebra.Homology.SingleHomology`
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`
- `WeilConjectures.Mathlib.Algebra.Module.LocalizedModule.Exact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.CommSq`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`
- `WeilConjectures.Mathlib.CategoryTheory.Generator.Abelian`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution`
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.HasCardinalLT`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`
- `WeilConjectures.Mathlib.RingTheory.PicardGroup`
- `WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT`
- `WeilConjectures.Mathlib.Topology.Sheaves.Flasque`
- `WeilConjectures.Topology.InverseImageModule`
- `WeilConjectures.Topology.InverseImageOperationExt`
- `WeilConjectures.Topology.InverseImagePresheafModule`
- `WeilConjectures.Topology.InverseImageStalk`
- `WeilConjectures.Topology.OpenModuleCohomology`
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`
- `WeilConjectures.Topology.PresheafStalkTensor`
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`
- `WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`
- `WeilConjectures.Topology.SheafCokernelLocalImage`
- `WeilConjectures.Topology.Sheaves.Cech`
- `WeilConjectures.Topology.Sheaves.CechCohomology`
- `WeilConjectures.Topology.Sheaves.CechComparison`
- `WeilConjectures.Topology.Sheaves.CechCriterion`
- `WeilConjectures.Topology.Sheaves.CechFlasque`
- `WeilConjectures.Topology.Sheaves.MayerVietorisVanishing`
- `WeilConjectures.Topology.Sheaves.PushforwardCohomology`
- `all`

## Where the brief, the DAG or earlier work was wrong

The stage-2 attachment overlooked the existing, fully proved affine-base theorem
`AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_of_isFinite` in the source
library. Its docstring already names this blueprint node. Consequently the substantial
coordinate-section argument does not need to be formalized again, and the imports of the
relative-Proj and absolute-ampleness interfaces are unnecessary. The corrected local
statement is respected; no claim of a global embedding over an arbitrary base is made.
The existing docstring retains the original mathematical plan, which the source theorem
implements using its native ample-family formulation.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
