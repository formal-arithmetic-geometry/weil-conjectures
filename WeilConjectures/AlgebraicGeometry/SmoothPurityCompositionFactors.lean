/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SecSmoothPurity.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.TowerAdjointCompositorRealization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement
import all WeilConjectures.AlgebraicGeometry.SmoothTensorDuality
import all WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import all WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionCoherence
import all WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import all WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import all Mathlib.CategoryTheory.Triangulated.Yoneda
import all WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import all Mathlib.CategoryTheory.Retract
import all Mathlib.CategoryTheory.Adjunction.FullyFaithful
import all WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
import all WeilConjectures.CategoryTheory.CompactlyGenerated
import all Mathlib.CategoryTheory.Triangulated.Functor
import all WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.CategoryTheory.Equivalence
import all WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
import all WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.Algebra.Category.ModuleCat.Ulift
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import all WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import all WeilConjectures.CategoryTheory.DerivedHomologyInjective
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import all Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.LargeHomSolutionSet
import all Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import all WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
import all Mathlib.Algebra.Module.ULift
import all WeilConjectures.CategoryTheory.CompactObject
import all WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import all WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import all WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import all WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import all Mathlib.Algebra.Homology.DerivedCategory.KProjective
import all Mathlib.Algebra.Category.ModuleCat.Projective
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
import all WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
import all WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import all WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import all Mathlib.CategoryTheory.Category.ULift
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import all Mathlib.CategoryTheory.Limits.Preserves.Opposites
import all Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import all WeilConjectures.CategoryTheory.CountableCoproductsIdempotentComplete
import all Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import all WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import all WeilConjectures.CategoryTheory.CoproductsOfCopowers
import all Mathlib.CategoryTheory.MorphismProperty.Retract
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import all WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
import all WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionForward
import all WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import all WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import all WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import all WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import all WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import all WeilConjectures.AlgebraicGeometry.SfGraphWordProjectionSquare
import all WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
import all WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import all WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import all WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import all WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all WeilConjectures.AlgebraicGeometry.SfGraphSecondProjectionSquare
import all WeilConjectures.AlgebraicGeometry.SfGraphMiddleProjectionSquare
import all WeilConjectures.AlgebraicGeometry.ProperOpenFactorProjection
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import all WeilConjectures.AlgebraicGeometry.SfGraphCompositionTailProjection
import all WeilConjectures.AlgebraicGeometry.SfGraphInterchangeProjection
import all WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenTensorSquare
import all WeilConjectures.CategoryTheory.KInjectiveTotalDerived
import all WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import all WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
import all WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.CategoryTheory.Sites.Point.Basic
import all Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import all WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import all WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import all WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import all WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all Mathlib.AlgebraicGeometry.Sites.Fpqc
import all WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import all WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import all WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import all WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import all WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import all WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import all WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import all WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import all WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import all WeilConjectures.Compactification.NagataCompactification
import all WeilConjectures.Compactification.Defs
import all WeilConjectures.SixFunctors.OpenClosed.Complex
import all WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import all WeilConjectures.Mathlib.RingTheory.Henselian
import all WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import all WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import all WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import all WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import all Mathlib.AlgebraicGeometry.ResidueField
import all Mathlib.FieldTheory.IsSepClosed
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import all WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import all WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import all WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import all WeilConjectures.RingTheory.StrictHenselizationTriples
import all WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import all WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import all WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMapsSupplement
import all WeilConjectures.AlgebraicGeometry.GeometricPointPullbackStalk
import all WeilConjectures.AlgebraicGeometry.GeometricPointCanonicalGerm
import all WeilConjectures.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange
import all WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import all WeilConjectures.Compactification.BaseChange
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all WeilConjectures.SixFunctors.OpenClosed.Exact
import all WeilConjectures.SixFunctors.BaseChange.Pasting
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenCartesianNormalization
import all WeilConjectures.AlgebraicGeometry.DerivedExchangeModuleTermwiseSupplement
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenCompositionSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenCubeNormalization
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenInterchangeSupplement
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPastingSupplement
import all WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonInterchange
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSidePasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import all WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkFirstLeg
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSecondLeg
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductRowPasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductInterchange
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductGeometry
import all WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientFirstSide
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import all WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition
import all WeilConjectures.AlgebraicGeometry.DerivedCompactSupportCompositionCoherenceSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientSecondSide
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkPasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import all WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSourcePasting
import all WeilConjectures.AlgebraicGeometry.OpenExchangeTowerSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSquarePasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkLift
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkWords
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkSquare
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import all WeilConjectures.AlgebraicGeometry.EtaleGraphDiagonalNormalization
import all WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport
import all WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange
import all WeilConjectures.AlgebraicGeometry.SfExceptionalTensorTransitivity
import all WeilConjectures.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase
import all WeilConjectures.AlgebraicGeometry.EtaleSumRightAdjointCoherenceSupplement
import all Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase
import all WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphUnitTensor
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphExchangeTensor
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.DiagonalAffineTraceCoordinates

/-! # Composition of smooth orientations and tensor maps

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.md
(blueprint: det-sp-composition-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

namespace SpCompositionFactors
open MonoidalCategory WeilConjectures.PurityFiniteSetting

section Finite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact f] [QuasiCompact (f ≫ g)]

/-- The unique right-adjoint comparison of the canonical proper/open left compositor.
Source: composition-factors, c (blueprint: det-sp-composition-factors). -/
def finiteCompositor :
    Etale.rightDerivedUpperShriek A (f ≫ g) ≅
      Etale.rightDerivedUpperShriek A g ⋙
        Etale.rightDerivedUpperShriek A f :=
  (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)).rightAdjointUniq
    (((Etale.rightDerivedUpperShriekAdjunction A f).comp
      (Etale.rightDerivedUpperShriekAdjunction A g)).ofNatIsoLeft
        (Etale.unboundedEtaleLowerShriekCompIso A f g))

/-- The actual finite tensor mate, with outside coefficient first.
Source: composition-factors, t (blueprint: det-sp-composition-factors). -/
abbrev finiteTensor {U V : Scheme.{u}} (v : U ⟶ V) [HasCompactification v]
    (K : Etale.DerivedCategoryModule A V) :=
  Etale.smoothTensorDualityMap A v
    (Etale.isIso_projectionMap_of_finite A v) K

/-- The coefficient rho before taking its inverse.
Source: composition-factors, rho (blueprint: det-sp-composition-factors). -/
abbrev finiteRho :=
  finiteTensor A f (Etale.dualizingComplex A g)

/-- The specified coefficient identification c_1 followed by rho inverse.
Source: composition-factors, mu (blueprint: det-sp-composition-factors). -/
def finiteMu (hR : IsIso (finiteRho A f g)) :=
  letI := hR
  (finiteCompositor A f g).app (𝟙_ _) ≪≫ (asIso (finiteRho A f g)).symm

/-- Canonical shifted Tate splitting, in the order f*L_g tensor L_f.
The even shifts are already part of the ordered finite line construction.
Source: composition-factors, clause (1) (blueprint: det-sp-composition-factors). -/
def finiteLineSplit (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤))) (e : ℕ) : ∀ d : ℕ,
    Etale.FiniteSmoothPurity.line A N hA X (d + e) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj
          (Etale.FiniteSmoothPurity.line A N hA Y e))).obj
            (Etale.FiniteSmoothPurity.line A N hA X d)
  | 0 => eqToIso (congrArg (Etale.FiniteSmoothPurity.line A N hA X) (Nat.zero_add e)) ≪≫
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA
        (Etale.projectiveLineTraceTransport N hN A hA) f hY e).symm ≪≫
      (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) X _).symm ≪≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).mapIso
        (smoothPurityUnitIso A X).symm
  | d + 1 =>
      eqToIso (congrArg (Etale.FiniteSmoothPurity.line A N hA X) (Nat.succ_add d e)) ≪≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
        (finiteLineSplit N hN hA hY e d)).app
          ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≪≫
      Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ _

/-- Pullback composition, inverse tensor associator and inverse pullback tensorator.
This identifies h*K tensor (f*M tensor N) with f*(g*K tensor M) tensor N.
Source: composition-factors, clause (2) (blueprint: det-sp-composition-factors). -/
def finiteReassociate (K : Etale.DerivedCategoryModule A Z)
    (M : Etale.DerivedCategoryModule A Y) (N : Etale.DerivedCategoryModule A X) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K)).app
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A f).obj M)).obj N) ≪≫
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ _).symm ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
        ((Etale.ordinaryFinitePullback A g).obj K) M).symm).app N

/-- The three equations on the finite pro-etale category, written in its canonical
ordinary-etale origin coordinates and then mapped by nu*. Every input is still an
arbitrary intrinsic constructible finite-Tor pro-etale complex. The source comparison
is sourceToOrigin/sourceAtOriginIso of the recorded finite purity interface.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors). -/
def FiniteEquations (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ)
    (af : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A N hA X d)
    (ag : Etale.dualizingComplex A g ≅
      Etale.FiniteSmoothPurity.line A N hA Y e)
    (ah : Etale.dualizingComplex A (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A N hA X (d + e)) : Prop :=
  ∃ hR : IsIso (finiteRho A f g),
    (Etale.FiniteSmoothPurity.comparison A X).map
        (ah.inv ≫ (finiteMu A f g hR).hom) =
      (Etale.FiniteSmoothPurity.comparison A X).map
        ((finiteLineSplit A f N hN hA hY e d).hom ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
            ((Etale.ordinaryFinitePullback A f).map ag.inv)).app _ ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).map af.inv) ∧
    ∀ (K : Etale.FiniteSmoothPurity.proCategory A Z),
      Etale.FiniteSmoothPurity.IsCtf A Z K →
      (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A (f ≫ g)).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))).map
                ((finiteMu A f g hR).inv) ≫
            finiteTensor A (f ≫ g) ((Etale.FiniteSmoothPurity.origin A Z).obj K) ≫
            (finiteCompositor A f g).hom.app ((Etale.FiniteSmoothPurity.origin A Z).obj K)) =
        (Etale.FiniteSmoothPurity.comparison A X).map
          ((finiteReassociate A f g ((Etale.FiniteSmoothPurity.origin A Z).obj K)
            (Etale.dualizingComplex A g)
            (Etale.dualizingComplex A f)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
              ((Etale.ordinaryFinitePullback A f).map
                (finiteTensor A g ((Etale.FiniteSmoothPurity.origin A Z).obj K)))).app _ ≫
            finiteTensor A f
              ((Etale.rightDerivedUpperShriek A g).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))) ∧
      (Etale.FiniteSmoothPurity.comparison A X).map
          (Etale.FiniteSmoothPurity.gamma A (f ≫ g) _ ah
              ((Etale.FiniteSmoothPurity.origin A Z).obj K) ≫
            (finiteCompositor A f g).hom.app ((Etale.FiniteSmoothPurity.origin A Z).obj K)) =
        (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A (f ≫ g)).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))).map
              (finiteLineSplit A f N hN hA hY e d).hom ≫
            (finiteReassociate A f g ((Etale.FiniteSmoothPurity.origin A Z).obj K)
              (Etale.FiniteSmoothPurity.line A N hA Y e)
              (Etale.FiniteSmoothPurity.line A N hA X d)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
              ((Etale.ordinaryFinitePullback A f).map
                (Etale.FiniteSmoothPurity.gamma A g _ ag
                  ((Etale.FiniteSmoothPurity.origin A Z).obj K)))).app _ ≫
            Etale.FiniteSmoothPurity.gamma A f _ af
              ((Etale.rightDerivedUpperShriek A g).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K)))

section TensorCalculus
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

universe v₁ v₂

private theorem tensorPiCongr {α : Sort v₁} (β γ : α → Sort v₂)
    (h : ∀ a, β a = γ a) : (∀ a, β a) = (∀ a, γ a) :=
  congrArg (fun F : α → Sort v₂ ↦ ∀ a, F a) (funext h)

private theorem tensorFunctionHEq {α : Sort v₁} {β γ : α → Sort v₂}
    (f : ∀ a, β a) (g : ∀ a, γ a)
    (hT : ∀ a, β a = γ a) (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  have hβγ : β = γ := funext hT
  cases hβγ
  exact heq_of_eq (funext fun a ↦ eq_of_heq (h a))

-- Isolate definitional reductions at their individual nodes of the congruence proof.
private theorem tensorNormalize {α β : Sort v₁}
    (a an : α) (b bn : β) (ha : a = an) (hb : b = bn)
    (h : HEq an bn) : HEq a b := by
  cases ha
  cases hb
  exact h

-- Extend the existing congruence builder across tensor API abbreviations and binders.
-- Every comparison produces an explicit congruence or extensionality proof.
open Lean Meta in
private meta def tensorWhiskerReduction (e : Expr) : MetaM (Option Expr) := do
  let mut cur := e
  let mut xs := #[]
  for _ in [:5] do
    if !cur.getAppFn.isConstOf ``Functor.obj then return none
    let args := cur.getAppArgs
    xs := xs.push args.back!
    cur := args[args.size - 2]!
  if !cur.getAppFn.isConstOf ``Functor.whiskeringLeft₂ then return none
  let h ← mkAppM ``Functor.whiskeringLeft₂_obj_obj_obj_obj_obj
    #[(← inferType e), xs[4]!, xs[3]!, xs[2]!, xs[1]!, xs[0]!]
  return some h

open Lean Meta in
private meta def tensorProjectionReduction (e : Expr) : MetaM (Option Expr) := do
  if !e.getAppFn.isConstOf ``Etale.sfCompactProjection then return none
  let args := e.getAppArgs
  let h ← mkAppM ``Etale.sfCompactProjection_eq
    #[args[0]!, args[args.size - 3]!, args[args.size - 2]!, args.back!]
  return some h

open Lean Meta in
private meta def tensorArrowReduction (e : Expr) : MetaM (Option Expr) := do
  if e.getAppFn.isConstOf ``NatTrans.app then
    let args := e.getAppArgs
    let n := args[args.size - 2]!.consumeMData
    if n.getAppFn.isConstOf ``CategoryTheory.Functor.map then
      let ns := n.getAppArgs
      let T := ns[ns.size - 4]!.consumeMData
      if T.getAppFn.isConstOf ``Etale.derivedTensor then
        return some (mkAppN (mkConst ``Etale.derivedTensor_map_app
          T.getAppFn.constLevels!) (T.getAppArgs ++
            #[ns[ns.size - 3]!, ns[ns.size - 2]!, ns.back!, args.back!]))
  if e.getAppFn.isConstOf ``CategoryTheory.Functor.map then
    let args := e.getAppArgs
    let F := args[args.size - 4]!.consumeMData
    if F.getAppFn.isConstOf ``Functor.obj then
      let fs := F.getAppArgs
      let T := fs[fs.size - 2]!.consumeMData
      if T.getAppFn.isConstOf ``Etale.derivedTensor then
        return some (mkAppN (mkConst ``Etale.derivedTensor_obj_map
          T.getAppFn.constLevels!) (T.getAppArgs ++
            #[fs.back!, args[args.size - 3]!, args[args.size - 2]!, args.back!]))
  return none

open Lean Meta in
private meta def tensorReductionEq (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if let some h ← tensorArrowReduction e then return h
  if let some h ← tensorWhiskerReduction e then return h
  if let some h ← tensorProjectionReduction e then return h
  if !e.getAppFn.isConstOf ``Functor.obj then return ← mkEqRefl e
  let args := e.getAppArgs
  let F := args[args.size - 2]!
  let N := args.back!
  if !F.getAppFn.isConstOf ``Functor.obj then return ← mkEqRefl e
  let argsF := F.getAppArgs
  let T := argsF[argsF.size - 2]!
  let M := argsF.back!
  let argsT := T.getAppArgs
  if T.getAppFn.isConstOf ``Etale.derivedTensor then
    let B := argsT[0]!
    let some X ← argsT.findM? (fun a ↦ do
      return (← inferType a).getAppFn.isConstOf ``Scheme) |
        throwError "no tensor scheme"
    return ← mkAppM ``Etale.compactTensor_obj_obj #[B, X, M, N]
  if T.getAppFn.isConstOf ``Etale.derivedTensorRightDerivedLowerShriek ||
      T.getAppFn.isConstOf ``Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar then
    let thm := if T.getAppFn.isConstOf ``Etale.derivedTensorRightDerivedLowerShriek then
      ``Etale.derivedTensorRightDerivedLowerShriek_obj_obj else
      ``Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    return mkAppN (mkConst thm T.getAppFn.constLevels!) (argsT ++ #[M, N])
  return ← mkEqRefl e

open Lean Meta in
private meta partial def tensorCongrHEqCore
    (proofCache : IO.Ref (Std.HashMap (Expr × Expr) Expr))
    (congrCache : IO.Ref (Std.HashMap (Expr × Nat) Expr)) (a b : Expr) : MetaM Expr := do
  let a := (← instantiateMVars a).consumeMData
  let b := (← instantiateMVars b).consumeMData
  if a == b then return ← mkHEqRefl a
  let key := (a, b)
  if let some h := (← proofCache.get).get? key then return h
  let solve : MetaM Expr := do
    let normalize (e : Expr) : MetaM Expr := do
      if let some h ← tensorArrowReduction e then return (← inferType h).appArg!
      if let some h ← tensorProjectionReduction e then return (← inferType h).appArg!
      if let some h ← tensorWhiskerReduction e then return (← inferType h).appArg!
      if e.getAppFn.isConstOf ``Functor.obj then
        let args := e.getAppArgs
        if args[args.size - 2]!.getAppFn.isConstOf ``Functor.id then return args.back!
      if e.isFVar then return ((← getLCtx).get! e.fvarId!).value?.getD e
      if e.getAppFn.isConstOf ``Etale.DerivedCategoryModule ||
          e.getAppFn.isConstOf ``purityModuleEtaleMonoidal ||
          e.getAppFn.isConstOf ``purityEtaleMonoidal ||
          e.getAppFn.isConstOf ``inferInstance ||
          e.getAppFn.isConstOf ``Etale.ordinaryFinitePullback ||
          e.getAppFn.isConstOf ``Etale.projectionMap ||
          e.getAppFn.isConstOf ``Etale.cartierAbelianEtale ||
          e.getAppFn.isConstOf ``Etale.dualizingComplex ||
          e.getAppFn.isConstOf ``Etale.constantComplex ||
          e.getAppFn.isConstOf ``Etale.derivedTensorAssociator ||
          e.getAppFn.isConstOf ``Etale.rightDerivedLowerShriek then
        return (← unfoldDefinition? e).getD e
      if e.getAppFn.isConstOf ``ReflQuiver.toQuiver ||
          e.getAppFn.isConstOf ``CategoryStruct.toQuiver then return ← whnf e
      if e.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory ||
          (e.getAppFn.isConstOf ``SymmetricCategory.toBraidedCategory &&
            e.getAppArgs.any (fun a ↦ a.getAppFn.isConstOf ``ModuleCat)) then
        return ← whnf e
      if (← inferType e).getAppFn.isConstOf ``PartialOrder then
        return ← whnf e
      return ← Etale.compactProjectionReduceObj e
    let an ← normalize a.headBeta
    let bn ← normalize b.headBeta
    if an != a || bn != b then
      let h ← tensorCongrHEqCore proofCache congrCache an bn
      return ← mkAppM ``tensorNormalize
        #[a, an, b, bn, (← tensorReductionEq a), (← tensorReductionEq b), h]
    if ← isProp (← inferType a) then
      let hp ← tensorCongrHEqCore proofCache congrCache (← inferType a) (← inferType b)
      let e ← mkAppM ``eq_of_heq #[hp]
      return ← mkAppM ``Etale.compactProjectionProofHEq #[a, b, e]
    if let .forallE n da ba bi := a then
      if let .forallE _ db bb _ := b then
        unless ← isDefEq da db do throwError m!"Different binder domains: {da} versus {db}"
        return ← withLocalDecl n bi da fun x ↦ do
          let pa := ba.instantiate1 x
          let pb := bb.instantiate1 x
          let h ← tensorCongrHEqCore proofCache congrCache pa pb
          let h ← mkAppM ``eq_of_heq #[h]
          let h ← mkLambdaFVars #[x] h
          let β ← mkLambdaFVars #[x] pa
          let γ ← mkLambdaFVars #[x] pb
          let e ← mkAppM ``tensorPiCongr #[β, γ, h]
          mkAppM ``heq_of_eq #[e]
    if let .lam n da ba bi := a then
      if let .lam _ db bb _ := b then
        unless ← isDefEq da db do
          throwError m!"Different lambda domains: {da} versus {db}"
        return ← withLocalDecl n bi da fun x ↦ do
          let pa := ba.instantiate1 x
          let pb := bb.instantiate1 x
          let h ← tensorCongrHEqCore proofCache congrCache pa pb
          let h ← mkLambdaFVars #[x] h
          let ht ← tensorCongrHEqCore proofCache congrCache (← inferType pa) (← inferType pb)
          let ht ← mkAppM ``eq_of_heq #[ht]
          let ht ← mkLambdaFVars #[x] ht
          mkAppM ``tensorFunctionHEq #[a, b, ht, h]
    let sameHead := a.getAppFn == b.getAppFn ||
      (a.getAppFn.isConst && b.getAppFn.isConst &&
        a.getAppFn.constName! == b.getAppFn.constName!)
    if sameHead && a.getAppArgs.size == b.getAppArgs.size then
      let argsA := a.getAppArgs
      let argsB := b.getAppArgs
      let ct? ← observing? (mkHCongrWithArity a.getAppFn argsA.size)
      let some ct := ct? | do
        -- The result of a functor object map can itself be a function (graded objects).
        let hf ← tensorCongrHEqCore proofCache congrCache a.appFn! b.appFn!
        let hx ← tensorCongrHEqCore proofCache congrCache a.appArg! b.appArg!
        let e ← mkAppM ``congr_heq #[hf, hx]
        return ← mkAppM ``heq_of_eq #[e]
      let mut ps := #[]
      for i in [:argsA.size] do
        let mut h ← tensorCongrHEqCore proofCache congrCache argsA[i]! argsB[i]!
        if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
        ps := ps ++ #[argsA[i]!, argsB[i]!, h]
      let congrKey := (a.getAppFn, argsA.size)
      let congrProof ← if let some h := (← congrCache.get).get? congrKey then pure h else do
        let h ← mkAuxTheorem ct.type ct.proof
        congrCache.modify (fun c ↦ c.insert congrKey h)
        pure h
      let pf := mkAppN congrProof ps
      if (← inferType pf).isHEq then return pf
      else return ← mkAppM ``heq_of_eq #[pf]
    else
      throwError m!"Different heads: {a} versus {b}"
  let h ← solve
  proofCache.modify (fun c ↦ c.insert key h)
  return h

open Lean Meta in
private meta def tensorCongrHEq (a b : Expr) : MetaM Expr := do
  let proofCache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  let congrCache ← IO.mkRef ({} : Std.HashMap (Expr × Nat) Expr)
  tensorCongrHEqCore proofCache congrCache a b

private theorem conjugate_projection_square
    {C : Type*} [Category C] {A B D E F G : C}
    (t : A ≅ B) (v : E ≅ F) (w : D ≅ G)
    (p : B ⟶ D) (q : A ⟶ E) (γ : F ⟶ D) (δ : E ⟶ G)
    (h : p ≫ w.hom = t.inv ≫ q ≫ δ)
    (hn : γ ≫ w.hom = v.inv ≫ δ) :
    t.hom ≫ p = q ≫ v.hom ≫ γ := by
  apply (cancel_mono w.hom).1
  simp only [Category.assoc]
  rw [h, hn, t.hom_inv_id_assoc, v.hom_inv_id_assoc]

private theorem braid_reassociate
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (A B W : C) :
    A ◁ (β_ B W).hom ≫ (β_ A (W ⊗ B)).hom ≫ (α_ W B A).hom =
      (α_ A B W).inv ≫ ((β_ A B).hom ▷ W) ≫ (β_ (B ⊗ A) W).hom := by
  simp only [BraidedCategory.braiding_tensor_right_hom,
    BraidedCategory.braiding_tensor_left_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact (BraidedCategory.yang_baxter A B W).symm

private theorem braid_tensorator
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (U : D ⥤ C) (A B : D) (W : C)
    (mAB : U.obj (A ⊗ B) ≅ U.obj A ⊗ U.obj B)
    (mBA : U.obj (B ⊗ A) ≅ U.obj B ⊗ U.obj A)
    (hb : mAB.inv ≫ U.map (β_ A B).hom =
      (β_ (U.obj A) (U.obj B)).hom ≫ mBA.inv) :
    U.obj A ◁ (β_ (U.obj B) W).hom ≫
      (β_ (U.obj A) (W ⊗ U.obj B)).hom ≫
      (α_ W (U.obj B) (U.obj A)).hom ≫ W ◁ mBA.inv =
    (α_ (U.obj A) (U.obj B) W).inv ≫ (mAB.inv ▷ W) ≫
      (U.map (β_ A B).hom ▷ W) ≫ (β_ (U.obj (B ⊗ A)) W).hom := by
  rw [← comp_whiskerRight_assoc, hb, comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ W ◁ mBA.inv) (braid_reassociate (U.obj A) (U.obj B) W)

private theorem braid_tensorator_comp
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (U : D ⥤ C) (A B : D) (W P : C)
    (γ : P ⟶ U.obj A)
    (mAB : U.obj (A ⊗ B) ≅ U.obj A ⊗ U.obj B)
    (mBA : U.obj (B ⊗ A) ≅ U.obj B ⊗ U.obj A)
    (hb : mAB.inv ≫ U.map (β_ A B).hom =
      (β_ (U.obj A) (U.obj B)).hom ≫ mBA.inv) :
    P ◁ (β_ (U.obj B) W).hom ≫ (β_ P (W ⊗ U.obj B)).hom ≫
      (W ⊗ U.obj B) ◁ γ ≫ (α_ W (U.obj B) (U.obj A)).hom ≫ W ◁ mBA.inv =
    (γ ▷ (U.obj B ⊗ W)) ≫ (α_ (U.obj A) (U.obj B) W).inv ≫
      (mAB.inv ▷ W) ≫ (U.map (β_ A B).hom ▷ W) ≫
      (β_ (U.obj (B ⊗ A)) W).hom := by
  rw [← BraidedCategory.braiding_naturality_left_assoc,
    whisker_exchange_assoc, braid_tensorator U A B W mAB mBA hb]

private theorem opposite_tensor_composition
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (U : D ⥤ C) (A B Q : D) (W P H R : C)
    (γ : P ⟶ U.obj A) (μ : H ≅ U.obj B ⊗ W)
    (mAB : U.obj (A ⊗ B) ≅ U.obj A ⊗ U.obj B)
    (mBA : U.obj (B ⊗ A) ≅ U.obj B ⊗ U.obj A)
    (hb : mAB.inv ≫ U.map (β_ A B).hom =
      (β_ (U.obj A) (U.obj B)).hom ≫ mBA.inv)
    (s : B ⊗ A ⟶ Q) (t : W ⊗ U.obj Q ⟶ R)
    (L : H ⊗ P ⟶ R)
    (hL : L = ((μ.hom ≫ (β_ (U.obj B) W).hom) ▷ P) ≫
      (W ⊗ U.obj B) ◁ γ ≫ (α_ W (U.obj B) (U.obj A)).hom ≫
      W ◁ mBA.inv ≫ W ◁ U.map s ≫ t) :
    P ◁ μ.inv ≫ (β_ P H).hom ≫ L =
      (γ ▷ (U.obj B ⊗ W)) ≫ (α_ (U.obj A) (U.obj B) W).inv ≫
      (mAB.inv ▷ W) ≫ (U.map ((β_ A B).hom ≫ s) ▷ W) ≫
      (β_ (U.obj Q) W).hom ≫ t := by
  rw [hL, ← BraidedCategory.braiding_naturality_right_assoc,
    ← whiskerLeft_comp_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% (braid_tensorator_comp U A B W P γ mAB mBA hb)]
  simp only [Functor.map_comp, comp_whiskerRight, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc (U.map s) W]

private theorem reassociate_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (U : D ⥤ C) (A : D) (P : C)
    (γ : P ⟶ U.obj A) {M M' : D} (m : M ⟶ M') {N N' : C} (n : N ⟶ N')
    (p : ∀ T : D, U.obj (A ⊗ T) ≅ U.obj A ⊗ U.obj T)
    (hp : U.obj A ◁ U.map m ≫ (p M').inv = (p M).inv ≫ U.map (A ◁ m)) :
    P ◁ (U.map m ⊗ₘ n) ≫ (γ ▷ (U.obj M' ⊗ N')) ≫
      (α_ (U.obj A) (U.obj M') N').inv ≫
      ((p M').inv ▷ N') =
    (γ ▷ (U.obj M ⊗ N)) ≫ (α_ (U.obj A) (U.obj M) N).inv ≫
      ((p M).inv ▷ N) ≫ (U.map (A ◁ m) ⊗ₘ n) := by
  rw [whisker_exchange_assoc,
    ← id_tensorHom (U.obj A) (U.map m ⊗ₘ n),
    associator_inv_naturality_assoc]
  rw [id_tensorHom, tensorHom_def', tensorHom_def']
  simp only [Category.assoc]
  rw [← comp_whiskerRight, hp, comp_whiskerRight, whisker_exchange_assoc]

private theorem gamma_of_tensor_composition
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (U : D ⥤ C) (A B Lg Q : D) (P H Lh W Lf R : C)
    (μ : H ≅ U.obj B ⊗ W) (ah : H ≅ Lh) (ag : B ≅ Lg) (af : W ≅ Lf)
    (split : Lh ≅ U.obj Lg ⊗ Lf)
    (th : P ⊗ H ⟶ R) (tg : A ⊗ B ⟶ Q) (tf : U.obj Q ⊗ W ⟶ R)
    (rW : P ⊗ (U.obj B ⊗ W) ⟶ U.obj (A ⊗ B) ⊗ W)
    (rL : P ⊗ (U.obj Lg ⊗ Lf) ⟶ U.obj (A ⊗ Lg) ⊗ Lf)
    (hor : ah.inv ≫ μ.hom = split.hom ≫ (U.map ag.inv ▷ Lf) ≫ U.obj B ◁ af.inv)
    (ht : P ◁ μ.inv ≫ th = rW ≫ (U.map tg ▷ W) ≫ tf)
    (hn : P ◁ (U.map ag.inv ▷ Lf) ≫ P ◁ (U.obj B ◁ af.inv) ≫ rW =
      rL ≫ (U.map (A ◁ ag.inv) ▷ Lf) ≫ U.obj (A ⊗ B) ◁ af.inv) :
    P ◁ ah.inv ≫ th = P ◁ split.hom ≫ rL ≫
      (U.map (A ◁ ag.inv ≫ tg) ▷ Lf) ≫ U.obj Q ◁ af.inv ≫ tf := by
  have ho := congrArg (fun t ↦ t ≫ μ.inv) hor
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at ho
  rw [ho]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [ht, reassoc_of% hn, whisker_exchange_assoc]
  simp only [Functor.map_comp, comp_whiskerRight, Category.assoc]

private theorem finiteCompositor_counit
    (K : Etale.DerivedCategoryModule A Z) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((finiteCompositor A f g).hom.app K)) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app _) ≫
      (Etale.rightDerivedUpperShriekAdjunction A g).counit.app K =
    (Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app _ ≫
      (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)).counit.app K := by
  let E := Etale.unboundedEtaleLowerShriekCompIso A f g
  let a := (Etale.rightDerivedUpperShriekAdjunction A f).comp
    (Etale.rightDerivedUpperShriekAdjunction A g)
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)) (a.ofNatIsoLeft E) K
  change _ ≫ E.inv.app _ ≫ a.counit.app K = _ at h
  rw [E.inv.naturality_assoc] at h
  have hh := congrArg (fun t ↦ E.hom.app _ ≫ t) h
  have ha := (Etale.rightDerivedUpperShriekAdjunction A f).comp_counit_app
    (Etale.rightDerivedUpperShriekAdjunction A g) K
  change a.counit.app K = _ at ha
  rw [ha] at hh
  dsimp only [a, E] at hh
  simpa only [finiteCompositor, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.comp_map] using hh

private theorem comparison_transpose
    {C D V : Type*} [Category C] [Category D] [Category V]
    (Fa : C ⥤ D) (Fb : D ⥤ V) (Fh : C ⥤ V)
    (Ga : D ⥤ C) (Gb : V ⥤ D) (Gh : V ⥤ C)
    (adja : Fa ⊣ Ga) (adjb : Fb ⊣ Gb) (adjh : Fh ⊣ Gh)
    (J : Fh ≅ Fa ⋙ Fb) (c : Gh ≅ Gb ⋙ Ga)
    (hc : ∀ K, Fb.map (Fa.map (c.hom.app K)) ≫
      Fb.map (adja.counit.app (Gb.obj K)) ≫ adjb.counit.app K =
        J.inv.app (Gh.obj K) ≫ adjh.counit.app K)
    {M : C} (K : V) (t : M ⟶ Gh.obj K) :
    ((adja.comp adjb).homEquiv M K).symm (t ≫ c.hom.app K) =
      J.inv.app M ≫ (adjh.homEquiv M K).symm t := by
  simp only [Adjunction.homEquiv_counit, Adjunction.comp_counit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [hc K]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ z ≫ adjh.counit.app K) (J.inv.naturality t)

omit [QuasiCompact f] in
private theorem finiteTensor_eq
    (K : Etale.DerivedCategoryModule A Y) :
    let := _root_.DerivedCategory.braidedCategory'
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    finiteTensor A f K =
      (β_ ((Etale.ordinaryFinitePullback A f).obj K)
        (Etale.dualizingComplex A f)).hom ≫ Etale.dualizingComplexTensorMap A f K := by
  exact Etale.smoothTensorDualityMap_eq A f (Etale.isIso_projectionMap_of_finite A f) K

section LeftCalculus
open Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Etale.sfEtaleAmbientTensorMap
  Etale.unboundedEtaleLowerShriekCompIso
attribute [local implicit_reducible] Etale.rightDerivedLowerShriek
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  Etale.dualizingComplex Etale.constantComplex Etale.sfCompactProjection

private theorem finiteProjectionComposition
    (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Z) :
    Etale.sfEtaleCompactProjectionInverse A (HasCompactification.compactification (f ≫ g))
        M K ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).map
        ((Etale.unboundedEtaleLowerShriekCompIso A f g).inv.app M)).app K =
    (Etale.unboundedEtaleLowerShriekCompIso A f g).inv.app
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.ordinaryFinitePullback A (f ≫ g)).obj K)) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (Etale.sfEtaleCompactProjectionInverse A (HasCompactification.compactification f)
          M ((Etale.ordinaryFinitePullback A g).obj K)) ≫
      Etale.sfEtaleCompactProjectionInverse A (HasCompactification.compactification g)
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K := by
  let ca := HasCompactification.compactification f
  let cb := HasCompactification.compactification g
  let ch := HasCompactification.compactification (f ≫ g)
  let Fa := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let Fb := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
  let Fh := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)
  let TX := Etale.derivedTensor (ModuleCat.{u + 1} A) X
  let TZ := Etale.derivedTensor (ModuleCat.{u + 1} A) Z
  let Ua := Etale.ordinaryFinitePullback A f
  let Ub := Etale.ordinaryFinitePullback A g
  let Uh := Etale.ordinaryFinitePullback A (f ≫ g)
  let E := (Etale.unboundedEtaleLowerShriekCompIso A f g).symm
  let γ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K
  rw [Etale.inverse_projection_wrapper, Etale.inverse_projection_wrapper,
    Etale.inverse_projection_wrapper, Fb.map_inv]
  apply Etale.inverse_graph_projection_square
  have hfwd0 := Etale.projectionMap_chosen_comp A f g M K
  have hfwd : Etale.sfCompactProjection A cb (Fa.obj M) K ≫
      Fb.map (Etale.sfCompactProjection A ca M (Ub.obj K)) ≫
      E.inv.app ((TX.obj M).obj (Ua.obj (Ub.obj K))) =
    (TZ.map (E.inv.app M)).app K ≫ Etale.sfCompactProjection A ch M K ≫
      Fh.map ((TX.obj M).map γ) := by
    simp only [Fa, Fb, Fh, TX, TZ, Ua, Ub, E, ca, cb, ch, γ, Iso.symm_inv,
      Etale.ordinaryFinitePullback] at hfwd0 ⊢
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let decls := (← Lean.getLCtx).decls.toList.filterMap id
      let some h := decls.find? (fun h ↦ h.userName.eraseMacroScopes == `hfwd0) |
        throwError "no forward projection equation"
      let eq ← tensorCongrHEq target (← Lean.instantiateMVars h.type)
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
      let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, h.toExpr]
      (← Lean.Elab.Tactic.getMainGoal).assign pf
  have hEγ := E.inv.naturality ((TX.obj M).map γ)
  change Fb.map (Fa.map ((TX.obj M).map γ)) ≫
      E.inv.app ((TX.obj M).obj (Ua.obj (Ub.obj K))) =
    E.inv.app ((TX.obj M).obj (Uh.obj K)) ≫ Fh.map ((TX.obj M).map γ) at hEγ
  have hc := conjugate_projection_square ((TZ.mapIso (E.app M)).app K)
    (E.app ((TX.obj M).obj (Uh.obj K)))
    (E.symm.app ((TX.obj M).obj (Ua.obj (Ub.obj K))))
    (Etale.sfCompactProjection A cb (Fa.obj M) K ≫
      Fb.map (Etale.sfCompactProjection A ca M (Ub.obj K)))
    (Etale.sfCompactProjection A ch M K)
    (Fb.map (Fa.map ((TX.obj M).map γ))) (Fh.map ((TX.obj M).map γ))
    (by simpa only [Iso.app_hom, Iso.symm_hom, Iso.app_inv,
      Functor.mapIso_inv, Category.assoc] using hfwd)
    (by simpa only [Iso.app_hom, Iso.symm_hom, Iso.app_inv] using hEγ)
  simp only [Iso.app_hom, Functor.mapIso_hom, Functor.comp_obj,
    Fa, Fb, TX, TZ, Ua, Ub, Uh, E, ca, cb, ch, γ, Iso.symm_hom,
    Etale.ordinaryFinitePullback, Etale.rightDerivedLowerShriek] at hc ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `hc) |
      throwError "no normalized projection equation"
    let eq ← tensorCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem finiteAmbientComposition
    (Ga : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (Gb : Etale.DerivedCategoryModule A Z ⥤ Etale.DerivedCategoryModule A Y)
    (Gh : Etale.DerivedCategoryModule A Z ⥤ Etale.DerivedCategoryModule A X)
    (adja : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ Ga)
    (adjb : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⊣ Gb)
    (adjh : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) ⊣ Gh)
    (c : Gh ≅ Gb ⋙ Ga)
    (hadj : ∀ K, (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (c.hom.app K)) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (adja.counit.app (Gb.obj K)) ≫ adjb.counit.app K =
      (Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app (Gh.obj K) ≫
        adjh.counit.app K)
    (h : IsIso (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification f)
      Ga adja
      (Gb.obj (Etale.constantComplex A Z))))
    (K : Etale.DerivedCategoryModule A Z) :
    Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification (f ≫ g))
        Gh
        adjh K ≫
        c.hom.app K =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        (c.hom.app (Etale.constantComplex A Z) ≫
          inv (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification f)
            Ga adja
            (Gb.obj (Etale.constantComplex A Z))))).app
        ((Etale.ordinaryFinitePullback A (f ≫ g)).obj K) ≫
      Etale.sfExceptionalTensorReassociation A f g
        (Ga.obj (Etale.constantComplex A Y))
        (Gb.obj (Etale.constantComplex A Z)) K ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (Ga.obj (Etale.constantComplex A Y))).map
          ((Etale.ordinaryFinitePullback A f).map
            (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification g)
              Gb
              adjb K)) ≫
      Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification f)
        Ga adja
        (Gb.obj K) := by
  let ca := HasCompactification.compactification f
  let cb := HasCompactification.compactification g
  let ch := HasCompactification.compactification (f ≫ g)
  let Fa := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let Fb := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
  let Fh := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)
  let TX := Etale.derivedTensor (ModuleCat.{u + 1} A) X
  let TY := Etale.derivedTensor (ModuleCat.{u + 1} A) Y
  let TZ := Etale.derivedTensor (ModuleCat.{u + 1} A) Z
  let Ua := Etale.ordinaryFinitePullback A f
  let Ub := Etale.ordinaryFinitePullback A g
  let Uh := Etale.ordinaryFinitePullback A (f ≫ g)
  let W := Ga.obj (Etale.constantComplex A Y)
  let V := Gb.obj (Etale.constantComplex A Z)
  let H := Gh.obj (Etale.constantComplex A Z)
  let M := (TX.obj W).obj (Ua.obj V)
  let E := (Etale.unboundedEtaleLowerShriekCompIso A f g).symm
  let := h
  let δ := c.hom.app (Etale.constantComplex A Z) ≫
    inv (Etale.sfEtaleAmbientTensorMap A ca Ga adja V)
  have hd : δ ≫ Etale.sfEtaleAmbientTensorMap A ca Ga adja V =
      c.hom.app (Etale.constantComplex A Z) := by
    simp only [δ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have scalar : E.inv.app H ≫ adjh.counit.app (Etale.constantComplex A Z) =
      Fb.map (Fa.map δ) ≫ Fb.map (Etale.ambientEvaluation A ca Ga adja V) ≫
        adjb.counit.app (Etale.constantComplex A Z) := by
    have hc := hadj (Etale.constantComplex A Z)
    change Fb.map (Fa.map (c.hom.app (Etale.constantComplex A Z))) ≫
      Fb.map (adja.counit.app V) ≫ adjb.counit.app (Etale.constantComplex A Z) = _ at hc
    rw [← hd] at hc
    simp only [Fa.map_comp, Fb.map_comp, Category.assoc] at hc
    rw [← Fb.map_comp_assoc (Fa.map (Etale.sfEtaleAmbientTensorMap A ca Ga adja V))] at hc
    have ht := Etale.ambient_transpose A ca Ga adja V
    change Fa.map (Etale.sfEtaleAmbientTensorMap A ca Ga adja V) ≫ adja.counit.app V =
      Etale.ambientEvaluation A ca Ga adja V at ht
    rw [ht] at hc
    exact hc.symm
  apply ((adja.comp adjb).homEquiv _ K).symm.injective
  rw [comparison_transpose Fa Fb Fh Ga Gb Gh adja adjb adjh E c hadj]
  rw [Adjunction.homEquiv_counit]
  have hth := Etale.ambient_transpose A ch Gh adjh K
  change Fh.map (Etale.sfEtaleAmbientTensorMap A ch Gh adjh K) ≫ adjh.counit.app K =
    Etale.ambientEvaluation A ch Gh adjh K at hth
  rw [hth]
  have hn := Etale.ambient_naturality A ca Ga adja
    (Etale.sfEtaleAmbientTensorMap A cb Gb adjb K)
  change (TX.obj W).map (Ua.map (Etale.sfEtaleAmbientTensorMap A cb Gb adjb K)) ≫
    Etale.sfEtaleAmbientTensorMap A ca Ga adja (Gb.obj K) =
      Etale.sfEtaleAmbientTensorMap A ca Ga adja ((TY.obj V).obj (Ub.obj K)) ≫
        Ga.map (Etale.sfEtaleAmbientTensorMap A cb Gb adjb K) at hn
  rw [hn, ← Category.assoc, ← Category.assoc, Etale.composite_transpose_post]
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have htb := Etale.ambient_transpose A cb Gb adjb K
  change Fb.map (Etale.sfEtaleAmbientTensorMap A cb Gb adjb K) ≫ adjb.counit.app K =
    Etale.ambientEvaluation A cb Gb adjb K at htb
  rw [htb]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Fb.map_comp_assoc
    (Fa.map (Etale.sfEtaleAmbientTensorMap A ca Ga adja ((TY.obj V).obj (Ub.obj K))))]
  have hta := Etale.ambient_transpose A ca Ga adja ((TY.obj V).obj (Ub.obj K))
  change Fa.map (Etale.sfEtaleAmbientTensorMap A ca Ga adja ((TY.obj V).obj (Ub.obj K))) ≫
    adja.counit.app ((TY.obj V).obj (Ub.obj K)) =
      Etale.ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K)) at hta
  rw [hta]
  rw [← TX.map_comp]
  change E.inv.app _ ≫ Etale.ambientEvaluation A ch Gh adjh K =
    Fb.map (Fa.map ((TX.map δ).app (Uh.obj K))) ≫
      Fb.map (Fa.map (Etale.sfExceptionalTensorReassociation A f g W V K)) ≫
      Fb.map (Etale.ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K))) ≫
        Etale.ambientEvaluation A cb Gb adjb K
  let r := (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X W
    (Ua.obj V) (Ua.obj (Ub.obj K))).hom ≫
      (TX.obj W).map (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f V
        (Ub.obj K)).inv
  let γ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K
  change _ = Fb.map (Fa.map ((TX.map δ).app (Uh.obj K))) ≫
    Fb.map (Fa.map ((TX.obj M).map γ ≫ r)) ≫
      Fb.map (Etale.ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K))) ≫
        Etale.ambientEvaluation A cb Gb adjb K
  rw [Fa.map_comp, Fb.map_comp]
  simp only [Category.assoc]
  have har := Etale.ambient_associativity_transpose A ca Ga adja V (Ub.obj K)
  change Fa.map r ≫ Etale.ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K)) =
    Etale.sfEtaleCompactProjectionInverse A ca M (Ub.obj K) ≫
      (TY.map (Etale.ambientEvaluation A ca Ga adja V)).app (Ub.obj K) at har
  have hnb := Etale.sfEtaleCompactProjectionInverse_naturality_left A cb
    (Etale.ambientEvaluation A ca Ga adja V) K
  have hp := finiteProjectionComposition A f g M K
  have hnδ := Etale.sfEtaleCompactProjectionInverse_naturality_left A ch δ K
  have hscl : Fh.map δ ≫ E.hom.app M ≫
      Fb.map (Etale.ambientEvaluation A ca Ga adja V) ≫
        adjb.counit.app (Etale.constantComplex A Z) =
          adjh.counit.app (Etale.constantComplex A Z) := by
    have hE := E.hom.naturality δ
    change Fh.map δ ≫ E.hom.app M = E.hom.app H ≫ Fb.map (Fa.map δ) at hE
    rw [reassoc_of% hE]
    change E.hom.app H ≫ Fb.map (Fa.map δ) ≫
      Fb.map (Etale.ambientEvaluation A ca Ga adja V) ≫
        adjb.counit.app (Etale.constantComplex A Z) = _
    rw [← scalar, Iso.hom_inv_id_app_assoc]
  exact Etale.projection_composition_calculation Fa Fb Fh E
    (TY.flip.obj (Ub.obj K)) (TZ.flip.obj K) δ ((TX.map δ).app (Uh.obj K))
    ((TX.obj M).map γ) r (Etale.ambientEvaluation A ca Ga adja V)
    (Etale.ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K)))
    (Etale.sfEtaleCompactProjectionInverse A ch H K)
    (Etale.sfEtaleCompactProjectionInverse A ch M K)
    (Etale.sfEtaleCompactProjectionInverse A ca M (Ub.obj K))
    (Etale.sfEtaleCompactProjectionInverse A cb (Fa.obj M) K)
    (Etale.sfEtaleCompactProjectionInverse A cb V K)
    (adjh.counit.app (Etale.constantComplex A Z))
    (adjb.counit.app (Etale.constantComplex A Z))
    (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Z K).hom hscl hnδ hp har hnb

private theorem finiteLeftComposition
    (h : IsIso (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification f)
      (Etale.rightDerivedUpperShriek A f) (Etale.rightDerivedUpperShriekAdjunction A f)
      ((Etale.rightDerivedUpperShriek A g).obj (Etale.constantComplex A Z))))
    (K : Etale.DerivedCategoryModule A Z) :
    Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification (f ≫ g))
        (Etale.rightDerivedUpperShriek A (f ≫ g))
        (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)) K ≫
        (finiteCompositor A f g).hom.app K =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((finiteCompositor A f g).hom.app (Etale.constantComplex A Z) ≫
          inv (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification f)
            (Etale.rightDerivedUpperShriek A f) (Etale.rightDerivedUpperShriekAdjunction A f)
            ((Etale.rightDerivedUpperShriek A g).obj (Etale.constantComplex A Z))))).app
        ((Etale.ordinaryFinitePullback A (f ≫ g)).obj K) ≫
      Etale.sfExceptionalTensorReassociation A f g
        ((Etale.rightDerivedUpperShriek A f).obj (Etale.constantComplex A Y))
        ((Etale.rightDerivedUpperShriek A g).obj (Etale.constantComplex A Z)) K ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.rightDerivedUpperShriek A f).obj (Etale.constantComplex A Y))).map
          ((Etale.ordinaryFinitePullback A f).map
            (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification g)
              (Etale.rightDerivedUpperShriek A g)
              (Etale.rightDerivedUpperShriekAdjunction A g) K)) ≫
      Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification f)
        (Etale.rightDerivedUpperShriek A f) (Etale.rightDerivedUpperShriekAdjunction A f)
        ((Etale.rightDerivedUpperShriek A g).obj K) := by
  exact finiteAmbientComposition A f g (Etale.rightDerivedUpperShriek A f)
    (Etale.rightDerivedUpperShriek A g) (Etale.rightDerivedUpperShriek A (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A g)
    (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)) (finiteCompositor A f g)
    (finiteCompositor_counit A f g) h K

-- Match the monoidal instance used by the derived tensor API.
attribute [local instance 20000] Etale.sheafBraidedCategory

private theorem finiteRightComposition (hR : IsIso (finiteRho A f g))
    (K : Etale.DerivedCategoryModule A Z) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((Etale.ordinaryFinitePullback A (f ≫ g)).obj K)).map
        (finiteMu A f g hR).inv ≫ finiteTensor A (f ≫ g) K ≫
        (finiteCompositor A f g).hom.app K =
      (finiteReassociate A f g K (Etale.dualizingComplex A g)
        (Etale.dualizingComplex A f)).hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.ordinaryFinitePullback A f).map (finiteTensor A g K))).app _ ≫
      finiteTensor A f ((Etale.rightDerivedUpperShriek A g).obj K) := by
  let : MonoidalCategory (Etale.DerivedCategoryModule A X) :=
    _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let : MonoidalCategory (Etale.DerivedCategoryModule A Y) :=
    _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  let : MonoidalCategory (Etale.DerivedCategoryModule A Z) :=
    _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := _root_.DerivedCategory.braidedCategory'
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := _root_.DerivedCategory.braidedCategory'
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := hR
  let U := Etale.ordinaryFinitePullback A f
  let V := Etale.dualizingComplex A g
  let W := Etale.dualizingComplex A f
  let P := (Etale.ordinaryFinitePullback A (f ≫ g)).obj K
  let B := (Etale.ordinaryFinitePullback A g).obj K
  let H := Etale.dualizingComplex A (f ≫ g)
  let ca := HasCompactification.compactification f
  let Ga := Etale.rightDerivedUpperShriek A f
  let adja := Etale.rightDerivedUpperShriekAdjunction A f
  let s := Etale.sfEtaleAmbientTensorMap A ca Ga adja V
  have hrho : finiteRho A f g = (β_ (U.obj V) W).hom ≫ s := by
    change finiteTensor A f V = _
    rw [finiteTensor_eq, ← Etale.ambientTensorMap_eq]
  have hbr : IsIso ((β_ (U.obj V) W).hom ≫ s) := by
    rw [← hrho]
    exact hR
  let := hbr
  have hs : IsIso s := IsIso.of_isIso_comp_left (β_ (U.obj V) W).hom s
  let := hs
  have hδ : (finiteCompositor A f g).hom.app (Etale.constantComplex A Z) ≫ inv s =
      (finiteMu A f g hR).hom ≫ (β_ (U.obj V) W).hom := by
    apply (cancel_mono s).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← hrho]
    simp only [finiteMu, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rfl
  have hl := finiteLeftComposition A f g hs K
  dsimp only [s, ca, Ga, adja, V, Etale.dualizingComplex, Etale.constantComplex] at hδ
  dsimp only [Etale.constantComplex] at hl
  rw [hδ] at hl
  let mAB := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f B V
  let mBA := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f V B
  have hb : mAB.inv ≫ U.map (β_ B V).hom =
      (β_ (U.obj B) (U.obj V)).hom ≫ mBA.inv := by
    have hbf := Etale.leftDerivedUpperStar_map_braiding_hom_δ
      (ModuleCat.{u + 1} A) f B V
    change U.map (β_ B V).hom ≫ mBA.hom =
      mAB.hom ≫ (β_ (U.obj B) (U.obj V)).hom at hbf
    apply (cancel_mono mBA.hom).1
    simp only [Category.assoc, hbf, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  let γ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K
  have he := opposite_tensor_composition U B V
    ((Etale.rightDerivedUpperShriek A g).obj K) W P H
    (Ga.obj ((Etale.rightDerivedUpperShriek A g).obj K)) γ
    (finiteMu A f g hR) mAB mBA hb
    (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification g)
      (Etale.rightDerivedUpperShriek A g) (Etale.rightDerivedUpperShriekAdjunction A g) K)
    (Etale.sfEtaleAmbientTensorMap A ca Ga adja
      ((Etale.rightDerivedUpperShriek A g).obj K))
    (Etale.sfEtaleAmbientTensorMap A (HasCompactification.compactification (f ≫ g))
      (Etale.rightDerivedUpperShriek A (f ≫ g))
      (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)) K ≫
      (finiteCompositor A f g).hom.app K) (by
        simpa only [Etale.sfExceptionalTensorReassociation,
          Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map,
          Etale.derivedTensorAssociator_eq, Etale.compactTensor_obj_obj,
          U, V, W, P, B, H, ca, Ga, adja, mBA, γ,
          Etale.dualizingComplex, Etale.constantComplex, Etale.ordinaryFinitePullback,
          Functor.comp_obj, Category.assoc] using hl)
  dsimp only [ca, Ga, adja] at he
  simp only [Etale.ambientTensorMap_eq] at he
  simp only [finiteTensor_eq, finiteReassociate, Iso.trans_hom,
    Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    U, V, W, P, B, H, mAB, γ,
    Functor.comp_obj, Category.assoc] at he ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `he) |
      throwError "no normalized tensor equation"
    let eq ← tensorCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem finiteGammaComposition
    {Lf Lh : Etale.DerivedCategoryModule A X}
    {Lg : Etale.DerivedCategoryModule A Y}
    (af : Etale.dualizingComplex A f ≅ Lf)
    (ag : Etale.dualizingComplex A g ≅ Lg)
    (ah : Etale.dualizingComplex A (f ≫ g) ≅ Lh)
    (hR : IsIso (finiteRho A f g))
    (split : Lh ≅ ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((Etale.ordinaryFinitePullback A f).obj Lg)).obj Lf)
    (hor : ah.inv ≫ (finiteMu A f g hR).hom = split.hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.ordinaryFinitePullback A f).map ag.inv)).app Lf ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj (Etale.dualizingComplex A g))).map af.inv)
    (K₀ : Etale.DerivedCategoryModule A Z) :
    Etale.FiniteSmoothPurity.gamma A (f ≫ g) Lh ah K₀ ≫
        (finiteCompositor A f g).hom.app K₀ =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A (f ≫ g)).obj K₀)).map split.hom ≫
      (finiteReassociate A f g K₀ Lg Lf).hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.ordinaryFinitePullback A f).map
          (Etale.FiniteSmoothPurity.gamma A g Lg ag K₀))).app Lf ≫
      Etale.FiniteSmoothPurity.gamma A f Lf af
        ((Etale.rightDerivedUpperShriek A g).obj K₀) := by
  let : MonoidalCategory (Etale.DerivedCategoryModule A X) :=
    _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let : MonoidalCategory (Etale.DerivedCategoryModule A Y) :=
    _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  let : MonoidalCategory (Etale.DerivedCategoryModule A Z) :=
    _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := _root_.DerivedCategory.braidedCategory'
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := _root_.DerivedCategory.braidedCategory'
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  let U := Etale.ordinaryFinitePullback A f
  let V := Etale.dualizingComplex A g
  let W := Etale.dualizingComplex A f
  let H := Etale.dualizingComplex A (f ≫ g)
  let μ := finiteMu A f g hR
  let B := (Etale.ordinaryFinitePullback A g).obj K₀
  let P := (Etale.ordinaryFinitePullback A (f ≫ g)).obj K₀
  let Q := (Etale.rightDerivedUpperShriek A g).obj K₀
  let R := (Etale.rightDerivedUpperShriek A f).obj Q
  let γ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K₀
  have ho : ah.inv ≫ μ.hom =
      split.hom ≫ (U.map ag.inv ▷ Lf) ≫ U.obj V ◁ af.inv := by
    simpa only [Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map] using hor
  have ht := finiteRightComposition A f g hR K₀
  have hp := ((Etale.leftDerivedUpperStarTensorNatIso
    (ModuleCat.{u + 1} A) f).inv.app B).naturality ag.inv
  change U.obj B ◁ U.map ag.inv ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f B V).inv =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f B Lg).inv ≫
      U.map (B ◁ ag.inv) at hp
  have hn₀ := reassociate_naturality U B P γ ag.inv af.inv
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f B) hp
  have hn : P ◁ (U.map ag.inv ▷ Lf) ≫ P ◁ (U.obj V ◁ af.inv) ≫
      (finiteReassociate A f g K₀ V W).hom =
    (finiteReassociate A f g K₀ Lg Lf).hom ≫
      (U.map (B ◁ ag.inv) ▷ Lf) ≫ U.obj (B ⊗ V) ◁ af.inv := by
    simp only [finiteReassociate,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      Functor.mapIso_hom, MonoidalCategory.tensorHom_def,
      whiskerLeft_comp, Functor.comp_obj, Category.assoc] at hn₀ ⊢
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let decls := (← Lean.getLCtx).decls.toList.filterMap id
      let some h := decls.find? (fun h ↦ h.userName.eraseMacroScopes == `hn₀) |
        throwError "no reassociation naturality equation"
      let eq ← tensorCongrHEq target (← Lean.instantiateMVars h.type)
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
      let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, h.toExpr]
      (← Lean.Elab.Tactic.getMainGoal).assign pf
  have hg := gamma_of_tensor_composition U B V Lg Q P H Lh W Lf R
    μ ah ag af split
    (finiteTensor A (f ≫ g) K₀ ≫ (finiteCompositor A f g).hom.app K₀)
    (finiteTensor A g K₀) (finiteTensor A f Q)
    (finiteReassociate A f g K₀ V W).hom
    (finiteReassociate A f g K₀ Lg Lf).hom ho ht hn
  dsimp only [U, V, W, H, μ, B, P, Q, R, γ] at hg
  simp only [Etale.FiniteSmoothPurity.gamma, Etale.FiniteSmoothPurity.puritySource,
    finiteTensor,
    Functor.comp_obj, Functor.flip_obj_obj,
    Category.assoc] at hg ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `hg) |
      throwError "no normalized tensor equation"
    let eq ← tensorCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

end LeftCalculus
end TensorCalculus

section TensorClauseProof
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

/-- The tensor-mate equation and its gamma consequence in the finite composition-factor
package: clause (2) of `FiniteEquations` and the final gamma equation, for any
invertibility witness of rho and assuming the orientation equation of clause (1).
Source: blueprint sk-prop-sp-composition-factors.proof.md, (2) and final paragraph.
Proof:
1. Transpose under the composite compact-support adjunction. The counit identity
for rightAdjointUniq identifies the specified finiteCompositor. Invert the canonical
chosen-compactification projection composition square and apply the ambient tensor
associativity calculation. This gives the coefficient-first tensor equation using
only the supplied invertibility of rho.
2. The canonical derived braiding identifies finiteTensor with the coefficient-first
mate. Naturality, the hexagon identities and braidedness of derived pullback put the
three tensor factors in the order of finiteReassociate, giving the tensor equation.
3. The finite Tate line is bounded below. Transport its bound through ah and mu,
then use injectivity of the bounded-below comparison Hom map to recover the ordinary
orientation equation from hor. Substitute it in gamma_h and use the tensor equation.
Naturality of the specified reassociation and tensor interchange give gamma_g and
gamma_f. Applying comparison.map proves both displayed equations for every origin K.
(blueprint: lem-sp-composition-finite-tensor-gamma-clause-j2). -/
theorem finiteTensorClause (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsSeparated f] [IsSeparated g]
    [QuasiCompact g] (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (hA : ((ell ^ r : ℕ) : A) = 0)
    (df : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (dg : Etale.FiniteRingSectionDeformation.Geometry e
      (pullback.fst g g) (pullback.diagonal g))
    (dh : Etale.FiniteRingSectionDeformation.Geometry (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)))
    (af : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d)
    (ag : Etale.dualizingComplex A g ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA Y e)
    (ah : Etale.dualizingComplex A (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X (d + e))
    (_hf : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA f d df
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) af)
    (_hg : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA g e dg
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) ag)
    (_hh : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA (f ≫ g) (d + e) dh
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ah) (hR : IsIso (finiteRho A f g))
    (hor : (Etale.FiniteSmoothPurity.comparison A X).map
        (ah.inv ≫ (finiteMu A f g hR).hom) =
      (Etale.FiniteSmoothPurity.comparison A X).map
        ((finiteLineSplit A f (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA
          ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
            (Y ↘ Spec (.of D.k))) e d).hom ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
            ((Etale.ordinaryFinitePullback A f).map ag.inv)).app _ ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).map af.inv)) :
    ∀ (K : Etale.FiniteSmoothPurity.proCategory A Z),
      Etale.FiniteSmoothPurity.IsCtf A Z K →
      (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A (f ≫ g)).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))).map
                ((finiteMu A f g hR).inv) ≫
            finiteTensor A (f ≫ g) ((Etale.FiniteSmoothPurity.origin A Z).obj K) ≫
            (finiteCompositor A f g).hom.app ((Etale.FiniteSmoothPurity.origin A Z).obj K)) =
        (Etale.FiniteSmoothPurity.comparison A X).map
          ((finiteReassociate A f g ((Etale.FiniteSmoothPurity.origin A Z).obj K)
            (Etale.dualizingComplex A g)
            (Etale.dualizingComplex A f)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
              ((Etale.ordinaryFinitePullback A f).map
                (finiteTensor A g ((Etale.FiniteSmoothPurity.origin A Z).obj K)))).app _ ≫
            finiteTensor A f
              ((Etale.rightDerivedUpperShriek A g).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))) ∧
      (Etale.FiniteSmoothPurity.comparison A X).map
          (Etale.FiniteSmoothPurity.gamma A (f ≫ g) _ ah
              ((Etale.FiniteSmoothPurity.origin A Z).obj K) ≫
            (finiteCompositor A f g).hom.app ((Etale.FiniteSmoothPurity.origin A Z).obj K)) =
        (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A (f ≫ g)).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))).map
              (finiteLineSplit A f (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA
              ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
                (Y ↘ Spec (.of D.k))) e d).hom ≫
            (finiteReassociate A f g ((Etale.FiniteSmoothPurity.origin A Z).obj K)
              (Etale.FiniteSmoothPurity.line A (ell ^ r) hA Y e)
              (Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
              ((Etale.ordinaryFinitePullback A f).map
                (Etale.FiniteSmoothPurity.gamma A g _ ag
                  ((Etale.FiniteSmoothPurity.origin A Z).obj K)))).app _ ≫
            Etale.FiniteSmoothPurity.gamma A f _ af
              ((Etale.rightDerivedUpperShriek A g).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))) := by
  let U := Etale.ordinaryFinitePullback A f
  let V := Etale.dualizingComplex A g
  let Lf := Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d
  let μ := finiteMu A f g hR
  let split := finiteLineSplit A f (ell ^ r)
    (pow_pos (Fact.out : ell.Prime).pos r) hA
    ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
      (Y ↘ Spec (.of D.k))) e d
  have hpL := DiagonalAffineTrace.coefficientPlus A (ell ^ r)
    (pow_pos (Fact.out : ell.Prime).pos r) hA X
    ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
      (X ↘ Spec (.of D.k))) (d + e)
  have hpH := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso ah.symm hpL
  have hpM := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso μ hpH
  have ho : ah.inv ≫ μ.hom = split.hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map (U.map ag.inv)).app Lf ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj (U.obj V)).map af.inv := by
    apply (bijective_comparisonUpperStar_mapDerivedCategory_map
      (A := ModuleCat.{u + 1} A) (X := X) _ _ hpM).injective
    exact hor
  intro K _hK
  let K₀ := (Etale.FiniteSmoothPurity.origin A Z).obj K
  have ht := finiteRightComposition A f g hR K₀
  constructor
  · exact congrArg (Etale.FiniteSmoothPurity.comparison A X).map ht
  · apply congrArg (Etale.FiniteSmoothPurity.comparison A X).map
    exact finiteGammaComposition A f g af ag ah hR split ho K₀

end TensorClauseProof

/-- The orientation equation in the finite composition-factor package: rho is invertible
and, in comparison coordinates, ah^{-1} followed by mu is the canonical shifted-Tate
splitting followed by f^*(ag^{-1}) tensor af^{-1} (clause (1) of `FiniteEquations`).
Source: blueprint sk-prop-sp-composition-factors.proof.md, (1).
Proof:
1. rho = t_{f, omega_g} is invertible by thm-asd-smooth-tensor (the hypotheses of
lem-pur-finite-setting-comparison-hypotheses make f compactifiable and ell^r invertible).
2. For R = Z/ell^r, lem-pur-composition-model-orientation-descent (E = Q_ell) gives the
orientation equation for the normalized orientations of det-sp-finite-general-ring after
inversion and the switch of the two even line blocks (sign (-1)^{(2d)(2e)} = 1),
including d = 0, e = 0 and empty X. With `finiteTensorClause` at R this gives the
gamma equation at the unit 1_R, where gamma_a(1) is the inverse orientation.
3. For A with ell^r A = 0 put S = - tensor_R^L A. The compositor transposes of
lem-sp-finite-adjoint-compositor-transposes, with the coefficient composition equation
of lem-sp-et-proet-coefficient-compatibility, give c_A u_h = G_{f,A}(u_g) u_f S(c_R).
Apply it at 1_R; the purity equations of det-sp-reduction-compatibilities for h, g, f
and naturality of gamma_{f,A} at u_g(1_R) transport the unit gamma equation to A; the
sources agree under the comparisons of det-sp-scalar-extension-functor (no flatness).
4. Replace gamma_{h,A}(1), gamma_{g,A}(1) by the inverse orientations and expand
gamma_{f,A}(omega_g) = rho (1 tensor af^{-1}); cancelling c_1 gives the equation.
(blueprint: lem-sp-composition-finite-orientation-clause-j2). -/
theorem finiteOrientationClause (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsSeparated f] [IsSeparated g]
    [QuasiCompact g] (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (hA : ((ell ^ r : ℕ) : A) = 0)
    (df : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (dg : Etale.FiniteRingSectionDeformation.Geometry e
      (pullback.fst g g) (pullback.diagonal g))
    (dh : Etale.FiniteRingSectionDeformation.Geometry (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)))
    (af : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d)
    (ag : Etale.dualizingComplex A g ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA Y e)
    (ah : Etale.dualizingComplex A (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X (d + e))
    (_hf : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA f d df
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) af)
    (_hg : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA g e dg
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) ag)
    (_hh : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA (f ≫ g) (d + e) dh
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ah) :
      ∃ hR : IsIso (finiteRho A f g),
    (Etale.FiniteSmoothPurity.comparison A X).map
        (ah.inv ≫ (finiteMu A f g hR).hom) =
      (Etale.FiniteSmoothPurity.comparison A X).map
        ((finiteLineSplit A f (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA
          ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
            (Y ↘ Spec (.of D.k))) e d).hom ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
            ((Etale.ordinaryFinitePullback A f).map ag.inv)).app _ ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).map af.inv) := by
  sorry

/-- Composition of the specified diagonal orientations and tensor transposes, at every
finite ell-primary ring. Equalities are in the actual pro-etale derived category via
its canonical ordinary-etale coordinates, retaining every intrinsic Dctf input.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors).

Proof: `finiteOrientationClause` gives the invertibility of rho and clause (1);
`finiteTensorClause`, applied to that witness and that equation, gives clause (2) and the
gamma consequence for every constructible finite-Tor K. Their conjunction is
`FiniteEquations`. -/
theorem finite (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsSeparated f] [IsSeparated g]
    [QuasiCompact g] (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (hA : ((ell ^ r : ℕ) : A) = 0)
    (df : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (dg : Etale.FiniteRingSectionDeformation.Geometry e
      (pullback.fst g g) (pullback.diagonal g))
    (dh : Etale.FiniteRingSectionDeformation.Geometry (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)))
    (af : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d)
    (ag : Etale.dualizingComplex A g ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA Y e)
    (ah : Etale.dualizingComplex A (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X (d + e))
    (_hf : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA f d df
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) af)
    (_hg : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA g e dg
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) ag)
    (_hh : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA (f ≫ g) (d + e) dh
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ah) :
    FiniteEquations A f g (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) d e af ag ah := by
  obtain ⟨hR, hor⟩ := finiteOrientationClause A f g D ell hne r hr d e hA df dg dh af ag ah
    _hf _hg _hh
  have ht := finiteTensorClause A f g D ell hne r hr d e hA df dg dh af ag ah _hf _hg _hh hR hor
  exact ⟨hR, hor, ht⟩

end Finite

section Towers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Y Z V W U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  (jf : X ⟶ V) [IsOpenImmersion jf] (pf : V ⟶ Y) [IsProper pf]
  (jg : Y ⟶ W) [IsOpenImmersion jg] (pg : W ⟶ Z) [IsProper pg]
  (jh : X ⟶ U) [IsOpenImmersion jh] (ph : U ⟶ Z) [IsProper ph]
  [QuasiCompact (jf ≫ pf)] [QuasiCompact (jg ≫ pg)] [QuasiCompact (jh ≫ ph)]
  [HasCompactification (jf ≫ pf)] [HasCompactification (jg ≫ pg)]
  [HasCompactification (jh ≫ ph)]
  (d e : ℕ)
  (wf : SpChartAdmissibility.Twists l E X)
  (wg : SpChartAdmissibility.Twists l E Y)
  (wh : SpChartAdmissibility.Twists l E X)
  (Pf : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jf pf))
  (Pg : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jg pg))
  (Ph : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jh ph))
  (af : SpTowerGamma.Purity l E b o q jf pf d wf Pf.closed Pf.right Pf.adj Pf.levels)
  (ag : SpTowerGamma.Purity l E b o q jg pg e wg Pg.closed Pg.right Pg.adj Pg.levels)
  (ah : SpTowerGamma.Purity l E b o q jh ph (d + e) wh
    Ph.closed Ph.right Ph.adj Ph.levels)
  (c : Ph.right ≅ Pg.right ⋙ Pf.right)

/-- The actual tower tensor mate supplied by gamma, before any level evaluation.
Source: composition-factors, t_f (blueprint: det-sp-composition-factors). -/
def towerTensorF (K : SpTowerCalculus.C l E b q Y) :=
  SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization jf pf)
    af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem K
      (af.tensor_mem K) (af.projection_iso K)

/-- The actual tower tensor mate for g.
Source: composition-factors, t_g (blueprint: det-sp-composition-factors). -/
def towerTensorG (K : SpTowerCalculus.C l E b q Z) :=
  SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization jg pg)
    ag.tensorX ag.tensorY Pg.closed Pg.right Pg.adj ag.unit_mem K
      (ag.tensor_mem K) (ag.projection_iso K)

/-- The actual tower tensor mate for h.
Source: composition-factors, t_h (blueprint: det-sp-composition-factors). -/
def towerTensorH (K : SpTowerCalculus.C l E b q Z) :=
  SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization jh ph)
    ah.tensorX ah.tensorY Ph.closed Ph.right Ph.adj ah.unit_mem K
      (ah.tensor_mem K) (ah.projection_iso K)

/-- The coefficient object omega_g as an object of the full uniform tower category.
Source: composition-factors, omega_g (blueprint: det-sp-composition-factors). -/
def towerOmegaG := Pg.right.obj ⟨SpTowerGamma.originalUnit l E b q Z, ag.unit_mem⟩

/-- Rho is the existing tower tensor mate at omega_g, not a chosen isomorphism.
Source: composition-factors, rho (blueprint: det-sp-composition-factors). -/
def towerRho := towerTensorF l E b o q jf pf d wf Pf af
  (towerOmegaG l E b o q jg pg e wg Pg ag)

/-- Mu is c at the unit followed by the inverse of that particular rho.
Source: composition-factors, mu (blueprint: det-sp-composition-factors). -/
def towerMu (hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag)) :=
  letI := hR
  (SpTowerGamma.realization l E b q X).mapIso
      (c.app ⟨SpTowerGamma.originalUnit l E b q Z, ag.unit_mem⟩) ≪≫
    (asIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag)).symm

/-- The canonical tower pullback compositor and K-flat tensor reassociation.
Source: composition-factors, clause (2) (blueprint: det-sp-composition-factors). -/
def towerReassociate (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (K : SpTowerShriek.D l E Z) (M : SpTowerShriek.D l E Y)
    (N : SpTowerShriek.D l E X) :=
  (SpTowerShriek.tensor l E b X).mapIso
      (Iso.prod
        (((eqToIso (congrArg (fun v ↦ SpTowerShriek.pull l E b (o.geometry v))
            hcomp.symm)).app K) ≪≫ (o.comp (jf ≫ pf) (jg ≫ pg)).symm.app K)
        (Iso.refl ((SpTowerShriek.tensor l E b X).obj
          ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj M, N)))) ≪≫
    ((b.calculus X).closed.monoidal.associator _ _ _).symm ≪≫
    (SpTowerShriek.tensor l E b X).mapIso
      (Iso.prod
        (((o.geometry (jf ≫ pf)).tensorPullback).symm.app
          ((SpTowerShriek.pull l E b (o.geometry (jg ≫ pg))).obj K, M)) (Iso.refl N))

/-- Canonical finite evaluation of the shifted-Tate splitting in the tower category.
This pins the splitting by the specified root, unit, pullback and K-flat tensor words,
including rank zero; no arbitrary endpoint isomorphism is admitted.
Source: composition-factors, clause (1) (blueprint: det-sp-composition-factors). -/
def TowerSplitNormalized
    (s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d)) : Prop :=
  ∀ n : ℕ,
    SpTowerP1.WordComparison l E n
      (SpTowerGamma.coefficientWord l E b X wh ah.roots n
        (ah.unitsX n) (ah.coefficientsX n) (ah.tensors n) (d + e))
      (SpTowerP1.tensorWord l E n b (af.tensors n)
        (SpTowerP1.pullWord l E n b (o.geometry (jf ≫ pf)) (af.geometry n)
          (SpTowerGamma.coefficientWord l E b Y wg ag.roots n
            (ag.unitsX n) (ag.coefficientsX n) (ag.tensors n) e))
        (SpTowerGamma.coefficientWord l E b X wf af.roots n
          (af.unitsX n) (af.coefficientsX n) (af.tensors n) d)) s.hom
      (finiteLineSplit (SpTowerP1.levelRing l E n) (jf ≫ pf) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
        (ag.unitsX n) e d).hom

/-- Both tower equations and their gamma consequence, in the actual ordinary derived
category of varying-ring systems. The input category has uniform constructibility and
Tor bounds; it imposes no derived reduction isomorphism on the input tower.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors). -/
def TowerEquations (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph) : Prop :=
  ∃ s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d),
    TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah s ∧
    ∃ hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag),
      ah.orientation.hom ≫
          (towerMu l E b o q jf pf jg pg jh ph d e wf wg Pf Pg Ph af ag c hR).hom =
        s.hom ≫ (SpTowerShriek.tensor l E b X).map
          (Prod.mkHom
            ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map ag.orientation.hom)
            af.orientation.hom) ∧
      ∀ K : SpTowerCalculus.C l E b q Z,
        (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom (𝟙 ((SpTowerShriek.pull l E b (o.geometry (jh ≫ ph))).obj
                ((SpTowerGamma.realization l E b q Z).obj K)))
              (towerMu l E b o q jf pf jg pg jh ph d e wf wg
                Pf Pg Ph af ag c hR).inv) ≫
            towerTensorH l E b o q jh ph d e wh Ph ah K ≫
      (SpTowerGamma.realization l E b q X).map (c.hom.app K) =
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            ((SpTowerGamma.realization l E b q Y).obj
              (towerOmegaG l E b o q jg pg e wg Pg ag))
            ((SpTowerGamma.exceptional l E b q Pf.right).obj
              ⟨SpTowerGamma.originalUnit l E b q Y, af.unit_mem⟩)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (towerTensorG l E b o q jg pg e wg Pg ag K)) (𝟙 _)) ≫
          towerTensorF l E b o q jf pf d wf Pf af (Pg.right.obj K) ∧
        SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jh ph) wh (d + e)
            ah.tensorX ah.tensorY Ph.closed Ph.right Ph.adj ah.unit_mem ah.orientation
            K (ah.tensor_mem K) (ah.projection_iso K) ≫
            (SpTowerGamma.realization l E b q X).map (c.hom.app K) =
          (SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _) s.hom) ≫
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            (SpTowerGamma.orderedLine l E b Y wg e)
            (SpTowerGamma.orderedLine l E b X wf d)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jg pg) wg e
                  ag.tensorX ag.tensorY Pg.closed Pg.right Pg.adj ag.unit_mem ag.orientation
                  K (ag.tensor_mem K) (ag.projection_iso K))) (𝟙 _)) ≫
          SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jf pf) wf d
            af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem af.orientation
            (Pg.right.obj K) (af.tensor_mem (Pg.right.obj K))
            (af.projection_iso (Pg.right.obj K))

/-- Composition of the normalized tower orientations.
Source: blueprint sk-prop-sp-composition-factors.proof.md, (1).
Proof: construct the ordered shifted-Tate splitting by concatenation of Tate powers.
Its transition compatibility follows from pullback and tensor coherence
(lem-pur-cochain-pullback-tensor-coherence, lem-pur-derived-tensor-additive-constraints;
even shifts give sign +1), so its finite values are the canonical finite splittings
(TowerSplitNormalized). The projection formula at omega_g is invertible by
lem-sp-twisted-pullback-tower-domain and det-sp-tower-shriek-levels, so rho is
invertible. Evaluate the quotient of the two orientation maps at every finite level
(lem-sp-tower-adjoint-compositor-realization, det-sp-tower-gamma,
lem-sp-tower-tensor-transpose-evaluation) and apply `finiteOrientationClause` and
`finiteTensorClause` at O_E/ell^n. After removing the common even shift these are
maps of degree-zero rank-one sheaf towers. Single-complex full faithfulness
(lem-weil-pbc-derived-single-fully-faithful) and componentwise equality identify them,
including zero ranks and empty schemes. No faithfulness of evaluation on arbitrary
derived maps is used.
(blueprint: lem-sp-composition-tower-orientation-clause-j2). -/
theorem towerOrientationClause (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
    [IsSeparated (jf ≫ pf)] [IsSeparated (jg ≫ pg)]
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (pres : SpTowerCalculus.Preservation l E D.k b o q)
    (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
    (alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
      TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph)
    (_ha : ∀ M, (alpha.hom.app M).hom =
      (cal.composition.composition (jf ≫ pf) (jg ≫ pg) (jh ≫ ph) hcomp
        (SpTowerGamma.factorization jf pf) (SpTowerGamma.factorization jg pg)
        (SpTowerGamma.factorization jh ph)).hom.app M)
    (_hc : ∀ K,
      (TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg).map (c.hom.app K) ≫
          (Pf.adj.comp Pg.adj).counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) :
  ∃ s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d),
    TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah s ∧
    ∃ hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag),
      ah.orientation.hom ≫
          (towerMu l E b o q jf pf jg pg jh ph d e wf wg Pf Pg Ph af ag c hR).hom =
        s.hom ≫ (SpTowerShriek.tensor l E b X).map
          (Prod.mkHom
            ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map ag.orientation.hom)
            af.orientation.hom) := by
  sorry

/-- Tensor composition and its gamma consequence for a normalized tower splitting.
Source: blueprint sk-prop-sp-composition-factors.proof.md, (2) and final paragraph.
Proof: the uniform domains and projection inverses are those of
lem-sp-tower-adjoint-compositor-realization, lem-sp-twisted-pullback-tower-domain and
det-sp-tower-shriek-levels. Express each tensor mate as the transpose of inverse
projection followed by the counit. Projection coherence on the ringed system topos
(lem-coef-semilinear-derived-sections, lem-sf-open-tensor-normalization,
lem-pur-unit-adjunct-tensor-action, lem-sfb-ringed-projection-tensor-composition,
lem-weil-pbc-ringed-projection-mate-exact), proper/open projection composition
(lem-cbc-compactifiable-compatible-tower, lem-sp-tower-composition-projection-mate) and
the counit normalization of c identify the two composite transposes
(lem-pur-composite-tensor-transpose). Injectivity of the composite adjunction
bijection gives the tensor identity in the actual derived tower category. Substitute
the assumed orientation equation in gamma_h. Naturality of the tensor mate
(lem-sp-tower-tensor-transpose-evaluation, det-sp-tower-gamma) moves
gamma_g through its pullback and gives gamma_f after reassociation. The two even
shifts have sign +1. All inputs retain their uniform constructibility and Tor bounds.
(blueprint: lem-sp-composition-tower-tensor-gamma-clause-j2). -/
theorem towerTensorGammaClause (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
    [IsSeparated (jf ≫ pf)] [IsSeparated (jg ≫ pg)]
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (pres : SpTowerCalculus.Preservation l E D.k b o q)
    (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
    (alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
      TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph)
    (_ha : ∀ M, (alpha.hom.app M).hom =
      (cal.composition.composition (jf ≫ pf) (jg ≫ pg) (jh ≫ ph) hcomp
        (SpTowerGamma.factorization jf pf) (SpTowerGamma.factorization jg pg)
        (SpTowerGamma.factorization jh ph)).hom.app M)
    (_hc : ∀ K,
      (TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg).map (c.hom.app K) ≫
          (Pf.adj.comp Pg.adj).counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K)
    (s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d))
    (hs : TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh
      Pf Pg Ph af ag ah s)
    (hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag))
    (hor : ah.orientation.hom ≫
          (towerMu l E b o q jf pf jg pg jh ph d e wf wg Pf Pg Ph af ag c hR).hom =
        s.hom ≫ (SpTowerShriek.tensor l E b X).map
          (Prod.mkHom
            ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map ag.orientation.hom)
            af.orientation.hom)) :
      ∀ K : SpTowerCalculus.C l E b q Z,
        (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom (𝟙 ((SpTowerShriek.pull l E b (o.geometry (jh ≫ ph))).obj
                ((SpTowerGamma.realization l E b q Z).obj K)))
              (towerMu l E b o q jf pf jg pg jh ph d e wf wg
                Pf Pg Ph af ag c hR).inv) ≫
            towerTensorH l E b o q jh ph d e wh Ph ah K ≫
      (SpTowerGamma.realization l E b q X).map (c.hom.app K) =
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            ((SpTowerGamma.realization l E b q Y).obj
              (towerOmegaG l E b o q jg pg e wg Pg ag))
            ((SpTowerGamma.exceptional l E b q Pf.right).obj
              ⟨SpTowerGamma.originalUnit l E b q Y, af.unit_mem⟩)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (towerTensorG l E b o q jg pg e wg Pg ag K)) (𝟙 _)) ≫
          towerTensorF l E b o q jf pf d wf Pf af (Pg.right.obj K) ∧
        SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jh ph) wh (d + e)
            ah.tensorX ah.tensorY Ph.closed Ph.right Ph.adj ah.unit_mem ah.orientation
            K (ah.tensor_mem K) (ah.projection_iso K) ≫
            (SpTowerGamma.realization l E b q X).map (c.hom.app K) =
          (SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _) s.hom) ≫
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            (SpTowerGamma.orderedLine l E b Y wg e)
            (SpTowerGamma.orderedLine l E b X wf d)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jg pg) wg e
                  ag.tensorX ag.tensorY Pg.closed Pg.right Pg.adj ag.unit_mem ag.orientation
                  K (ag.tensor_mem K) (ag.projection_iso K))) (𝟙 _)) ≫
          SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jf pf) wf d
            af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem af.orientation
            (Pg.right.obj K) (af.tensor_mem (Pg.right.obj K))
            (af.projection_iso (Pg.right.obj K)) := by
  sorry

/-- Composition of the diagonal orientations and actual tensor mates for ordinary
coefficient towers. All arrows are ordinary derived-tower arrows; neither the input nor
its morphisms are replaced by a family of levelwise arrows.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors).

Proof: `towerOrientationClause` gives the ordered splitting s, its normalization, the
invertibility of rho and clause (1); `towerTensorGammaClause`, applied to these, gives
clause (2) and the gamma consequence on every uniform constructible finite-Tor tower.
Their conjunction is `TowerEquations`. -/
theorem towers (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
    [IsSeparated (jf ≫ pf)] [IsSeparated (jg ≫ pg)]
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (pres : SpTowerCalculus.Preservation l E D.k b o q)
    (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
    (alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
      TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph)
    (_ha : ∀ M, (alpha.hom.app M).hom =
      (cal.composition.composition (jf ≫ pf) (jg ≫ pg) (jh ≫ ph) hcomp
        (SpTowerGamma.factorization jf pf) (SpTowerGamma.factorization jg pg)
        (SpTowerGamma.factorization jh ph)).hom.app M)
    (_hc : ∀ K,
      (TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg).map (c.hom.app K) ≫
          (Pf.adj.comp Pg.adj).counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) :
    TowerEquations l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah c hcomp := by
  obtain ⟨s, hs, hR, hor⟩ := towerOrientationClause (l := l) (E := E) (b := b) (o := o) (q := q)
    (jf := jf) (pf := pf) (jg := jg) (pg := pg) (jh := jh) (ph := ph)
    (d := d) (e := e) (wf := wf) (wg := wg) (wh := wh)
    (Pf := Pf) (Pg := Pg) (Ph := Ph) (af := af) (ag := ag) (ah := ah) (c := c)
    D _hl hcomp z pres cal alpha _ha _hc
  have ht := towerTensorGammaClause (l := l) (E := E) (b := b) (o := o) (q := q)
    (jf := jf) (pf := pf) (jg := jg) (pg := pg) (jh := jh) (ph := ph)
    (d := d) (e := e) (wf := wf) (wg := wg) (wh := wh)
    (Pf := Pf) (Pg := Pg) (Ph := Ph) (af := af) (ag := ag) (ah := ah) (c := c)
    D _hl hcomp z pres cal alpha _ha _hc s hs hR hor
  exact ⟨s, hs, hR, hor, ht⟩

end Towers
end SpCompositionFactors
end AlgebraicGeometry.ProEtale
