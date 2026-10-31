/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
import WeilConjectures.AlgebraicGeometry.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientTensorCtf
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.FiniteSiteCounitProjectionTransport
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCompactProjectionFormula
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Adjunction.LeftCoefficientProjectionAction
import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.CompactSupportSiteCoherence
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionCoherence
import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
import WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.LargeHomSolutionSet
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
import Mathlib.Algebra.Module.ULift
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import WeilConjectures.CategoryTheory.CoproductsOfCopowers
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionForward
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord
import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import WeilConjectures.AlgebraicGeometry.SfGraphWordProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.SfGraphSecondProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphMiddleProjectionSquare
import WeilConjectures.AlgebraicGeometry.ProperOpenFactorProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.SfGraphCompositionTailProjection
import WeilConjectures.AlgebraicGeometry.SfGraphInterchangeProjection
import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenTensorSquare
import WeilConjectures.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMapsSupplement
import WeilConjectures.AlgebraicGeometry.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.Compactification.BaseChange
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCartesianNormalization
import WeilConjectures.AlgebraicGeometry.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenCompositionSupplement
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCubeNormalization
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPastingSupplement
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonInterchange
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSidePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkFirstLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSecondLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductRowPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductInterchange
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductGeometry
import WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientFirstSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition
import WeilConjectures.AlgebraicGeometry.DerivedCompactSupportCompositionCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientSecondSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSourcePasting
import WeilConjectures.AlgebraicGeometry.OpenExchangeTowerSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSquarePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkLift
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkSquare
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphDiagonalNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport
import WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatumStages
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Domains of the normalized compact-support double transpose

Source: main-20261015, sk-prop-cohsm, second paragraph, composition comparison
(blueprint: lem-pur-compact-support-composite-transpose-domains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CompactSupportTranspose

attribute [local irreducible] _root_.DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

/-- Ordinary fixed-scalar derived categories on the actual small pro-etale sites.
Source: sk-prop-cohsm, finite stage
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
abbrev D (P : PurityFiniteSetting.{u}) (T : SixFunctorSpace P.field) :=
  _root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology T.obj.left) (ModuleCat.{u + 1} P.Coefficient))

/-- A separated finite-type arrow and the specified bounded compactification.
There is no absolute separatedness condition on either finite-type field scheme.
Source: sk-prop-cohsm, composition comparison
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
structure Edge (P : PurityFiniteSetting.{u}) (X Y : SixFunctorSpace P.field) where
  f : X ⟶ Y
  separated : IsSeparated f.hom.left
  finiteType : LocallyOfFiniteType f.hom.left
  quasiCompact : QuasiCompact f.hom.left
  compactification : Compactification f.hom.left
  dimension : ℕ
  dimension_le : topologicalKrullDim compactification.Z ≤ (dimension : WithBot ℕ∞)

attribute [instance] Edge.separated Edge.finiteType Edge.quasiCompact

variable (P : PurityFiniteSetting.{u})
variable {X Y Z : SixFunctorSpace P.field}

/-- The existing bounded constructible full domain, in fixed coefficients.
Source: sk-prop-cohsm, the module-input domain
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
abbrev BC (T : SixFunctorSpace P.field) : ObjectProperty (D P T) :=
  DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) T.obj.left

/-- The existing finite-Tor full coefficient domain.
Source: sk-prop-cohsm, the coefficient-input domain
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
abbrev CTF (T : SixFunctorSpace P.field) : ObjectProperty (D P T) :=
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) T.obj.left

/-- The canonical derived inverse image S_h.
Source: sk-prop-cohsm, S_h = Lh^*
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def S (e : Edge P X Y) : D P Y ⥤ D P X :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) e.f.hom.left).leftDerivedFunctor

/-- The specified proper/open compact-support functor P_h.
Source: sk-prop-cohsm, P_h = Rh_!
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def image (e : Edge P X Y) : D P X ⥤ D P Y :=
  rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) e.compactification

/-- The unique ordinary-etale right adjoint at the retained compactification.
Source: sk-prop-cohsm, normalized etale-origin adjunction
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def etaleG (e : Edge P X Y) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient e.compactification
  (Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) e.compactification).rightAdjoint

/-- The canonical transported exceptional functor G_h at the given compactification.
Source: sk-prop-cohsm, G_h = nu^* h^times Rnu_*
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def G (e : Edge P X Y) : D P Y ⥤ D P X :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient e.compactification
  sfFiniteExceptionalAt P.Coefficient e.compactification

/-- The relative dualizing object W_h = G_h A.
Source: sk-prop-cohsm, coefficient-unit specialization
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
abbrev W (e : Edge P X Y) : D P X := (G P e).obj (𝟙_ (D P Y))

/-- Quasi-compactness of the target follows from its finite-type field structure.
Source: sk-prop-cohsm, finite-type schemes
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
instance targetCompact (T : SixFunctorSpace P.field) : CompactSpace T.obj.left :=
  letI : QuasiCompact T.obj.hom := T.property.2
  QuasiCompact.compactSpace_of_compactSpace T.obj.hom

/-- The actual bounded-below etale antecedent of the exceptional image.
Source: sk-prop-cohsm, normalized Hom domains
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def exceptionalOrigin (e : Edge P X Y)
    (B : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y.obj.left) (ModuleCat.{u + 1} P.Coefficient))) :
    _root_.DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient e.compactification
  ⟨(etaleG P e).obj
    ((comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y.obj.left).rightDerivedFunctor.obj
      B.obj), specifiedExceptionalEtale_boundedBelow P.Coefficient e.compactification B⟩

/-- The retained witness of G_h B uses its literal antecedent and the identity comparison.
Source: sk-prop-cohsm, bounded-below origins.
Proof: use exceptionalOrigin as the etale antecedent; the comparison is the identity
by the definition of G. Its bounded-below property is specifiedExceptionalEtale_boundedBelow.
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
theorem exceptionalOriginProperty (e : Edge P X Y) (B : D P Y)
    (hB : _root_.DerivedCategory.TStructure.t.plus B) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X.obj.left
      ((G P e).obj B) := by
  refine ⟨(exceptionalOrigin P e ⟨B, hB⟩).obj,
    (exceptionalOrigin P e ⟨B, hB⟩).property, ⟨Iso.refl _⟩⟩

/-- The specified Hom bijection, computed at any retained source origin. Its value is
canonical: each change of origin is conjugated through the same comparison isomorphism.
Source: sk-prop-cohsm, thm-sf-ambient-adjoint-class normalization
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def hom (e : Edge P X Y) {M : D P X}
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
    {B : D P Y} (hB : _root_.DerivedCategory.TStructure.t.plus B) :
    ((image P e).obj M ⟶ B) ≃ (M ⟶ (G P e).obj B) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient e.compactification
  let L := Classical.choose hM
  let hL := (Classical.choose_spec hM).1
  let a := Classical.choice (Classical.choose_spec hM).2
  specifiedExceptionalHomEquiv P.Coefficient e.compactification
    ⟨M, DerivedCategory.plusEtaleOrigin.plus hM⟩ ⟨⟨L, hL⟩, a⟩ ⟨B, hB⟩

/-- The counit is the inverse normalized Hom transpose of the identity.
Source: sk-prop-cohsm, epsilon_h
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def counit (e : Edge P X Y) (B : D P Y)
    (hB : _root_.DerivedCategory.TStructure.t.plus B) :
    (image P e).obj ((G P e).obj B) ⟶ B :=
  (hom P e (exceptionalOriginProperty P e B hB) hB).symm (𝟙 _)


private theorem etaleCTF (T : SixFunctorSpace P.field) (M : D P T)
    (hM : CTF P T M) :
    ∃ L, Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) T.obj.left L ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        T.obj.left).mapDerivedCategory.obj L ≅ M) := by
  obtain ⟨L, hL, ⟨a⟩⟩ := hM.1
  obtain ⟨b, c, ht⟩ := hM.2
  exact ⟨L, ⟨hL, b, c, DerivedCategory.torAmplitudeIn_of_mapDerivedCategory P.Coefficient
    ((DerivedCategory.torAmplitudeIn _ T.obj.left b c).prop_of_iso a.symm ht)⟩, ⟨a⟩⟩

private theorem tensorBC (T : SixFunctorSpace P.field) (B M : D P T)
    (hB : CTF P T B) (hM : BC P T M) : BC P T (B ⊗ M) := by
  let := _root_.DerivedCategory.symmetricCategory
    (Sheaf T.obj.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  obtain ⟨L, hL, ⟨a⟩⟩ := etaleCTF P T B hB
  obtain ⟨N, hN, ⟨b⟩⟩ := hM
  let q := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) L).app N ≪≫ tensorIso a b
  apply (BC P T).prop_of_iso q
  apply DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
  exact (Etale.DerivedCategory.boundedConstructible _ T.obj.left).prop_of_iso
    (β_ N L) (Etale.boundedConstructible_tensor P.Coefficient T.obj.left hN hL.1 hL.2)

private theorem tensorCTF (T : SixFunctorSpace P.field) (B M : D P T)
    (hB : CTF P T B) (hM : CTF P T M) : CTF P T (B ⊗ M) := by
  obtain ⟨L, hL, ⟨a⟩⟩ := etaleCTF P T B hB
  obtain ⟨N, hN, ⟨b⟩⟩ := etaleCTF P T M hM
  let q := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) L).app N ≪≫ tensorIso a b
  exact (CTF P T).prop_of_iso q
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.constructibleFiniteTor_tensor P.Coefficient T.obj.left hL hN))

private theorem pullFiniteTor (e : Edge P X Y) (B : D P Y) (hB : CTF P Y B) :
    CTF P X ((S P e).obj B) := by
  obtain ⟨L, hL, ⟨a⟩⟩ := etaleCTF P Y B hB
  let q := ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
        e.f.hom.left).symm ≪≫ Functor.mapDerivedCategoryCompIso _ _).app L ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) e.f.hom.left).symm.app _ ≪≫
      (S P e).mapIso a
  exact (CTF P X).prop_of_iso q
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.constructibleFiniteTor_mapDerivedCategory_upperStar
        P.Coefficient e.f.hom.left hL))

/-- The coefficient unit has Tor interval [0,0] and is bounded constructible.
Source: sk-prop-cohsm, coefficient-unit instances
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: the constant finite free rank-one sheaf is constructible; its complex is
concentrated in degree zero. Tensoring with it is the identity, giving [0,0]. -/
theorem unitCTF (T : SixFunctorSpace P.field) : CTF P T (𝟙_ (D P T)) := by
  exact (CTF P T).prop_of_iso
    (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient T.obj.left)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.constructibleFiniteTor_tensorUnit P.Coefficient T.obj.left))

/-- The module domain of every inverse projection in the calculation.
Source: sk-prop-cohsm, tensor input domains
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: pullback preserves the coefficient Tor interval and constructibility
(lem-sf-pullback-tor-amplitude). Clause (i) of lem-sf-tensor-ctf makes its tensor
with the bounded constructible module bounded constructible. -/
theorem tensorInputBC (e : Edge P X Y) (B : D P Y) (M : D P X)
    (_hB : CTF P Y B) (_hM : BC P X M) :
    BC P X ((S P e).obj B ⊗ M) := by
  exact tensorBC P X _ M (pullFiniteTor P e B _hB) _hM

/-- Finite-Tor coefficients remain finite Tor in the same tensor inputs.
Source: sk-prop-cohsm, successive coefficient pullbacks and products
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: pullback preserves each Tor interval. Clause (ii) of lem-sf-tensor-ctf
adds the two intervals, and clause (i) supplies bounded constructibility. -/
theorem tensorInputCTF (e : Edge P X Y) (B : D P Y) (M : D P X)
    (_hB : CTF P Y B) (_hM : CTF P X M) :
    CTF P X ((S P e).obj B ⊗ M) := by
  exact tensorCTF P X _ M (pullFiniteTor P e B _hB) _hM

/-- Compact support preserves the bounded constructible module domain.
Source: sk-prop-cohsm, compact-support input domains
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: choose a bounded constructible etale origin, apply fixed-scalar
compact-support finiteness, and transport along the specified comparison at e.
This asserts no finite Tor amplitude for the image. -/
theorem imageBC (e : Edge P X Y) (M : D P X) (_hM : BC P X M) :
    BC P Y ((image P e).obj M) := by
  let := P.finiteComparedInvertibleExponent (𝟙 (Spec (.of P.field.k)))
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2
  let := e.compactification.hasCompactification
  have h := boundedConstructible_rightDerivedLowerShriek P.Coefficient e.f.hom.left
    X.obj.hom Y.obj.hom e.f.hom.w M _hM
  let hM := _hM.plusEtaleOrigin
  let a := ((rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
    e.f.hom.left).mapIso hM.choose_spec.2.some).symm ≪≫
    (rightDerivedLowerShriekCompactificationIso P.Coefficient e.compactification).app
      ⟨hM.choose, hM.choose_spec.1⟩ ≪≫
    (image P e).mapIso hM.choose_spec.2.some
  exact (BC P Y).prop_of_iso a h

/-- Compact support also preserves the full bounded-below etale-origin class.
Source: sk-prop-cohsm, comparison-class composition
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: take the given bounded-below etale antecedent. Etale compact support
preserves a lower bound. The normalized compact-support comparison gives the
required origin isomorphism for its image. -/
theorem imageOrigin (e : Edge P X Y) (M : D P X)
    (_hM : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) X.obj.left M) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Y.obj.left
      ((image P e).obj M) := by
  obtain ⟨L, hL, ⟨a⟩⟩ := _hM
  refine ⟨_, ?_, ⟨(rightDerivedLowerShriekOfCompactificationWitnessIso
    (ModuleCat.{u + 1} P.Coefficient) e.compactification hL a).symm⟩⟩
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) e.compactification).app ⟨L, hL⟩)
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} P.Coefficient) e.compactification).obj ⟨L, hL⟩).property

/-- The specified compactification projection evaluated in its native bifunctor interface.
Source: def-exchange-projection, compactification projection
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def rawProjection (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {V U : Scheme.{u}} {f : V ⟶ U} (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology V) A))
    (B : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
    (rightDerivedLowerShriekOfCompactification A c).obj M ⊗ B ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        (M ⊗ (upperStar A f).leftDerivedFunctor.obj B) :=
  ((projectionMapOfCompactification A c).app M).app B

/-- The canonical symmetry of the existing K-flat derived tensor structure.
Source: sk-prop-cohsm, left-coefficient projection convention
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def braid (T : SixFunctorSpace P.field) (B M : D P T) : B ⊗ M ≅ M ⊗ B :=
  letI := _root_.DerivedCategory.symmetricCategory
    (Sheaf (Scheme.ProEt.topology T.obj.left) (ModuleCat.{u + 1} P.Coefficient))
  β_ B M

/-- The specified forward projection in left-coefficient order, conjugated by symmetry.
Source: def-exchange-projection, finite chosen-compactification projection
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def forwardProjection (e : Edge P X Y) (B : D P Y) (M : D P X) :
    B ⊗ (image P e).obj M ⟶ (image P e).obj ((S P e).obj B ⊗ M) :=
  (braid P Y B ((image P e).obj M)).hom ≫
    rawProjection (ModuleCat.{u + 1} P.Coefficient) e.compactification M B ≫
    (image P e).map (braid P X M ((S P e).obj B)).hom

/-- Invertibility of the specified projection on precisely its finite coefficient domain.
Source: sk-prop-cohsm, inverse projections
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: choose etale representatives of B and M. Tor comparison reflects the
coefficient interval; lem-weil-finite-compact-projection-formula makes the etale
map invertible. Finite-site counit/projection transport identifies its image
with this specified map. Symmetry on both ends preserves invertibility. -/
theorem forwardProjection_isIso (e : Edge P X Y) (B : D P Y) (M : D P X)
    (_hB : CTF P Y B) (_hM : BC P X M) :
    IsIso (forwardProjection P e B M) := by
  have h := hasProjectionFormulaOfCompactification_of_boundedConstructible
    P.Coefficient e.compactification _hM _hB
  let : IsIso (rawProjection (ModuleCat.{u + 1} P.Coefficient)
    e.compactification M B) := h
  unfold forwardProjection
  infer_instance

/-- The actual inverse of the specified forward projection, with left coefficient.
Source: sk-prop-cohsm, pi^h_{B,M}
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def pi (e : Edge P X Y) (B : D P Y) (M : D P X)
    (hB : CTF P Y B) (hM : BC P X M) :
    (image P e).obj ((S P e).obj B ⊗ M) ⟶ B ⊗ (image P e).obj M :=
  letI := forwardProjection_isIso P e B M hB hM
  inv (forwardProjection P e B M)

/-- The counit/projection tensor map in the node's source order.
Source: def-pur-co-smoothness, clause (2)
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def theta (e : Edge P X Y) (hW : CTF P X (W P e))
    (B : D P Y) (hB : CTF P Y B) :
    (S P e).obj B ⊗ W P e ⟶ (G P e).obj B :=
  hom P e (tensorInputBC P e B (W P e) hB hW.1).plusEtaleOrigin hB.plus
    (pi P e B (W P e) hB hW.1 ≫
      B ◁ counit P e (𝟙_ (D P Y)) (unitCTF P Y).plus ≫ (ρ_ B).hom)

/-- The composite arrow with its independently chosen bounded compactification.
Source: sk-prop-cohsm, f,g,gf compactifications
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def compositeEdge (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left)) (n : ℕ)
    (hn : topologicalKrullDim c.Z ≤ (n : WithBot ℕ∞)) : Edge P X Z where
  f := e.f ≫ d.f
  separated := inferInstanceAs (IsSeparated (e.f.hom.left ≫ d.f.hom.left))
  finiteType := inferInstanceAs (LocallyOfFiniteType (e.f.hom.left ≫ d.f.hom.left))
  quasiCompact := inferInstanceAs (QuasiCompact (e.f.hom.left ≫ d.f.hom.left))
  compactification := c
  dimension := n
  dimension_le := hn

/-- The canonical change of compactification on a retained bounded-below etale origin:
the published etale-origin comparison between the two compact-support functors,
conjugated by the retained origin isomorphism.
Source: thm-sf-comp-composition, independence of the compactification
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def originChange {S T : Scheme.{u}} {g : S ⟶ T} [QuasiCompact g]
    (c c' : Compactification g)
    (W : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} P.Coefficient)))
    (hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) S W) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj W ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c').obj W :=
  let L : _root_.DerivedCategory.Plus _ := ⟨hW.choose, hW.choose_spec.1⟩
  let a := hW.choose_spec.2.some
  ((rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).mapIso a).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationOriginIso P.Coefficient c c').app L ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c').mapIso a

/-- The canonical compactification compositor alpha of thm-sf-comp-composition
(`originComposition`), written in the three retained compactification coordinates by the
canonical changes of compactification. It is not chosen from Nonempty.
Source: thm-sf-comp-composition, displayed isomorphism alpha
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
@[irreducible]
def alpha (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left))
    (M : D P X) (hM : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) X.obj.left M) :
    (image P d).obj ((image P e).obj M) ≅
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).obj M :=
  haveI := e.compactification.hasCompactification
  haveI := d.compactification.hasCompactification
  haveI := c.hasCompactification
  (image P d).mapIso
      (originChange P e.compactification
        (HasCompactification.compactification e.f.hom.left) M hM) ≪≫
    originChange P d.compactification
      (HasCompactification.compactification d.f.hom.left) _
      (DerivedCategory.plusEtaleOrigin.rightDerivedLowerShriek_obj e.f.hom.left hM) ≪≫
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Z.obj.left).ι.mapIso
      ((originComposition P.Coefficient e.f.hom.left d.f.hom.left).app ⟨M, hM⟩) ≪≫
    originChange P (HasCompactification.compactification (e.f.hom.left ≫ d.f.hom.left)) c M hM

/-- The component of the adjunction conjugate of alpha, by its representing Hom chain.
Source: def-weil-pbc-adjunction-conjugate, restricted comparison class
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def conjugate (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left)) (n : ℕ)
    (hn : topologicalKrullDim c.Z ≤ (n : WithBot ℕ∞))
    (B : D P Z) (hB : _root_.DerivedCategory.TStructure.t.plus B) :
    (G P (compositeEdge P e d c n hn)).obj B ⟶ (G P e).obj ((G P d).obj B) :=
  hom P e (exceptionalOriginProperty P (compositeEdge P e d c n hn) B hB)
    (exceptionalOriginProperty P d B hB).plus
    (hom P d (imageOrigin P e _
        (exceptionalOriginProperty P (compositeEdge P e d c n hn) B hB)) hB
      ((alpha P e d c _
        (exceptionalOriginProperty P (compositeEdge P e d c n hn) B hB)).hom ≫
          counit P (compositeEdge P e d c n hn) B hB))

/-- The inverse representing map, using alpha inverse and the pasted counits.
Source: sk-prop-cohsm, conjugacy on the comparison class
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def conjugateInv (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left)) (n : ℕ)
    (hn : topologicalKrullDim c.Z ≤ (n : WithBot ℕ∞))
    (B : D P Z) (hB : _root_.DerivedCategory.TStructure.t.plus B) :
    (G P e).obj ((G P d).obj B) ⟶ (G P (compositeEdge P e d c n hn)).obj B :=
  hom P (compositeEdge P e d c n hn)
    (exceptionalOriginProperty P e _ (exceptionalOriginProperty P d B hB).plus) hB
    ((alpha P e d c _
      (exceptionalOriginProperty P e _ (exceptionalOriginProperty P d B hB).plus)).inv ≫
        (image P d).map (counit P e _ (exceptionalOriginProperty P d B hB).plus) ≫
        counit P d B hB)

/-- The prescribed unit component q = c_A inverse after theta_{f,W_g}.
Source: sk-prop-cohsm, definition of q
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
def q (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left)) (n : ℕ)
    (hn : topologicalKrullDim c.Z ≤ (n : WithBot ℕ∞))
    (hWe : CTF P X (W P e)) (hWd : CTF P Y (W P d)) :
    (S P e).obj (W P d) ⊗ W P e ⟶ W P (compositeEdge P e d c n hn) :=
  theta P e hWe (W P d) hWd ≫ conjugateInv P e d c n hn _ (unitCTF P Z).plus

/-- Products of finite-Tor coefficients, including all reassociations in the calculation.
Source: sk-prop-cohsm, coefficient-associativity inputs
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: clause (ii) of lem-sf-tensor-ctf adds the Tor intervals, and clause (i)
retains bounded constructibility. -/
theorem coefficientProductCTF (T : SixFunctorSpace P.field) (B B' : D P T)
    (_hB : CTF P T B) (_hB' : CTF P T B') : CTF P T (B ⊗ B') := by
  exact tensorCTF P T B B' _hB _hB'

/-- Restricted projection naturality and the unit and associativity equations.
These are exactly the equations of def-sfb-projection-formula with its inverse
strong-monoidal structure maps; the module domain has no Tor restriction.
Source: sk-prop-cohsm, projection-coherence hypotheses
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
structure ProjectionCoherent (e : Edge P X Y) : Prop where
  natural_left (B B' : D P Y) (hB : CTF P Y B) (hB' : CTF P Y B')
      (M : D P X) (hM : BC P X M) (a : B ⟶ B') :
    (image P e).map ((S P e).map a ▷ M) ≫ pi P e B' M hB' hM =
      pi P e B M hB hM ≫ a ▷ (image P e).obj M
  natural_right (B : D P Y) (hB : CTF P Y B)
      (M M' : D P X) (hM : BC P X M) (hM' : BC P X M') (a : M ⟶ M') :
    (image P e).map ((S P e).obj B ◁ a) ≫ pi P e B M' hB hM' =
      pi P e B M hB hM ≫ B ◁ (image P e).map a
  unit (M : D P X) (hM : BC P X M) :
    pi P e (𝟙_ (D P Y)) M (unitCTF P Y) hM ≫ (λ_ ((image P e).obj M)).hom =
      (image P e).map
        ((leftDerivedUpperStarUnitIso
          (ModuleCat.{u + 1} P.Coefficient) e.f.hom.left).hom ▷ M ≫ (λ_ M).hom)
  assoc (B B' : D P Y) (hB : CTF P Y B) (hB' : CTF P Y B')
      (M : D P X) (hM : BC P X M) :
    pi P e (B ⊗ B') M (coefficientProductCTF P Y B B' hB hB') hM ≫
        (α_ B B' ((image P e).obj M)).hom =
      (image P e).map
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
          e.f.hom.left B B').hom ▷ M ≫
            (α_ ((S P e).obj B) ((S P e).obj B') M).hom) ≫
        pi P e B ((S P e).obj B' ⊗ M) hB (tensorInputBC P e B' M hB' hM) ≫
        B ◁ pi P e B' M hB' hM

/-- The smooth tensor hypothesis puts the exceptional image in Dctf.
Source: sk-prop-cohsm, first paragraph of the domain assertion
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: tensorInputCTF puts S_h B tensor W_h in Dctf. The assumed specified
isomorphism theta transports membership to G_h B, since Dctf is strictly full. -/
theorem smoothImageCTF (e : Edge P X Y) (hW : CTF P X (W P e))
    (_ht : ∀ (B : D P Y) (hB : CTF P Y B), IsIso (theta P e hW B hB))
    (B : D P Y) (_hB : CTF P Y B) : CTF P X ((G P e).obj B) := by
  let := _ht B _hB
  exact (CTF P X).prop_of_iso (asIso (theta P e hW B _hB))
    (tensorInputCTF P e B (W P e) _hB hW)

/-- The finite diagram's complete coefficient and module membership certificates.
Each finite-Tor certificate also supplies bounded constructibility and an etale origin.
Source: sk-prop-cohsm, all double-transpose input domains
(blueprint: lem-pur-compact-support-composite-transpose-domains). -/
structure CalculationDomains (e : Edge P X Y) (d : Edge P Y Z) (K : D P Z) : Prop where
  sgK : CTF P Y ((S P d).obj K)
  sgKWg : CTF P Y ((S P d).obj K ⊗ W P d)
  ggK : CTF P Y ((G P d).obj K)
  sfU : CTF P X ((S P e).obj ((S P d).obj K ⊗ W P d))
  sfT : CTF P X ((S P e).obj ((G P d).obj K))
  sfWg : CTF P X ((S P e).obj (W P d))
  n : CTF P X ((S P e).obj ((S P d).obj K ⊗ W P d) ⊗ W P e)
  sfTW : CTF P X ((S P e).obj ((G P d).obj K) ⊗ W P e)
  gfggK : CTF P X ((G P e).obj ((G P d).obj K))
  sfWgW : CTF P X ((S P e).obj (W P d) ⊗ W P e)
  gfWg : CTF P X ((G P e).obj (W P d))
  sfsgK : CTF P X ((S P e).obj ((S P d).obj K))
  sfsgKU : CTF P X ((S P e).obj ((S P d).obj K) ⊗ (G P e).obj (W P d))
  reassociated : CTF P X
    ((S P e).obj ((S P d).obj K) ⊗ ((S P e).obj (W P d) ⊗ W P e))

/-- Pullback membership for each finite-Tor coefficient in the calculation.
Source: sk-prop-cohsm, coefficient input domains
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: lem-sf-pullback-tor-amplitude preserves both bounded constructibility
and the given finite Tor interval, in the fixed-module presentation. -/
theorem pullCTF (e : Edge P X Y) (B : D P Y) (_hB : CTF P Y B) :
    CTF P X ((S P e).obj B) := by
  exact pullFiniteTor P e B _hB

attribute [local irreducible] hom counit originChange

private theorem transpose_left
    {E₀ E₁ C₀ C₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* C₀] [Category* C₁]
    (A : E₀ ⥤ C₀) (B : E₁ ⥤ C₁) (U : C₁ ⥤ E₁)
    (F : E₀ ⥤ E₁) (R : E₁ ⥤ E₀) (I : C₀ ⥤ C₁)
    (ad : F ⊣ R) (bd : B ⊣ U)
    {L L' : E₀} {M M' : C₀} {N : C₁}
    (a : A.obj L ≅ M) (a' : A.obj L' ≅ M')
    (v : B.obj (F.obj L) ⟶ I.obj (A.obj L))
    (v' : B.obj (F.obj L') ⟶ I.obj (A.obj L'))
    (s : M ⟶ M') (b : I.obj M' ⟶ N) (t : L ⟶ L')
    (ht : A.map t = a.hom ≫ s ≫ a'.inv)
    (hv : B.map (F.map t) ≫ v' = v ≫ I.map (A.map t)) :
    a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ I.map s ≫ b))) =
    s ≫ a'.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v' ≫ I.map a'.hom ≫ b))) := by
  have hm : A.map t ≫ a'.hom = a.hom ≫ s := by
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heq : v ≫ I.map a.hom ≫ I.map s ≫ b =
      B.map (F.map t) ≫ v' ≫ I.map a'.hom ≫ b := by
    rw [reassoc_of% hv, ← I.map_comp_assoc, ← I.map_comp_assoc, hm, I.map_comp,
      Category.assoc]
  rw [heq, bd.homEquiv_naturality_left, ad.homEquiv_naturality_left, A.map_comp]
  simp only [← Category.assoc]
  congr 1
  rw [ht]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem transpose_right
    {E₀ E₁ C₀ C₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* C₀] [Category* C₁]
    (A : E₀ ⥤ C₀) (B : E₁ ⥤ C₁) (U : C₁ ⥤ E₁)
    (F : E₀ ⥤ E₁) (R : E₁ ⥤ E₀) (I : C₀ ⥤ C₁)
    (ad : F ⊣ R) (bd : B ⊣ U)
    {L : E₀} {M : C₀} {N N' : C₁}
    (a : A.obj L ≅ M) (v : B.obj (F.obj L) ⟶ I.obj (A.obj L))
    (s : I.obj M ⟶ N) (b : N ⟶ N') :
    a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ s ≫ b))) =
    (a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ s)))) ≫ A.map (R.map (U.map b)) := by
  simp only [← Category.assoc]
  rw [bd.homEquiv_naturality_right ((v ≫ I.map a.hom) ≫ s) b,
    ad.homEquiv_naturality_right, A.map_comp]
  simp only [Category.assoc]

private theorem hom_value (e : Edge P X Y) (M : D P X)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
    (B : D P Y) (hB : _root_.DerivedCategory.TStructure.t.plus B)
    (a : (image P e).obj M ⟶ B) :
    letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
      P.Coefficient e.compactification
    let L := hM.choose
    let v := hM.choose_spec.2.some
    hom P e hM hB a = v.inv ≫
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X.obj.left).mapDerivedCategory.map
        ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) e.compactification)).homEquiv L _
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient)
            Y.obj.left).homEquiv _ B
            ((fixedCompactSupportComparisonIso P.Coefficient e.compactification).inv.app
              ⟨L, hM.choose_spec.1⟩ ≫ (image P e).map v.hom ≫ a))) := by
  dsimp only
  unfold hom
  dsimp only [specifiedExceptionalHomEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply, Iso.homFromEquiv, Equiv.coe_fn_mk,
    Functor.mapIso, Iso.symm]
  rfl

private theorem hom_left (e : Edge P X Y) (M M' : D P X)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
    (hM' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X.obj.left M')
    (B : D P Y) (hB : _root_.DerivedCategory.TStructure.t.plus B)
    (a : M ⟶ M') (b : (image P e).obj M' ⟶ B) :
    hom P e hM hB ((image P e).map a ≫ b) = a ≫ hom P e hM' hB b := by
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient e.compactification
  let A := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X.obj.left).mapDerivedCategory
  let B' := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y.obj.left).mapDerivedCategory
  let L := hM.choose
  let L' := hM'.choose
  let v := hM.choose_spec.2.some
  let v' := hM'.choose_spec.2.some
  obtain ⟨t, ht⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
    L L' hM'.choose_spec.1).surjective (v.hom ≫ a ≫ v'.inv)
  have hv := (fixedCompactSupportComparisonIso P.Coefficient e.compactification).inv.naturality
    (ObjectProperty.homMk t : ⟨L, hM.choose_spec.1⟩ ⟶ ⟨L', hM'.choose_spec.1⟩)
  rw [hom_value, hom_value]
  exact transpose_left A B' _ _ _ (image P e)
    (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) e.compactification))
    (derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y.obj.left)
    v v' _ _ a b t ht hv

private theorem hom_right (e : Edge P X Y) (M : D P X)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
    (B B' : D P Y) (hB : _root_.DerivedCategory.TStructure.t.plus B)
    (hB' : _root_.DerivedCategory.TStructure.t.plus B')
    (a : (image P e).obj M ⟶ B) (b : B ⟶ B') :
    hom P e hM hB' (a ≫ b) = hom P e hM hB a ≫ (G P e).map b := by
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient e.compactification
  rw [hom_value, hom_value]
  exact transpose_right _ _ _ _ _ (image P e)
    (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) e.compactification))
    (derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y.obj.left) _ _ a b

/-- Naturality and the counit normalization of the actual Hom-chain bijections.
Source: thm-sf-ambient-adjoint-class, normalized comparison-class adjunction
(blueprint: lem-pur-compact-support-composite-transpose-domains).
Proof: each factor in specifiedExceptionalHomEquiv is natural. Changes of origin
conjugate both sides by the same isomorphism, which cancels. Inverse-transposing
an arrow into G_h B is P_h of that arrow followed by the inverse transpose of
the identity; the latter is counit by definition. These identities give the
left and right naturality equations without an ambient pro-etale adjunction. -/
theorem hom_natural (e : Edge P X Y) :
    (∀ (M M' : D P X)
      (hM : DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
      (hM' : DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) X.obj.left M')
      (B : D P Y) (hB : _root_.DerivedCategory.TStructure.t.plus B)
      (a : M ⟶ M') (b : (image P e).obj M' ⟶ B),
      hom P e hM hB ((image P e).map a ≫ b) = a ≫ hom P e hM' hB b) ∧
    (∀ (M : D P X)
      (hM : DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
      (B B' : D P Y) (hB : _root_.DerivedCategory.TStructure.t.plus B)
      (hB' : _root_.DerivedCategory.TStructure.t.plus B')
      (a : (image P e).obj M ⟶ B) (b : B ⟶ B'),
      hom P e hM hB' (a ≫ b) = hom P e hM hB a ≫ (G P e).map b) ∧
    (∀ (M : D P X)
      (hM : DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) X.obj.left M)
      (B : D P Y) (hB : _root_.DerivedCategory.TStructure.t.plus B)
      (a : M ⟶ (G P e).obj B),
      (hom P e hM hB).symm a = (image P e).map a ≫ counit P e B hB) := by
  refine ⟨hom_left P e, hom_right P e, ?_⟩
  intro M hM B hB a
  apply (hom P e hM hB).injective
  rw [Equiv.apply_symm_apply,
    hom_left P e M _ hM (exceptionalOriginProperty P e B hB)]
  simp only [counit, Equiv.apply_symm_apply, Category.comp_id]

/-- The whole domain assertion and normalized composition and projection data.
Source: main-20261015, sk-prop-cohsm, second paragraph, composition comparison
(blueprint: lem-pur-compact-support-composite-transpose-domains).

Proof, following the accepted six-step split:
1. Apply lem-sf-pullback-tor-amplitude and both clauses of lem-sf-tensor-ctf to
K,W_g,W_f successively. Use theta_g to put G_g K in Dctf before applying theta_f.
The unit has interval [0,0]. Arbitrary bounded constructible module inputs need
no Tor interval; tensor them only with the finite-Tor coefficients obtained here.
2. Lem-sf-proetale-constructible-origin supplies bounded constructible etale
antecedents. Fixed-scalar compact-support finiteness preserves them, also for
P_f M followed by P_g and for every tensor module input. This gives all D+
comparison-class domains; no Tor claim about compact-support images is used.
3. Apply the normalized Hom bijections of thm-sf-ambient-adjoint-class for f
then g. Naturality gives the pasted counit. Transport the specified alpha and
form its adjunction conjugate. Transposing the identity in either representing
object gives conjugate and conjugateInv; naturality and injectivity show they
are inverse. At the unit, theta_f,W_g is an isomorphism, so q is an isomorphism.
4. Reflect Tor intervals to the etale representatives. The finite compact
projection formula makes every specified projection invertible. Finite-site
counit/projection transport fixes the actual transformations, including all
naturality instances; inverse and symmetry give pi with the stated ordering.
5. Ringed-derived monoidal comparisons, the proper adjoint-left-action lemma,
open tensor normalization and open-left-action lemma give both forward action
laws. The composite-left-action lemma gives them for the specified proper/open
projection. Invert the unit and associativity equations to get ProjectionCoherent.
6. Apply ordinary-etale compact projection coherence in a compatible tower.
The choice-independence of lem-amb-etale-compact-comparisons identifies its graph
comparison with the inverse specified etale compositor. Compact-support site
coherence and finite-site transport then give the displayed composite equation
with the canonical pullback compositor. All its module and coefficient domains
are those verified in steps 1 and 2. These are precisely the hypotheses needed
by the restricted-domain double-transpose calculation. -/
theorem compactSupportCompositeTransposeDomains
    (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left)) (n : ℕ)
    (hn : topologicalKrullDim c.Z ≤ (n : WithBot ℕ∞))
    (hWe : CTF P X (W P e)) (hWd : CTF P Y (W P d))
    (hte : ∀ (B : D P Y) (hB : CTF P Y B), IsIso (theta P e hWe B hB))
    (htd : ∀ (B : D P Z) (hB : CTF P Z B), IsIso (theta P d hWd B hB)) :
    (∀ (K : D P Z), CTF P Z K → CalculationDomains P e d K) ∧
    ProjectionCoherent P e ∧ ProjectionCoherent P d ∧
    ProjectionCoherent P (compositeEdge P e d c n hn) ∧
    (∀ (B : D P Z) (hB : _root_.DerivedCategory.TStructure.t.plus B),
      conjugate P e d c n hn B hB ≫ conjugateInv P e d c n hn B hB = 𝟙 _ ∧
      conjugateInv P e d c n hn B hB ≫ conjugate P e d c n hn B hB = 𝟙 _ ∧
      (image P d).map ((image P e).map (conjugate P e d c n hn B hB)) ≫
        (image P d).map (counit P e _ (exceptionalOriginProperty P d B hB).plus) ≫
        counit P d B hB =
      (alpha P e d c _
        (exceptionalOriginProperty P (compositeEdge P e d c n hn) B hB)).hom ≫
        counit P (compositeEdge P e d c n hn) B hB) ∧
    (∀ (B B' : D P Z) (hB : _root_.DerivedCategory.TStructure.t.plus B)
      (hB' : _root_.DerivedCategory.TStructure.t.plus B') (a : B ⟶ B'),
      (G P (compositeEdge P e d c n hn)).map a ≫ conjugate P e d c n hn B' hB' =
        conjugate P e d c n hn B hB ≫ (G P e).map ((G P d).map a)) ∧
    IsIso (q P e d c n hn hWe hWd) ∧
    CTF P X (W P (compositeEdge P e d c n hn)) ∧
    (∀ (K : D P Z) (hK : CTF P Z K) (M : D P X) (hM : BC P X M),
      (alpha P e d c ((S P e).obj ((S P d).obj K) ⊗ M)
        (tensorInputBC P e ((S P d).obj K) M
          (pullCTF P d K hK) hM).plusEtaleOrigin).hom ≫
        (image P (compositeEdge P e d c n hn)).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            e.f.hom.left d.f.hom.left).inv.app K ▷ M) ≫
        pi P (compositeEdge P e d c n hn) K M hK hM =
      (image P d).map
        (pi P e ((S P d).obj K) M
          (pullCTF P d K hK) hM) ≫
        pi P d K ((image P e).obj M) hK (imageBC P e M hM) ≫
        K ◁ (alpha P e d c M hM.plusEtaleOrigin).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CompactSupportTranspose
