/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Affine.AffineVectorTraceAction

import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceUnitCompactBaseChange
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTowerCounitBaseChange
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.AlgebraicGeometry.SfP1ConstantUnitPullback
import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
import WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.FiniteP1KummerNaturality
import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import WeilConjectures.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorization
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import Mathlib.Tactic.SuppressCompilation
import WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.EtaleSecondCoordinateContraction
import WeilConjectures.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange
import WeilConjectures.AlgebraicGeometry.Sf.SfSupportedDiagonalDataSupplement
import WeilConjectures.AlgebraicGeometry.SfSupportedTraceContractions
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence
import WeilConjectures.AlgebraicGeometry.SfSupportedFirstExtraction
import WeilConjectures.AlgebraicGeometry.ProperRelativeKunnethSupports
import WeilConjectures.AlgebraicGeometry.ProperKunnethNormalizationAlgebra
import Mathlib.CategoryTheory.Functor.Category
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupports
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.AlgebraicGeometry.SfSupportedSecondExtraction
import WeilConjectures.AlgebraicGeometry.SfSupportedCoefficientBraid
import WeilConjectures.AlgebraicGeometry.SfSupportedCoordinateTensor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
import WeilConjectures.AlgebraicGeometry.SfDiagonalInsertionProjection
import WeilConjectures.AlgebraicGeometry.SfProperSectionProjection
import WeilConjectures.AlgebraicGeometry.SfProperProjectionComposition
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
import WeilConjectures.AlgebraicGeometry.SfIdentityProjectionNormalization
import WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord
import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
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
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import WeilConjectures.CategoryTheory.CoproductsOfCopowers
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.SfDiagonalPushComparison
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.OrdinaryProperForgetComparison
import WeilConjectures.AlgebraicGeometry.SfP1SupportedExtMapData
import WeilConjectures.AlgebraicGeometry.SfP1ConstantUnitHom
import WeilConjectures.AlgebraicGeometry.SfP1UnitPullbackNativeHom
import WeilConjectures.AlgebraicGeometry.SfP1FiniteConstantComparisonHom
import WeilConjectures.AlgebraicGeometry.SfP1NativeConstantHom
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition

/-! # The standard global frame of the free bundle -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Modules
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.vectorBundleIntegration Etale.rightDerivedLowerShriek
  Etale.affineLinearBaseCoefficient Etale.upperStar Functor.leftDerivedFunctor
  Etale.leftDerivedUpperStarComp DerivedCategory.singleFunctors

/-- The standard inverse frame, transported from the top open back to its base.
This construction involves no trace or purity isomorphism. -/
def affineVectorStandardChart (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) :
    affineTraceTower B d ⟶
      VectorBundleZeroSection.scheme B d
        (SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))) :=
  affineTraceMap B.topIso.inv d ≫
    Etale.vectorIntegrationChart B d
      (SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))) ⊤
      (Scheme.Modules.restrictFreeIso (⊤ : B.Opens).ι (ULift.{u} (Fin d)))

/-- The standard inverse frame is over the identity of the base. -/
theorem affineVectorStandardChart_over (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) :
    affineVectorStandardChart B d ≫
      VectorBundleZeroSection.π B d
        (SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))) =
    affineTraceProjection B d := by
  have hc := (Etale.vectorIntegrationChart_isPullback B d
    (SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))) ⊤
    (Scheme.Modules.restrictFreeIso (⊤ : B.Opens).ι (ULift.{u} (Fin d)))).w
  have hm := (affineTraceMap_isPullback B.topIso.inv d).w
  dsimp only [affineVectorStandardChart]
  rw [Category.assoc, hc, ← Category.assoc, hm, Category.assoc]
  change affineTraceProjection B d ≫ B.topIso.inv ≫ B.topIso.hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- The standard global inverse frame is an isomorphism. -/
instance affineVectorStandardChart_isIso (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) :
    IsIso (affineVectorStandardChart B d) := by
  let : IsIso (⊤ : B.Opens).ι := B.topIso.isIso_hom
  let := (affineTraceMap_isPullback B.topIso.inv d).isIso_fst_of_isIso
  let := (Etale.vectorIntegrationChart_isPullback B d
    (SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))) ⊤
      (Scheme.Modules.restrictFreeIso (⊤ : B.Opens).ι (ULift.{u} (Fin d)))).isIso_fst_of_isIso
  dsimp only [affineVectorStandardChart]
  infer_instance

/-- Cartesian square of the standard inverse frame. -/
theorem affineVectorStandardChart_square (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) :
    IsPullback (affineVectorStandardChart B d) (affineTraceProjection B d)
      (VectorBundleZeroSection.π B d
        (SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d)))) (𝟙 B) :=
  IsPullback.of_horiz_isIso
    ⟨(affineVectorStandardChart_over B d).trans (Category.comp_id _).symm⟩

open Etale

attribute [local implicit_reducible] vectorIntegrationSource vectorIntegrationCoefficient

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

attribute [local irreducible] affineLinearCoefficientDescent affineLinearCompactComparison
  derivedSquareUpperStarIso
  affineTraceRightBaseChange affineTraceExchange affineTraceCounit
  vectorIntegrationBaseCoefficientPullback vectorIntegrationChart

private theorem coefficient_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' S S' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S')
    (v : X' ⟶ X) (g : S' ⟶ S) (sq : CommSq v p' p g)
    (hS : IsUnit (N : Γ(S, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A v).map
        (vectorIntegrationBaseCoefficientPullback A N hA t p hS d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app
        (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A p').map
        (vectorIntegrationBaseCoefficientPullback A N hA t g hS d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t p' hS' d).hom := by
  have h₁ := orderedTateCoefficientComposition A N hA t v p (v ≫ p) rfl hS hX d
  have h₂ := orderedTateCoefficientComposition A N hA t p' g (v ≫ p) sq.w hS hS' d
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app
    (affineLinearBaseCoefficient A N hA S d))).mp
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  exact h₁.trans h₂.symm

private def coefficientExchange
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' S S' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S')
    [HasCompactification p] [HasCompactification p'] [QuasiCompact p']
    (v : X' ⟶ X) (g : S' ⟶ S) (sq : IsPullback v p' p g)
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :=
  (rightDerivedLowerShriekBaseChangeMap A sq).app
      (affineLinearBaseCoefficient A N hA X d) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p').map
      (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom

private theorem exchange_paste_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {p'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (sq₁ : IsPullback v' p' p v) (sq₂ : IsPullback w' p'' p' w)
    (z : X'' ⟶ X) (c : Y'' ⟶ Y) (hz : z = w' ≫ v') (hc : c = w ≫ v)
    (sq : IsPullback z p'' p c) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v c hc).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hc
  exact affineLinearExchange_paste A sq₁ sq₂ K

private theorem coefficientExchange_comp
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' X'' S S' S'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian S] [IsNoetherian S'] [IsNoetherian S'']
    (p : X ⟶ S) (p' : X' ⟶ S') (p'' : X'' ⟶ S'')
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (v : X' ⟶ X) (w : X'' ⟶ X') (g : S' ⟶ S) (f : S'' ⟶ S')
    (z : X'' ⟶ X) (c : S'' ⟶ S) (hz : z = w ≫ v) (hc : c = f ≫ g)
    (sq₁ : IsPullback v p' p g) (sq₂ : IsPullback w p'' p' f)
    (sq : IsPullback z p'' p c)
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤))) (d : ℕ) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g c hc).hom.app _ ≫
      (ordinaryFinitePullback A f).map
        (coefficientExchange A N hA t p p' v g sq₁ hX d) ≫
      coefficientExchange A N hA t p' p'' w f sq₂ hX' d =
    coefficientExchange A N hA t p p'' z c sq hX d := by
  have hp := exchange_paste_named A sq₁ sq₂ z c hz hc
    (sq := sq) (affineLinearBaseCoefficient A N hA X d)
  have hn := (rightDerivedLowerShriekBaseChangeMap A sq₂).naturality
    (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom
  have ht := orderedTateCoefficientComposition A N hA t w v z hz hX hX' d
  dsimp only [Functor.comp_map] at hn
  unfold coefficientExchange
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [ordinaryFinitePullback] at hp hn ht ⊢
  rw [reassoc_of% hn, reassoc_of% hp]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, ht]

private def compactTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
      ((affineLinearCoefficientDescent A N hA t S hS d) ≪≫
        vectorIntegrationBaseCoefficientPullback A N hA t (affineTraceProjection S d)
          hS d).inv ≫
    (affineLinearCompactComparison N hN A hA S hS d).inv ≫
    affineTraceCounit A N hA t D S hS d

private theorem tower_coefficient_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hT : IsUnit (N : Γ(T, ⊤)))
    (d : ℕ) (hX : IsUnit (N : Γ(affineTraceTower S d, ⊤))) :
    let aS := affineLinearCoefficientDescent A N hA t S hS d ≪≫
      vectorIntegrationBaseCoefficientPullback A N hA t (affineTraceProjection S d) hS d
    let aT := affineLinearCoefficientDescent A N hA t T hT d ≪≫
      vectorIntegrationBaseCoefficientPullback A N hA t (affineTraceProjection T d) hT d
    let b := affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
      (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f)
    (ordinaryFinitePullback A (affineTraceMap f d)).map aS.inv ≫ b.hom =
      (vectorIntegrationBaseCoefficientPullback A N hA t (affineTraceMap f d) hX d).hom ≫
        aT.inv := by
  dsimp only
  have hb := congrArg Iso.hom
    (affineTraceRightBaseChange_unit_coefficient A N hA t f hS hT d)
  have hc := coefficient_square A N hA t (affineTraceProjection S d)
    (affineTraceProjection T d) (affineTraceMap f d) f
    (affineTraceMap_isPullback f d).toCommSq hS hX hT d
  apply (cancel_mono ((affineLinearCoefficientDescent A N hA t T hT d ≪≫
    vectorIntegrationBaseCoefficientPullback A N hA t
      (affineTraceProjection T d) hT d).hom)).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hb]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.app_hom]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [← hc]
  simp only [← Functor.map_comp_assoc, Category.comp_id, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem compactTrace_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (hX : IsUnit (N : Γ(affineTraceTower S d, ⊤))) :
    coefficientExchange A N hA t (affineTraceProjection S d) (affineTraceProjection T d)
        (affineTraceMap f d) f (affineTraceMap_isPullback f d) hX d ≫
      compactTrace N hN A hA t D T hT d =
    (ordinaryFinitePullback A f).map (compactTrace N hN A hA t D S hS d) ≫
      (ordinaryFiniteUnitPullback A f).hom := by
  let aS := affineLinearCoefficientDescent A N hA t S hS d ≪≫
    vectorIntegrationBaseCoefficientPullback A N hA t (affineTraceProjection S d) hS d
  let aT := affineLinearCoefficientDescent A N hA t T hT d ≪≫
    vectorIntegrationBaseCoefficientPullback A N hA t (affineTraceProjection T d) hT d
  let b := affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
    (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f)
  have hc := tower_coefficient_square A N hA t f hS hT d hX
  have hn := (rightDerivedLowerShriekBaseChangeMap A
    (affineTraceMap_isPullback f d)).naturality aS.inv
  have hk := affineTraceUnitCompactComparison_baseChange N hN A hA t
    (T := T) (S := S) f hS d
  have hd : OrdinaryFiniteP1BaseChange A N hA t D :=
    ordinaryFiniteP1BaseChange_of_normalization N hN A hA t D
  have ht := affineTraceTowerCounit_baseChange A N hN hA t D hd f hS d
    (ordinaryFiniteUnit A S)
  have hu := (affineTraceAdjunction A N hA t D T
    (affineTracePullbackInvertible N f hS) d).counit.naturality
      (ordinaryFiniteUnitPullback A f).hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn hu
  have ht' : affineTraceExchange A f d
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
        (affineTraceLeft A T d).map b.hom ≫
        affineTraceCounit A N hA t D T hT d =
      (ordinaryFinitePullback A f).map (affineTraceCounit A N hA t D S hS d) ≫
        (ordinaryFiniteUnitPullback A f).hom := by
    simp only [b, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    unfold affineTraceCounit
    rw [hu]
    exact (reassoc_of% ht) _
  unfold coefficientExchange compactTrace
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hc]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [aS, b, ordinaryFinitePullback] at hn hk ht' ⊢
  rw [← reassoc_of% hn, ← reassoc_of% hk, ht']

private lemma named_compositor
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (v : Y ⟶ Z) (k : X ⟶ Z) (e : k = r ≫ v) :
    eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

private theorem inverse_square_comparison
    (A : Type (u + 1)) [CommRing A] {X X' Y Y' : Scheme.{u}}
    (q : X' ⟶ X) (r : X' ⟶ Y') (p : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : CommSq q r p v) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm ≪≫
      eqToIso (congrArg (ordinaryFinitePullback A) sq.w) ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  have hn : eqToIso (congrArg (ordinaryFinitePullback A) sq.w) ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v (q ≫ p) sq.w := by
    exact named_compositor A r v (q ≫ p) sq.w
  simp only [derivedSquareUpperStarIso, Iso.trans_symm, Iso.symm_symm_eq]
  rw [hn]

private theorem descended_coefficient_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' S S' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S')
    (v : X' ⟶ X) (g : S' ⟶ S) (sq : CommSq v p' p g)
    (hS : IsUnit (N : Γ(S, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ)
    (R : DerivedCategoryModule A X')
    (a : R ≅ (ordinaryFinitePullback A p').obj (affineLinearBaseCoefficient A N hA S' d)) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app
        (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A p').map
        (vectorIntegrationBaseCoefficientPullback A N hA t g hS d).hom ≫ a.inv =
    (ordinaryFinitePullback A v).map
        (vectorIntegrationBaseCoefficientPullback A N hA t p hS d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom ≫
      (a ≪≫ vectorIntegrationBaseCoefficientPullback A N hA t p' hS' d).inv := by
  rw [reassoc_of% (coefficient_square A N hA t p p' v g sq hS hX hS' d)]
  simp only [Iso.trans_inv, Iso.hom_inv_id_assoc]

private theorem iso_tail {C : Type*} [Category C]
    {W X Y Z U V : C} (e₁ : W ≅ X) (e₂ : X ≅ Y) (e₃ : Y ≅ Z)
    (c : W ≅ Z) (r : Z ≅ U) (a : V ≅ U) (h : e₁ ≪≫ e₂ ≪≫ e₃ = c) :
    (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ r ≪≫ a.symm).hom = c.hom ≫ r.hom ≫ a.inv := by
  have hh := congrArg (fun e : W ≅ Z ↦ e.hom ≫ r.hom ≫ a.inv) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hh

-- Perform component conversions with abstract functors; specializing them first
-- forces the kernel to unfold the large derived inverse-image constructions.
private theorem nat_iso_tail {C D : Type*} [Category C] [Category D]
    {F G H J : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (γ : H ≅ J) (δ : J ≅ F)
    (h : α ≪≫ β ≪≫ γ = δ.symm) (K : C)
    {U V : D} (r : J.obj K ≅ U) (a : V ≅ U) :
    (α.app K ≪≫ β.app K ≪≫ γ.app K ≪≫ r ≪≫ a.symm).hom =
      δ.inv.app K ≫ r.hom ≫ a.inv := by
  have hs := congrArg (fun z ↦ z.app K) h
  simp only [NatIso.trans_app] at hs
  simpa only [Iso.app_hom, Iso.symm_hom] using
    iso_tail (α.app K) (β.app K) (γ.app K) (δ.symm.app K) r a hs

private theorem expanded_coefficient_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' S S' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S')
    (v : X' ⟶ X) (g : S' ⟶ S) (sq : CommSq v p' p g)
    (hS : IsUnit (N : Γ(S, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ)
    (R : DerivedCategoryModule A X')
    (a : R ≅ (ordinaryFinitePullback A p').obj (affineLinearBaseCoefficient A N hA S' d)) :
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).symm.app
        (affineLinearBaseCoefficient A N hA S d) ≪≫
      (eqToIso (congrArg (ordinaryFinitePullback A) sq.w)).app
        (affineLinearBaseCoefficient A N hA S d) ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' g).app
        (affineLinearBaseCoefficient A N hA S d) ≪≫
      (ordinaryFinitePullback A p').mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t g hS d) ≪≫ a.symm).hom =
      (ordinaryFinitePullback A v).map
          (vectorIntegrationBaseCoefficientPullback A N hA t p hS d).hom ≫
        (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom ≫
        (a ≪≫ vectorIntegrationBaseCoefficientPullback A N hA t p' hS' d).inv := by
  have hh := nat_iso_tail
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).symm
    (eqToIso (congrArg (ordinaryFinitePullback A) sq.w))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' g)
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq)
    (inverse_square_comparison A v p' p g sq)
    (affineLinearBaseCoefficient A N hA S d)
    ((ordinaryFinitePullback A p').mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA t g hS d)) a
  exact hh.trans (descended_coefficient_square A N hA t p p' v g sq hS hX hS' d R a)

private theorem chart_coefficient
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (hE : IsUnit (N : Γ(VectorBundleZeroSection.scheme S d F, ⊤))) :
    (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom =
      (ordinaryFinitePullback A (vectorIntegrationChart S d F V e)).map
          (vectorIntegrationBaseCoefficientPullback A N hA t
            (VectorBundleZeroSection.π S d F) hS d).hom ≫
        (vectorIntegrationBaseCoefficientPullback A N hA t
          (vectorIntegrationChart S d F V e) hE d).hom ≫
        ((affineLinearCoefficientDescent A N hA t V.toScheme
            (affineTracePullbackInvertible N V.ι hS) d) ≪≫
          vectorIntegrationBaseCoefficientPullback A N hA t
            (affineTraceProjection V.toScheme d)
            (affineTracePullbackInvertible N V.ι hS) d).inv := by
  exact expanded_coefficient_square A N hA t (VectorBundleZeroSection.π S d F)
    (affineTraceProjection V.toScheme d) (vectorIntegrationChart S d F V e) V.ι
    (vectorIntegrationChart_isPullback S d F V e).toCommSq hS hE
    (affineTracePullbackInvertible N V.ι hS) d _
    (affineLinearCoefficientDescent A N hA t V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d)

private theorem frame_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    [IsAffineHom (VectorBundleZeroSection.π S d F)]
    [LocallyOfFiniteType (VectorBundleZeroSection.π S d F)]
    (V : S.Opens) [IsNoetherian V.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d F V)
    (hE : IsUnit (N : Γ(VectorBundleZeroSection.scheme S d F, ⊤))) :
    coefficientExchange A N hA t (VectorBundleZeroSection.π S d F)
        (affineTraceProjection V.toScheme d)
        (vectorIntegrationChart S d F V e) V.ι
        (vectorIntegrationChart_isPullback S d F V e) hE d ≫
      compactTrace N hN A hA t D V.toScheme (affineTracePullbackInvertible N V.ι hS) d =
    (ordinaryFinitePullback A V.ι).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
            (VectorBundleZeroSection.π S d F)).map
          (vectorIntegrationBaseCoefficientPullback A N hA t
            (VectorBundleZeroSection.π S d F) hS d).inv ≫
          vectorBundleIntegration N hN A hA S hS d F) ≫
      (ordinaryFiniteUnitPullback A V.ι).hom := by
  let := (vectorIntegration_geometry S d F).1
  let := (vectorIntegration_geometry S d F).2.1
  have hnorm : VectorIntegrationNormalization N hN A hA S hS d F
      (vectorBundleIntegration N hN A hA S hS d F) := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact (existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose_spec.2
  have hn := hnorm t D V e
  have he := (rightDerivedLowerShriekBaseChangeMap A
    (vectorIntegrationChart_isPullback S d F V e)).naturality
      (vectorIntegrationBaseCoefficientPullback A N hA t
        (VectorBundleZeroSection.π S d F) hS d).inv
  dsimp only [Functor.comp_map] at he
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  unfold vectorIntegrationLocalTrace
  rw [chart_coefficient A N hA t S hS d F V e hE]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [ordinaryFinitePullback, vectorIntegrationCoefficient] at he ⊢
  rw [reassoc_of% he]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [coefficientExchange, compactTrace, Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc]

private theorem finish_trace {C : Type*} [Category C] (F : C ⥤ C)
    {X Y Z T U : C} (i : Z ⟶ F.obj X) (E : F.obj X ⟶ T) (τ : T ⟶ Y)
    (τ₀ : X ⟶ Y) (b : F.obj Y ⟶ Y) (u : Y ⟶ U) (m : F.obj U ⟶ U)
    (htrace : E ≫ τ = F.map τ₀ ≫ b) (hu : b ≫ u = F.map u ≫ m) :
    (i ≫ E) ≫ τ ≫ u = i ≫ F.map (τ₀ ≫ u) ≫ m := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% htrace, hu]

-- Match the factors in the public trace formula before specializing the category.
private theorem finish_trace_expanded {C : Type*} [Category C] (F : C ⥤ C)
    {X X₁ Y Z T₀ T₁ T₂ T₃ U : C} (i : Z ⟶ F.obj X)
    (e : F.obj X ⟶ T₀) (v : T₀ ⟶ T₁)
    (a : T₁ ⟶ T₂) (b : T₂ ⟶ T₃) (c : T₃ ⟶ Y)
    (r : X ⟶ X₁) (s : X₁ ⟶ Y) (j : F.obj Y ⟶ Y)
    (u : Y ⟶ U) (m : F.obj U ⟶ U)
    (htrace : (e ≫ v) ≫ (a ≫ b ≫ c) = F.map (r ≫ s) ≫ j)
    (hu : j ≫ u = F.map u ≫ m) :
    (i ≫ e ≫ v) ≫ (a ≫ b ≫ c ≫ u) = i ≫ F.map (r ≫ s ≫ u) ≫ m := by
  simpa only [Category.assoc] using
    finish_trace F i (e ≫ v) (a ≫ b ≫ c) (r ≫ s) j u m htrace hu

/-- Evaluation of vector integration at the one fixed standard global free frame.
There is no arbitrary vector bundle or arbitrary affine presentation in this statement.
Source: def-amb-vector-integration, normalization on a frame and restriction from the top open.
(blueprint: lem-pur-affine-vector-standard-frame).

Proof: evaluate the normalization in existsUnique_vectorIntegrationGluing at the
standard free frame on the top open, for the given t,D. The commutative-square
composition law for the ordered Tate coefficient identifies the chart coefficient.
Compact-support exchange naturality then gives the normalized trace on that chart.
Transport this equality along B.topIso.inv using compact comparison base change and
the affine-tower counit base-change equation. Paste the chart square with this tower
square; exchange pasting and ordered Tate composition identify their composite with
affineVectorStandardChart. The constant-unit composition law cancels the two top-open
pullbacks, and the constant-to-monoidal-unit comparison gives the stated target.
In rank zero, on the empty base, and for zero coefficients the same equations apply. -/
theorem affineVectorStandardFrame (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    let F := SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    let q := affineTraceProjection B d
    let π := VectorBundleZeroSection.π B d F
    letI := (NagataCompactification q).hasCompactification
    letI := (NagataCompactification π).hasCompactification
    let c (T S : Scheme.{u}) (f : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) :=
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t f (P.diagonalExponent_isUnit aS) d
    let L := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) q
    let L₀ := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π
    let τ := L.map
        ((Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t B (P.diagonalExponent_isUnit aB) d) ≪≫
          c _ _ q aB).inv ≫
      (Etale.affineLinearCompactComparison P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d).inv ≫
      Etale.affineTraceCounit P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t D B (P.diagonalExponent_isUnit aB) d ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
    let τ₀ := L₀.map (c _ _ π aB).inv ≫
      Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
    Etale.affineVectorTraceAction P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t π q (affineVectorStandardChart B d)
        (affineVectorStandardChart_square B d) (P.diagonalExponent_isUnit (π ≫ aB)) d ≫ τ =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫
        (Etale.ordinaryFinitePullback P.Coefficient (𝟙 B)).map τ₀ ≫
        (Etale.leftDerivedUpperStarUnitIso
          (ModuleCat.{u + 1} P.Coefficient) (𝟙 B)).hom := by
  let A := P.Coefficient
  let N := P.diagonalExponent
  let hN : 0 < N := pow_pos P.coefficients.prime.out.pos P.level
  let hA := P.diagonalExponent_annihilates
  let hB := P.diagonalExponent_isUnit aB
  let F := SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))
  let π := VectorBundleZeroSection.π B d F
  let := (vectorIntegration_geometry B d F).1
  let := (vectorIntegration_geometry B d F).2.1
  let := (vectorIntegration_geometry B d F).2.2
  let V : B.Opens := ⊤
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let g := V.ι
  let f := B.topIso.inv
  let q := affineTraceProjection B d
  let qV := affineTraceProjection V.toScheme d
  let e := Scheme.Modules.restrictFreeIso V.ι (ULift.{u} (Fin d))
  let v := vectorIntegrationChart B d F V e
  let w := affineTraceMap f d
  let k := affineVectorStandardChart B d
  let hE := affineTracePullbackInvertible N π hB
  let hV := affineTracePullbackInvertible N g hB
  let hXV := affineTracePullbackInvertible N qV hV
  let := affineTraceNoetherian B d
  let := affineTraceNoetherian V.toScheme d
  let L := rightDerivedLowerShriek (ModuleCat.{u + 1} A) π
  let τ₀ := L.map (vectorIntegrationBaseCoefficientPullback A N hA t π hB d).inv ≫
    vectorBundleIntegration N hN A hA B hB d F
  have hi : (𝟙 B) = f ≫ g := B.topIso.inv_hom_id.symm
  have hn := frame_normalization N hN A hA t D B hB d F V e hE
  have ht := compactTrace_baseChange N hN A hA t D f hV hB d hXV
  have hp := coefficientExchange_comp A N hA t π qV q v w g f k (𝟙 B) rfl hi
    (vectorIntegrationChart_isPullback B d F V e) (affineTraceMap_isPullback f d)
    (affineVectorStandardChart_square B d) hE hXV d
  have htrace : coefficientExchange A N hA t π q k (𝟙 B)
        (affineVectorStandardChart_square B d) hE d ≫
      compactTrace N hN A hA t D B hB d =
    (ordinaryFinitePullback A (𝟙 B)).map τ₀ ≫
      (ordinaryFiniteUnitPullback A (𝟙 B)).hom := by
    rw [← hp]
    simp only [Category.assoc]
    rw [ht, ← Functor.map_comp_assoc, hn]
    rw [(ordinaryFinitePullback A f).map_comp]
    simp only [Category.assoc]
    have hc := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g (𝟙 B) hi).hom.naturality
      τ₀
    dsimp only [Functor.comp_map] at hc
    change (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g (𝟙 B) hi).hom.app _ ≫
        (ordinaryFinitePullback A f).map ((ordinaryFinitePullback A g).map τ₀) ≫
        (ordinaryFinitePullback A f).map (ordinaryFiniteUnitPullback A g).hom ≫
        (ordinaryFiniteUnitPullback A f).hom = _
    dsimp only [ordinaryFinitePullback] at hc ⊢
    rw [← reassoc_of% hc]
    have hu := ordinaryFiniteUnitPullback_comp A f g (𝟙 B) hi
    dsimp only [ordinaryFinitePullback] at hu
    rw [hu]
  have hu := SfP1Transport.constantUnit_pullback A (𝟙 B)
  simp only [SfP1Transport.constantUnit_hom, leftDerivedUpperStarDerivedTensorUnitIso] at hu
  exact finish_trace_expanded (ordinaryFinitePullback A (𝟙 B))
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).inv.app _)
    _ _ _ _ _ (L.map (vectorIntegrationBaseCoefficientPullback A N hA t π hB d).inv)
    (vectorBundleIntegration N hN A hA B hB d F) _ _ _ htrace hu

end WeilConjectures.PurityFiniteSetting
