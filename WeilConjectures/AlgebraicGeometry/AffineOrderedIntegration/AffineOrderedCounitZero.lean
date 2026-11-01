/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
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
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalComparisonData
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
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
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology
import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
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
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalTriangles
import WeilConjectures.AlgebraicGeometry.EtaleProperSectionContraction
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
import WeilConjectures.CategoryTheory.AdjunctionUnitTransport
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionIntegral
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
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
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorization
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import Mathlib.Tactic.SuppressCompilation
import WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.EtaleSecondCoordinateContraction
import WeilConjectures.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCounitCoefficient
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceEvaluationNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux
import WeilConjectures.AlgebraicGeometry.EtaleChartExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistComposition
import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Ring.Int.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleExactExchangeComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceScalarSquare
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounitComparisons
import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
import WeilConjectures.AlgebraicGeometry.DerivedPairingOppositeShiftsPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing
import WeilConjectures.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FlatSinglePairingSymmetricPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalFirstCoordinateExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalSecondCoordinateExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitDescentComparison
import all WeilConjectures.AlgebraicGeometry.IntegrationComposition.IteratedIntegration
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization

/-! # The ordinary ordered coefficient-counit induction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.AffineOrderedCounitZeroAux

set_option synthInstance.maxSize 2048

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local implicit_reducible] affineTraceTower affineTraceProjection

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  Etale.rightDerivedLowerShriek

private lemma unit_of_composition
    {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) (L : C ⥤ C) (R : D ⥤ D)
    (e : L ≅ 𝟭 C) (d : R ≅ 𝟭 D) (a : L ⋙ P ≅ P ⋙ R)
    (h : ∀ K, P.map (L.map (e.hom.app K)) ≫ a.hom.app K =
      a.hom.app (L.obj K) ≫ R.map (a.hom.app K) ≫ R.map (d.hom.app (P.obj K)))
    (K : C) : P.map (e.hom.app K) = a.hom.app K ≫ d.hom.app (P.obj K) := by
  have : R.Faithful := CategoryTheory.Functor.Faithful.of_iso d.symm
  apply R.map_injective
  rw [CategoryTheory.Functor.map_comp]
  apply (cancel_epi (a.hom.app (L.obj K))).mp
  have hn := a.hom.naturality (e.hom.app K)
  simp only [CategoryTheory.Functor.comp_map] at hn
  rw [← hn]
  simpa only [CategoryTheory.Functor.id_obj, Category.assoc] using h K

private lemma plus_comparison_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f g : X ⟶ Y} [HasCompactification f] [HasCompactification g] (h : f = g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusCongr A h).hom.app K) ≫
        (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom.app K =
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K ≫
        (unboundedEtaleLowerShriekCongr A h).hom.app (DerivedCategory.Plus.ι.obj K) := by
  subst h
  simp only [rightDerivedLowerShriekPlusCongr, CompactSupportFormalism.lowerShriekCongr,
    unboundedEtaleLowerShriekCongr, Iso.refl_hom, NatTrans.id_app]
  erw [DerivedCategory.Plus.ι.map_id, Category.id_comp, Category.comp_id]

private lemma identity_comparison_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusId A S).hom.app K) =
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S)).hom.app K ≫
        (unboundedEtaleLowerShriekId A S).hom.app (DerivedCategory.Plus.ι.obj K) := by
  apply unit_of_composition DerivedCategory.Plus.ι
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (𝟙 S))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S))
    (rightDerivedLowerShriekPlusId A S) (unboundedEtaleLowerShriekId A S)
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 S))
  intro M
  have h := unboundedEtaleCompactSupport_composition_plus A (𝟙 S) (𝟙 S) M
  rw [rightDerivedLowerShriekPlusCompIso_id_left,
    (unboundedEtaleLowerShriekCompIso_units A (𝟙 S)).1] at h
  simp only [NatTrans.comp_app, CategoryTheory.Functor.leftUnitor_hom_app,
    CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at h
  rw [plus_comparison_congr A (Category.id_comp (𝟙 S)).symm M] at h
  apply (cancel_mono ((unboundedEtaleLowerShriekCongr A
    (Category.id_comp (𝟙 S)).symm).hom.app (DerivedCategory.Plus.ι.obj M))).mp
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj, Category.assoc] using h

private theorem source_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) :
    ordinarySourceIso P Y aY K 0 =
      Etale.OrdinaryAffineCounitTensorNormalization.reassociation
        (AffineLinePurity.Ring P) (exponent P)
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
        (transport P) Y (exponentUnit P Y aY) 0 K ≪≫
      Etale.ordinaryFiniteTensorRightMapIso (AffineLinePurity.Ring P) Y (Iso.refl _)
        ((Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P)
          (exponent P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (annihilates P) (transport P) Y (exponentUnit P Y aY) 0).symm ≪≫
            coefficientComparison P Y aY 0) := by
  exact source_fixed_zero (AffineLinePurity.Ring P) (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
    (transport P) Y (exponentUnit P Y aY) K

private theorem source_fixed_zero (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) :
    ordinarySourceIsoFixed A N hA t Y hY K 0 =
      Etale.OrdinaryAffineCounitTensorNormalization.reassociation A N hN hA t Y hY 0 K ≪≫
      Etale.ordinaryFiniteTensorRightMapIso A Y (Iso.refl _)
        ((Etale.CoordinateCounitArrows.towerTateIso A N hN hA t Y hY 0).symm ≪≫
          Etale.affineLinearCoefficientDescent A N hA t Y hY 0 ≪≫
            Etale.vectorIntegrationBaseCoefficientPullback A N hA t
              (affineTraceProjection Y 0) hY 0) := by
  delta ordinarySourceIsoFixed
  rw [descent_zero]
  delta Etale.OrdinaryAffineCounitTensorNormalization.reassociation
  simp only [Iso.trans_assoc]
  exact congrArg (fun z ↦
    Etale.OrdinaryAffineCounitTensorNormalization.descent A N hA t Y hY 0 K ≪≫
      Etale.ordinaryFiniteTensorPullback A (affineTraceProjection Y 0) K
        (Etale.affineLinearBaseCoefficient A N hA Y 0) ≪≫ z)
    (tensor_iso_transport A Y _ _ _ _)

private theorem tensor_iso_transport (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {K K' L L' L'' M : Etale.DerivedCategoryModule A Y}
    (e : K ≅ K') (a : L ≅ L') (b : L ≅ L'') (v : L' ≅ M) :
    Etale.ordinaryFiniteTensorRightMapIso A Y (Iso.refl K) v ≪≫
        Etale.ordinaryFiniteTensorRightMapIso A Y e (Iso.refl M) =
      Etale.ordinaryFiniteTensorRightMapIso A Y e (a.symm ≪≫ b) ≪≫
        Etale.ordinaryFiniteTensorRightMapIso A Y (Iso.refl K')
          (b.symm ≪≫ a ≪≫ v) := by
  rw [tensor_iso_comp, tensor_iso_comp]
  simp only [Iso.refl_trans, Iso.trans_refl, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc]

private theorem tensor_iso_comp (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {K K' K'' L L' L'' : Etale.DerivedCategoryModule A Y}
    (e : K ≅ K') (e' : K' ≅ K'') (c : L ≅ L') (c' : L' ≅ L'') :
    Etale.ordinaryFiniteTensorRightMapIso A Y e c ≪≫
        Etale.ordinaryFiniteTensorRightMapIso A Y e' c' =
      Etale.ordinaryFiniteTensorRightMapIso A Y (e ≪≫ e') (c ≪≫ c') := by
  let T := Etale.ordinaryFiniteTensor A Y
  apply Iso.ext
  simp only [Etale.ordinaryFiniteTensorRightMapIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Etale.derivedTensorRight,
    Etale.derivedTensorRightFunctor, CategoryTheory.Functor.flip_obj_map,
    CategoryTheory.Functor.flip_map_app,
    Category.assoc]
  change (T.map e.hom).app L ≫ (T.obj K').map c.hom ≫
      (T.map e'.hom).app L' ≫ (T.obj K'').map c'.hom =
    (T.map (e.hom ≫ e'.hom)).app L ≫ (T.obj K'').map (c.hom ≫ c'.hom)
  rw [reassoc_of% (T.map e'.hom).naturality c.hom]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem descent_zero (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) :
    ordinarySourceDescent A N hA t Y hY K 0 =
      Etale.OrdinaryAffineCounitTensorNormalization.descent A N hA t Y hY 0 K := by
  exact (normalized_source_descent A N hA t Y hY K 0).symm

private theorem comparison_zero (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y]
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ordinaryCompactComparison A Y 0 K).inv =
      (Etale.affineDualizingTowerComparison A Y 0).inv.app K.obj := by
  rw [compact_comparison_zero]
  -- Reduce only this zero component; generating equations in arbitrary rank is expensive.
  rfl

private theorem compact_comparison_zero (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y]
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ordinaryCompactComparison A Y 0 K).inv =
      (Etale.unboundedEtaleLowerShriekId A Y).hom.app K.obj := by
  delta ordinaryCompactComparison
  dsimp only [affineTraceProjection]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, CategoryTheory.Functor.mapIso_inv,
    Etale.affineTracePlusCompatibility, Etale.affineTraceCompactSupportComparison]
  rw [identity_comparison_plus]
  simp only [Nat.rec_zero, CategoryTheory.Functor.id_obj, Nat.zero_eq,
    CategoryTheory.Functor.comp_obj,
    ObjectProperty.ι_obj, Iso.inv_hom_id_app_assoc, NatIso.trans_app, Iso.trans_hom,
    Iso.app_hom, CategoryTheory.Functor.leftUnitor_hom_app, Iso.symm_hom,
    CategoryTheory.Functor.rightUnitor_inv_app, Category.comp_id]
  exact Category.comp_id _

end AlgebraicGeometry.Etale.AffineOrderedCounitZeroAux

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite
open Etale.AffineOrderedCounitZeroAux

set_option synthInstance.maxSize 2048
attribute [local implicit_reducible] etaleCategory compactification Etale.affineTraceLeftPlus
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor OrdinaryCounitEquation
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  Etale.derivedTensor Etale.rightDerivedLowerShriek
  Etale.ordinaryFiniteTensorPullback Etale.ordinaryFiniteTensorRightMapIso
  DerivedCategory.singleFunctors Scheme.finiteEtaleTateLine

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
-- Use the same inverse-image instances as the canonical source-descent comparison.
set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1
  Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3
  Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5
  Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7
  Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9
  Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11
  Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local implicit_reducible] affineTraceTower affineTraceProjection
attribute [local semireducible] Etale.affineDualizingTowerComparison
attribute [local implicit_reducible] Etale.affineDualizingTowerComparison
attribute [local irreducible] Etale.unboundedEtaleLowerShriekId
  ordinaryCounit ordinaryTraceRaw
  Etale.OrdinaryAffineCounitTensorNormalization.counit
  Etale.OrdinaryAffineCounitTensorNormalization.trace
  Etale.OrdinaryAffineCounitTensorNormalization.reassociation

private theorem projection_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {W W' : Etale.DerivedCategoryModule A X} (c : W ⟶ W')
    (K : Etale.DerivedCategoryModule A Y) :
    ((Etale.ordinaryFiniteTensor A Y).obj K).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map c) ≫
      Etale.compactSupportProjectionMap A f W' K =
    Etale.compactSupportProjectionMap A f W K ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((Etale.ordinaryFiniteTensor A X).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map c) := by
  exact Etale.IntegrationComposition.projection_naturality f c K

private theorem cancel_projection_exists {C : Type*} [Category C] {X Y Z : C}
    (p₀ : X ⟶ Y) (z : Y ⟶ Z) (r : X ⟶ Z)
    (h : ∃ p : X ≅ Y, p.hom = p₀ ∧ z = p.inv ≫ r) : p₀ ≫ z = r := by
  obtain ⟨p, rfl, hp⟩ := h
  rw [hp, Iso.hom_inv_id_assoc]

private theorem coefficient_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D ⥤ D) {J X X' V V' : C} {U K : D}
    (e : J ≅ X) (m : X ≅ X') (s : J ≅ X') (c : V ≅ V')
    (p : T.obj (F.obj V) ⟶ F.obj X) (p' : T.obj (F.obj V') ⟶ F.obj X')
    (z : F.obj J ⟶ K) (τ : F.obj V ⟶ U) (τ' : F.obj V' ⟶ U)
    (η : T.obj U ⟶ K) (hs : s = e ≪≫ m)
    (hp : p ≫ F.map e.inv ≫ z = T.map τ ≫ η)
    (hn : T.map (F.map c.inv) ≫ p = p' ≫ F.map m.inv)
    (ht : F.map c.inv ≫ τ = τ') : p' ≫ F.map s.inv ≫ z = T.map τ' ≫ η := by
  rw [hs, Iso.trans_inv, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hp]
  rw [← CategoryTheory.Functor.map_comp_assoc, ht]

private theorem counit_transport_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) :
    Etale.OrdinaryAffineCounitTensorNormalization.counit (AffineLinePurity.Ring P)
      (exponent P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) 0 K =
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y 0)).map
        (Etale.OrdinaryAffineCounitTensorNormalization.reassociation (AffineLinePurity.Ring P)
          (exponent P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) Y (exponentUnit P Y aY) 0 K).inv ≫ ordinaryCounit P Y aY K hK 0 := by
  delta Etale.OrdinaryAffineCounitTensorNormalization.counit ordinaryCounit
  rw [comparison_zero]
  rfl

private theorem trace_transport_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y 0)).map
        ((Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) Y (exponentUnit P Y aY) 0).symm ≪≫
          coefficientComparison P Y aY 0).inv ≫
      Etale.OrdinaryAffineCounitTensorNormalization.trace (AffineLinePurity.Ring P)
        (exponent P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
        (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) 0 =
      ordinaryTraceRaw P Y aY 0 := by
  have hcomp : (Etale.affineLinearCompactComparison (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P)
      (annihilates P) Y (exponentUnit P Y aY) 0).inv =
      (Etale.affineDualizingTowerComparison (AffineLinePurity.Ring P) Y 0).inv.app
        ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
          (annihilates P) Y 0).obj (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y)) := by
    apply comparison_zero
  delta Etale.OrdinaryAffineCounitTensorNormalization.trace Etale.affineTraceCounit
    ordinaryTraceRaw
  rw [hcomp]
  simp only [Iso.trans_inv, Iso.symm_inv]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

private theorem projection_counit_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) :
    Etale.compactSupportProjectionMap (AffineLinePurity.Ring P) (affineTraceProjection Y 0)
        (Etale.SectionLocalDualizingComparisons.tateObject (AffineLinePurity.Ring P)
          (exponent P) (annihilates P) (affineTraceTower Y 0) 0) K ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (affineTraceProjection Y 0)).map
          (Etale.OrdinaryAffineCounitTensorNormalization.reassociation (AffineLinePurity.Ring P)
            (exponent P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
            (transport P) Y (exponentUnit P Y aY) 0 K).inv ≫ ordinaryCounit P Y aY K hK 0 =
      ((Etale.derivedTensor (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) Y).obj K).map
        (Etale.OrdinaryAffineCounitTensorNormalization.trace (AffineLinePurity.Ring P)
          (exponent P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) 0) ≫
          (Etale.derivedTensorSingleUnitIso K).hom := by
  have h := cancel_projection_exists _ _ _
    (Etale.ordinaryAffineCounit_tensor_normalization (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P)
      (annihilates P) (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) 0 K)
  rw [counit_transport_zero P Y aY K hK] at h
  exact h

/-- The zero-coordinate coefficient-counit equation.
Source: current blueprint, projection-purity agreement proof, final paragraph;
expanded ordered-transpose argument, Step 6, identity-adjunction base case.
(blueprint: lem-pur-affine-ordered-counit-zero).

Proof: the zero-coordinate tower and both ordered adjoints are identities. The ordinary
compact-support comparison is the inverse of the normalized identity comparison.
The zero descent is defined from the inverse tensor-unitor and identity pullback.
Its unique recursion specification identifies ordinarySourceDescent at zero with
ordinaryDescentZeroRaw. Substitute this in ordinarySourceIso. Naturality of the tensor
unitor and the identity pullback comparison cancel the two tensor-pullback maps.
The canonical identity compact-support projection then cancels the support identity
comparison, leaving the tensor of the identity unit trace followed by the unitor.
The definition of coefficientComparison at zero gives the same unit trace in
ordinaryTraceRaw. Thus both sides are equal, also for the zero ring and empty base. -/
theorem ordinary_counit_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) :
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y 0)
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y 0) 0) K _ (ordinarySourceIso P Y aY K 0)
      (ordinaryCounit P Y aY K hK 0) (ordinaryTraceRaw P Y aY 0) := by
  let A := AffineLinePurity.Ring P
  have hN : 0 < exponent P := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y 0)
  let T := (Etale.ordinaryFiniteTensor A Y).obj K
  let b := Etale.CoordinateCounitArrows.towerTateIso A (exponent P) hN (annihilates P)
    (transport P) Y (exponentUnit P Y aY) 0
  let c := b.symm ≪≫ coefficientComparison P Y aY 0
  let e := Etale.OrdinaryAffineCounitTensorNormalization.reassociation A (exponent P) hN
    (annihilates P) (transport P) Y (exponentUnit P Y aY) 0 K
  have hi : (Etale.ordinaryFiniteTensorRightMapIso A Y (Iso.refl _) c).inv =
      ((Etale.ordinaryFiniteTensor A Y).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A)
          (affineTraceProjection Y 0)).mapDerivedCategory.obj K)).map
          c.inv := by
    simp only [Etale.ordinaryFiniteTensorRightMapIso, Iso.trans_inv, Iso.refl_inv,
      CategoryTheory.Functor.mapIso_inv, Iso.app_inv, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rfl
  have hn : T.map (F.map c.inv) ≫
      Etale.compactSupportProjectionMap A (affineTraceProjection Y 0) _ K =
    Etale.compactSupportProjectionMap A (affineTraceProjection Y 0) _ K ≫
      F.map (Etale.ordinaryFiniteTensorRightMapIso A Y (Iso.refl _) c).inv := by
    dsimp only [T, F]
    rw [hi]
    exact projection_naturality A (affineTraceProjection Y 0) c.inv K
  have h := coefficient_transport F T e
    (Etale.ordinaryFiniteTensorRightMapIso A Y (Iso.refl _) c)
    (ordinarySourceIso P Y aY K 0) c _ _ (ordinaryCounit P Y aY K hK 0) _
    (ordinaryTraceRaw P Y aY 0) (Etale.derivedTensorSingleUnitIso K).hom
    (source_zero P Y aY K) (projection_counit_zero P Y aY K hK) hn
    (trace_transport_zero P Y aY)
  exact h.trans (Etale.ordinaryFiniteTensorTrace_app A Y (ordinaryTraceRaw P Y aY 0) K).symm

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
