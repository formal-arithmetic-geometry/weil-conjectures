/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
public import Submission.WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

import Submission.WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import Submission.WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Submission.WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.SixFunctors.BaseChange.Square
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import Mathlib.CategoryTheory.Abelian.RightDerived
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Submission.WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Submission.WeilConjectures.ConstructibleSheaf.InternalHom
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Submission.WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import Submission.WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.Grp.Ulift
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceDerivedStalkComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalScalarHomologyIso
import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
import Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalRestriction.ProEtaleLocalDerivedRestrictionComparisonsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import Submission.WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Algebra.Category.Grp.Colimits
import Submission.WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Submission.WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback
import Submission.WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import Submission.WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Submission.WeilConjectures.CategoryTheory.SiteModuleSliceSheafification
import Mathlib.Topology.Sheaves.Abelian
import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import Submission.WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Mathlib.Topology.Connected.Clopen
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Homotopy
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.Mathlib.Topology.NoetherianSpace

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Descended etale stalk data before finite-level local trivialization

Source: Stacks Project, Tag 09C6, the normalized algebraic stalk diagram;
Tags 09AL and 09B1 for finite coefficient descent.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-stalk-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- A descended finite quotient diagram and the coefficient transport from its stalk.

The transport is conditional on a supplied etale isomorphism with the stalk complex.
It supplies neither such an isomorphism nor a covering on which one exists. It includes
further restriction along every arrow to a supplied etale chart.
Source: Stacks Tags 09C6, 09AL and 09B1.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-stalk-data). -/
structure FinitePerfectAdicEtaleStalkData (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (E : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))) where
  connected : ConnectedSpace V.left
  point : V.left
  level : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))
  bounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) q).obj (level n))
  lisse : ∀ (n : ℕ) (q : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) q).obj (level n))
  transport : ∀ (n : ℕ) (U : V.left.Etale), Nonempty
    ((AlgebraicGeometry.Etale.upperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.obj
        (level n) ≅
      (constantSheaf U.left.smallEtaleTopology
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))).mapDerivedCategory.obj
          ((finitePerfectAdicEtaleStalk V.left _ point).obj (level n))) →
    ∀ (W : X.Etale), (W ⟶ Etale.mk (U.hom ≫ V.hom)) → Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            ((finitePerfectAdicDerivedConstant X (A ⧸ d.ideal ^ (n + 1))).obj (E n))))

end AlgebraicGeometry.Scheme
