/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalPushforward

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.AdicLisseModule
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatum
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationData
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumCompleted
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompleted
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete
import WeilConjectures.AlgebraicGeometry.CompletedTowerPullback
import WeilConjectures.AlgebraicGeometry.CompletedTowerDirectImage
import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import WeilConjectures.Algebra.Homology.DerivedTensor
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import Mathlib.CategoryTheory.Limits.Over
import WeilConjectures.RingTheory.LimitFlatModules
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.Algebra.Homology.SignedDoubleHomCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import Mathlib.Algebra.Homology.ShortComplex.Basic
import WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulQuotientComparison
import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentationIsIso
import WeilConjectures.AlgebraicGeometry.ConstantKoszulAugmentationConstruction
import WeilConjectures.CategoryTheory.TensorQuotientAugmentation
import WeilConjectures.CategoryTheory.RingedNegativeKoszulLowDegrees
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.CategoryTheory.SignedKoszulFiniteCoordinates
import WeilConjectures.CategoryTheory.SignedKoszulTensorCoordinates
import WeilConjectures.CategoryTheory.SignedKoszulTensorCoproduct
import WeilConjectures.CategoryTheory.SignedKoszulTensorAssembly
import WeilConjectures.CategoryTheory.SignedKoszulSummandDifferential
import WeilConjectures.CategoryTheory.SignedKoszulSummandTermTransport
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedNegativeKoszulFactorHomTensor
import WeilConjectures.AlgebraicGeometry.OrderedKoszulHomologyTorsion
import Mathlib.Data.Finset.Sort
import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech
import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.ConstantExactCoefficientRealization
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import WeilConjectures.AlgebraicGeometry.ConstantKoszulCoefficientConeComparison
import WeilConjectures.CategoryTheory.ExteriorKoszulScalarRealization
import WeilConjectures.CategoryTheory.ExteriorKoszulBasisDifferential
import WeilConjectures.CategoryTheory.RingedKoszulDualBasis
import WeilConjectures.CategoryTheory.RingedNegativeKoszulExteriorDifferential
import WeilConjectures.CategoryTheory.RingedNegativeKoszulSignedDifferential
import WeilConjectures.CategoryTheory.RingedNegativeKoszulBasisUnitor
import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import WeilConjectures.AlgebraicGeometry.DerivedChangeOfRingsModel
import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorConeComparison
import WeilConjectures.AlgebraicGeometry.TensorConeTowerIso
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorSquare
import WeilConjectures.AlgebraicGeometry.ConstantScalarTensorModel
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorLevel
import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero
import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import WeilConjectures.RingTheory.KoszulProjectiveResolution
import WeilConjectures.RingTheory.KoszulPowerHomologyProZero
import WeilConjectures.RingTheory.KoszulConeHomologyProZero
import WeilConjectures.Algebra.Homology.BoundedDerivedTowerProZero
import WeilConjectures.CategoryTheory.Triangulated.ProZeroMiddle
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import WeilConjectures.CategoryTheory.GeometricRingInverseImage
import WeilConjectures.CategoryTheory.InverseImageRingFunctor
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.CategoryTheory.RouteInverseImageConstantComparison
import Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.CategoryTheory.RouteInverseImageConstantRingAssembly
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTransport
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTransportEquation
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullExistence
import Mathlib.RingTheory.Ideal.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullUniqueness
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels

/-!
# Proper direct image with rational condensed coefficients: proper base change

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.md, clause 3, proper base
change (blueprint: det-thm-sfb-proper-base-change-rational).

Split off from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational`
for compile time. The recorded
unit--square--counit base-change map with the named rational preservation proof is invertible.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedPushSource derivedPushTarget derivedPushHom
  moduleObjectProjectionMap boundedConstructibleBaseChangeOfPreserves
  DerivedCategory HasDerivedCategory.standard CategoryTheory.Mod.monoidalCategory

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] rationalizationPushHom
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.mapDerivedCategory
set_option allowUnsafeReducibility true in
attribute [local irreducible] rationalCoefficientPushforwardPreservation
  rationalFinitenessPushforwardPreservation
  ContinuousMapRingObj.rationalFinitenessPushforwardPreservation

attribute [local irreducible] derivedTensor moduleObjectProjectionData

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

variable {X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

attribute [local irreducible] boundedConstructibleBaseChange

attribute [local irreducible] boundedConstructibleUpperStar
  derivedUpperStarLowerStarAdjunction ObjectProperty.lift
  boundedConstructibleUpperStarCompatibility boundedConstructiblePullbackSquareComparison
  Functor.squareTransport Adjunction.restrictFullyFaithful

private theorem baseChange_restriction_eq
    (H : PreservesBoundedConstructiblePushforwards (Profinite.padicAlgClRingObj ℓ) k)
    (sq : CommSq g' p' p g) :
    boundedConstructibleBaseChangeOfPreserves (Profinite.padicAlgClRingObj ℓ) ℓ H sq =
      boundedConstructibleBaseChange ℓ sq := by
  with_unfolding_all rfl

private theorem baseChange_restriction_eq_subfield
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (H : PreservesBoundedConstructiblePushforwards (Profinite.continuousMapRingObj E) k)
    (sq : CommSq g' p' p g) :
    boundedConstructibleBaseChangeOfPreserves (Profinite.continuousMapRingObj E) ℓ H sq =
      ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq := by
  with_unfolding_all rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recorded unit--square--counit base-change map is invertible for every proper
cartesian square in the standing setting, with no condition on g.
Source: blueprint rational proper direct image, clause 3, proper base change
(blueprint: det-thm-sfb-proper-base-change-rational).

Proof: the conditional restriction and the finiteness-coefficient restriction have
identical functor data; their preservation arguments are proofs of the same proposition.
After unfolding just the restricted unit, square and counit constructions, proof
irrelevance identifies their base-change transformations. In each of the two bundled
coefficient cases, apply the existing proper base-change theorem to this same map.
The cartesian square is arbitrary apart from the stated properness of p.
-/
theorem isIso_properBaseChange_boundedConstructible_rational
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (sq : IsPullback g' p' p g)
    (K : ProEtale.BoundedConstructible
      (condensedRingObj Λ.X X.left)) :
    IsIso ((boundedConstructibleBaseChangeOfPreserves Λ.X ℓ
      (rationalCoefficientPushforwardPreservation ℓ Λ hΛ)
      sq.toCommSq).app K) := by
  have hΛ' := hΛ
  rcases hΛ' with ⟨E, hE⟩ | hQ
  · subst Λ
    have hstd : IsIso (boundedConstructibleBaseChangeOfPreserves _ ℓ
        (rationalCoefficientPushforwardPreservation ℓ _ hΛ) sq.toCommSq) := by
      have h := isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq
      rw [← baseChange_restriction_eq_subfield ℓ p E
        (ContinuousMapRingObj.rationalFinitenessPushforwardPreservation ℓ E) sq.toCommSq] at h
      exact h
    infer_instance
  · subst Λ
    have hstd : IsIso (boundedConstructibleBaseChangeOfPreserves _ ℓ
        (rationalCoefficientPushforwardPreservation ℓ _ hΛ) sq.toCommSq) := by
      have h := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
      rw [← baseChange_restriction_eq ℓ p
        (rationalFinitenessPushforwardPreservation ℓ) sq.toCommSq] at h
      exact h
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
