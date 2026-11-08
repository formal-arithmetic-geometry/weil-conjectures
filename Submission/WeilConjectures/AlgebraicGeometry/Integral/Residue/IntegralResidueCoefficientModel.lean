/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import Submission.WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
import Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import Submission.WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Submission.WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import Submission.WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.HasLimits
import Submission.WeilConjectures.SixFunctors.Open.OpenDvrAugmentedTowerComparison
import Submission.WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import Submission.WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import Submission.WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import Submission.WeilConjectures.SmoothPurity.Integral.IntegralPrincipalConeQuotientComparison
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Submission.WeilConjectures.Algebra.Homology.RoosComplex
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Submission.WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
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
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Data.Nat.Prime.Infinite
import Submission.WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.Ring
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.Mathlib.CategoryTheory.NatIso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Submission.WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Normalized DVR coefficient comparison without open-completeness data

Source: Bhatt--Scholze, Definition 6.5.1 and Lemma 6.5.8(1).
(blueprint: lem-weil-pbc-integral-residue-coefficient-model).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale WeilConjectures
namespace AlgebraicGeometry.Scheme

/-- Only the finite coefficient comparisons and their completed limit are retained.
No quotient-completeness criterion or open-operation model is part of this structure.
Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-integral-residue-coefficient-model). -/
structure IntegralResidueCoefficientModel
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) where
  /-- At each level the constant sheaf is identified with continuous component functions. -/
  finite : ∀ n : ℕ, integralCoefficientSheaf.{u, u} l E T n ≅ completedAdicFiniteRing T d n
  /-- The comparison sends each local constant scalar to that same constant function. -/
  finite_constants : ∀ (n : ℕ) (V : T.ProEtᵒᵖ)
      (a : Padic.coefficientExtensionIntegers l E),
    (finite n).hom.hom.app V ((adicLisseConstantUnit T
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).app V
      (ULift.up (Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1)) a))) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app V
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a))
  /-- All quotient maps are respected, before taking the limit. -/
  finite_transition : ∀ n : ℕ,
    integralCoefficientSheafTransition.{u, u} l E T n ≫ (finite n).hom =
      (finite (n + 1)).hom ≫ completedAdicFiniteStep T d n
  /-- The completed comparison is an isomorphism of commutative ring sheaves. -/
  completed : completedAdicCommRing T d ≅ completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  /-- It is precisely the comparison induced by the entire finite quotient diagram. -/
  completed_projection : ∀ n : ℕ,
    (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      completed.hom ≫
        limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op n) ≫ (finite n).hom =
      completedAdicProjection T d n

end AlgebraicGeometry.Scheme
