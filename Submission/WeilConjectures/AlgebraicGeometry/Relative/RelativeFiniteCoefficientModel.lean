/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Submission.WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
public import Submission.WeilConjectures.CategoryTheory.RingedKoszulSystem
public import Submission.WeilConjectures.CategoryTheory.RingedExtendedCech
public import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Submission.WeilConjectures.CategoryTheory.RingedCompletionUnit
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
public import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Submission.WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Submission.WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Submission.WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import Submission.WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Submission.WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Submission.WeilConjectures.RingTheory.LimitFlatModules
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
public import Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionFinitePullSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Submission.WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteConstantSliceComparison
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteScalarTransport
import Mathlib.RingTheory.Finiteness.Cardinality

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Relative finite coefficients on the equivalent small site -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem finiteLocalModels_of_iso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B]
    {F G : SheafOfModules.{u + 1} (SheafOfModules.constantCoefficientRing J B)}
    (e : F ≅ G) (h : SheafOfModules.IsLocallyConstantFiniteTypeModules J B F) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J B G := by
  intro V
  obtain ⟨S, hS, hs⟩ := h V
  refine ⟨S, hS, fun W f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hs W f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso e.symm ≪≫ i⟩⟩

private theorem finiteLocalModels_iso_iff
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B]
    {F G : SheafOfModules.{u + 1} (SheafOfModules.constantCoefficientRing J B)}
    (e : F ≅ G) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J B F ↔
      SheafOfModules.IsLocallyConstantFiniteTypeModules J B G :=
  ⟨finiteLocalModels_of_iso J B e, finiteLocalModels_of_iso J B e.symm⟩

private theorem relativeFiniteLisse_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) :
    IsRelativelyFiniteLisseModule g B F ↔
      SheafOfModules.IsLocallyConstantFiniteTypeModules (proEtaleModelTopology Y) B
        ((relativeFiniteModelModules g B).obj F) := by
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_functor
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsDenseSubsite
      (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsDenseSubsite
      (proEtaleModelTopology Y) (ProEt.topology Y) :=
    inferInstanceAs (AsSmall.down.IsDenseSubsite _ _)
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsDenseSubsite
      (ProEt.topology Y) (proEtaleModelTopology Y) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsDenseSubsite
      (ProEt.topology Y) (proEtaleModelTopology Y))
  constructor
  · rintro ⟨S, hS, hs⟩ V
    let S' := S.pullback (terminal.from (AsSmall.down.obj V))
    refine ⟨S'.functorPullback AsSmall.down, ?_, fun W a ha ↦ ?_⟩
    · exact AsSmall.down.cover_lift (proEtaleModelTopology Y) (ProEt.topology Y)
        ((ProEt.topology Y).pullback_stable _ hS)
    · obtain ⟨M, hM, hm⟩ := hs (AsSmall.down.obj W)
        (AsSmall.down.map a ≫ terminal.from (AsSmall.down.obj V)) ha
      have : Finite M := hM
      exact ⟨M, inferInstance, (relativeFiniteConstantSliceComparison g B F M W).mp hm⟩
  · intro hF
    obtain ⟨S, hS, hs⟩ := hF (AsSmall.up.obj (⊤_ Y.ProEt))
    refine ⟨S.functorPullback AsSmall.up, ?_, fun V a ha ↦ ?_⟩
    · exact AsSmall.up.cover_lift (ProEt.topology Y) (proEtaleModelTopology Y) hS
    · obtain ⟨M, hM, hm⟩ := hs (AsSmall.up.obj V) (AsSmall.up.map a) ha
      have : Module.Finite B M := hM
      exact ⟨M, Module.finite_of_finite B,
        (relativeFiniteConstantSliceComparison g B F M (AsSmall.up.obj V)).mpr hm⟩

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Exact small-site models preserve relative finite lissity and coefficient extension.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03A0; Cohomology on Sites,
Tags 06YY and 094I.
(blueprint: lem-weil-pbc-relative-finite-coefficient-model)

Proof: identify inverse-image constant coefficients with native constant coefficients
by the canonical constant-section isomorphism. Precompose native ring sheaves and
module sheaves with AsSmall.down. The site equivalence gives an exact equivalence of
module categories; the constant-sheaf comparison identifies the resulting coefficient
ring with the actual small-site constant commutative ring sheaf. Let L be the image
of the pulled-back complex under this exact equivalence. The homology comparison for
exact functors gives the displayed preservation of zero cohomology.

On every slice, these equivalences identify relative constant modules with constant
coefficient modules. Transport covering sieves along AsSmall.up and AsSmall.down.
A finite module is finitely generated, and over finite B a finitely generated module
has finite underlying set. This gives the first lissity equivalence, including empty
slices and the zero ring. Restriction of scalars commutes with site transport and the
canonical coefficient isomorphisms: on sections the comparison is the identity with
the scalar action identified by naturality of the constant-section map. Uniqueness
of left adjoints therefore identifies derived scalar extension with adicFiniteExtension,
including after pullback. Apply the same slice argument over R and the exact-functor
homology comparison to obtain the second equivalence. No nilpotence, surjectivity,
boundedness, normalization, tower, or stratification is used in this comparison. -/
theorem exists_relative_finite_coefficient_model {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] [Finite B] [Finite R]
    (f : B →+* R)
    (K : DerivedCategory (pbcModules X (adicLisseConstantRing X B))) :
    let J := proEtaleModelTopology Y
    ∃ L : CategoryTheory.ConstantCompletion.D
        (CategoryTheory.ConstantCompletion.constant J B),
      (∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor
          (pbcModules X (adicLisseConstantRing X B)) q).obj K) →
        IsZero ((coefficientModelCohomology _ q).obj L)) ∧
      (∀ q : ℤ, IsRelativelyFiniteLisseModule g B
          ((DerivedCategory.homologyFunctor
              (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) q).obj
            ((adicTowerPullback g (adicLisseConstantRing X B)).obj K)) ↔
        SheafOfModules.IsLocallyConstantFiniteTypeModules J B
          ((coefficientModelCohomology _ q).obj L)) ∧
      (∀ q : ℤ, IsRelativelyFiniteLisseModule g R
          ((DerivedCategory.homologyFunctor
              (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X R))) q).obj
            ((adicTowerPullback g (adicLisseConstantRing X R)).obj
              ((pbcDerivedExtend ((constantSheaf (ProEt.topology X)
                CommRingCat.{u + 1}).map (CommRingCat.ofHom f))).obj K))) ↔
        SheafOfModules.IsLocallyConstantFiniteTypeModules J R
          ((coefficientModelCohomology _ q).obj
            ((adicFiniteExtension J f).obj L))) := by
  let P := (adicTowerPullback g (adicLisseConstantRing X B)).obj K
  let L := (relativeFiniteModelDerived g B).obj P
  refine ⟨L, ?_, ?_, ?_⟩
  · intro q hq
    let F := proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)
    have hp : IsZero ((DerivedCategory.homologyFunctor _ q).obj P) :=
      (F.map_isZero hq).of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm
    exact ((relativeFiniteModelModules g B).map_isZero hp).of_iso
      (relativeFiniteModelHomologyIso g B P q).symm
  · intro q
    exact (relativeFiniteLisse_iff g B _).trans
      (finiteLocalModels_iso_iff (proEtaleModelTopology Y) B
        (relativeFiniteModelHomologyIso g B P q))
  · intro q
    obtain ⟨e⟩ := relativeFiniteScalarTransport g f
    let Kr := (pbcDerivedExtend ((constantSheaf (ProEt.topology X)
      CommRingCat.{u + 1}).map (CommRingCat.ofHom f))).obj K
    let Pr := (adicTowerPullback g (adicLisseConstantRing X R)).obj Kr
    let eh := relativeFiniteModelHomologyIso g R Pr q ≪≫
      (coefficientModelCohomology _ q).mapIso (e.app K)
    exact (relativeFiniteLisse_iff g R _).trans
      (finiteLocalModels_iso_iff (proEtaleModelTopology Y) R eh)

end AlgebraicGeometry.Scheme
