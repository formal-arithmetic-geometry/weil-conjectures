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
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Explicit transport of inverse-image constant coefficients to the small site -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Inverse image preserves the constant coefficient ring by uniqueness of left adjoints.
Source: Stacks Tag 0H7J
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
theorem relativeFiniteConstantInverseImage_isIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of B)) := by
  let G := proEtaleBaseChange g
  let hX : IsTerminal (⊤_ X.ProEt) := terminalIsTerminal
  let hY := hX.isTerminalObj G _
  let aX := constantSheafAdj (ProEt.topology X) CommRingCat.{u + 1} hX
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let a := (aX.comp adj).ofNatIsoRight (Iso.refl _)
  let b := constantSheafAdj (ProEt.topology Y) CommRingCat.{u + 1} hY
  let e := a.leftAdjointUniq b
  have he : proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of B) = e.hom.app (CommRingCat.of B) := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id, Adjunction.comp_homEquiv]
    dsimp [proEtaleConstantInverseImageMap]
    rw [← Adjunction.homEquiv_counit]
    dsimp only [adj]
    rw [Equiv.apply_symm_apply]
    dsimp only [proEtaleConstantDirectImageMap, aX, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hX).homEquiv _ _
      (((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
        _ _)
        (((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

/-- The canonical coefficient identification, first along the equivalence of sites,
then along inverse image. Both comparisons are constructed by their adjunctions.
Source: Stacks Tags 00VC, 03A0, and 0H7J
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelCoefficient {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B ≅
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have := relativeFiniteConstantInverseImage_isIso g B
  exact ((e.constantSheafSheafCongrIso (ProEt.topology Y) (proEtaleModelTopology Y)
    CommRingCat.{u + 1} terminalIsTerminal).app (CommRingCat.of B)).symm ≪≫
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).mapIso
          (asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
            (CommRingCat.of B))).symm

/-- Sectionwise transport with scalar action through the canonical coefficient map.
There is no choice of module objects in this definition.
Source: Stacks Tags 03A0 and 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelModules {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) ⥤
      CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B) :=
  proEtaleModuleToModel ((adicLisseForget Y).obj
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (relativeFiniteModelCoefficient g B).hom)

private theorem toModel_isEquivalence (Y : Scheme.{u})
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).IsEquivalence := by
  let S := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsContinuous
      (ProEt.topology Y) (proEtaleModelTopology Y) := proEtaleModelUp_isContinuous Y
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology Y) (ProEt.topology Y)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)) (𝟙 R) (𝟙 S)
    (by ext V; dsimp [AsSmall.equiv]; erw [S.obj.map_id]; rfl)
    (by ext V; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)
  exact inferInstanceAs e.inverse.IsEquivalence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem isoRestriction_isEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence := by
  let ec : C ≌ C := CategoryTheory.Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [S.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : S ⟶ S ↦ (f.hom.app V).hom x) c.inv_hom_id.symm)
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [R.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : R ⟶ R ↦ (f.hom.app V).hom x) c.hom_inv_id)
  exact inferInstanceAs e.functor.IsEquivalence

/-- The explicit coefficient transport is an equivalence of module categories.
Source: Stacks Tags 03A0 and 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
instance relativeFiniteModelModules_isEquivalence {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    (relativeFiniteModelModules g B).IsEquivalence := by
  have := toModel_isEquivalence Y ((adicLisseForget Y).obj
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
  have : (SheafOfModules.restrictScalars
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (relativeFiniteModelCoefficient g B).hom)).IsEquivalence :=
    isoRestriction_isEquivalence
    ((sheafCompose (proEtaleModelTopology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (relativeFiniteModelCoefficient g B))
  unfold relativeFiniteModelModules
  infer_instance

/-- The transport preserves addition on maps, section by section.
Source: Stacks Tag 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
instance relativeFiniteModelModules_additive {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] : (relativeFiniteModelModules g B).Additive where
  map_add := by intros; rfl

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- The exact transport on the standard derived localizations.
Source: Stacks Tags 03D1 and 05RU
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelDerived {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    DerivedCategory (pbcModules Y
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) ⥤
      CategoryTheory.ConstantCompletion.D
        (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B) := by
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod
    (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B))
  exact (relativeFiniteModelModules g B).mapDerivedCategory

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Exact transport commutes with homology in every degree.
Source: Stacks Tag 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelHomologyIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (pbcModules Y
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))) (q : ℤ) :
    (relativeFiniteModelModules g B).obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (coefficientModelCohomology _ q).obj ((relativeFiniteModelDerived g B).obj K) := by
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod
    (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B))
  exact ((relativeFiniteModelModules g B).mapDerivedCategoryHomologyFunctorIso q).app K

end AlgebraicGeometry.Scheme
