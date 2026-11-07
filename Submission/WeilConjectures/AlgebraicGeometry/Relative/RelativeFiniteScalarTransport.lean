/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteScalarRestriction
import all Submission.WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.LocalSite
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.Topology.Constructible
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Submission.WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Abelian.RightDerived
import all Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import all Mathlib.Algebra.Homology.Additive
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import all Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.RingTheory.Ideal.Quotient.PowTransition
import all Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all Submission.WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import all Submission.WeilConjectures.CategoryTheory.RingedKoszulSystem
import all Submission.WeilConjectures.CategoryTheory.RingedExtendedCech
import all Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.Algebra.Homology.HomComplex
import all Submission.WeilConjectures.CategoryTheory.RingedCompletionUnit
import all Submission.WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
import all Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Submission.WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all Mathlib.CategoryTheory.Sites.Over
import all Submission.WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all Submission.WeilConjectures.CategoryTheory.RingedIdealGenerators
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Submission.WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import all Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all Submission.WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Finiteness.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all Submission.WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import all Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import all Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.CategoryTheory.Limits.Final
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.RingTheory.Flat.Basic
import all Mathlib.RingTheory.Flat.Tensor
import all Mathlib.LinearAlgebra.TensorProduct.RightExactness
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Linear.FunctorCategory
import all Mathlib.CategoryTheory.Linear.LinearFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import all Mathlib.CategoryTheory.Limits.Over
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all Submission.WeilConjectures.RingTheory.LimitFlatModules
import all Mathlib.RingTheory.Flat.EquationalCriterion
import all Mathlib.RingTheory.TensorProduct.Quotient
import all Mathlib.RingTheory.Ideal.Quotient.Noetherian
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import all Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import all Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionFinitePullSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.RingTheory.Ideal.Quotient.Defs
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import all Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Scalar extension commutes with explicit small-site coefficient transport -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open CategoryTheory.ConstantCompletion

private def pullbackScalarIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedExtend φ ⋙ adicTowerPullback g S ≅
      adicTowerPullback g R ⋙ pbcDerivedExtend ((adicTowerInverseImage g).map φ) := by
  let R' := (adicTowerInverseImage g).obj R
  let S' := (adicTowerInverseImage g).obj S
  let φ' := (adicTowerInverseImage g).map φ
  let adjR := (proEtaleRingDerivedOperations_adjunction g R R' (Iso.refl _)).some
  let adjS := (proEtaleRingDerivedOperations_adjunction g S S' (Iso.refl _)).some
  let δ := proEtaleRingRestrictionDerivedDirectImage g R S R' S' φ φ'
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact ((pbcDerivedScalarAdjunction φ).comp adjS).leftAdjointUniq
    ((adjR.comp (pbcDerivedScalarAdjunction φ')).ofNatIsoRight δ.symm)

private def transportLeftAdjoints
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ C) (F : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (sq : R ⋙ E.functor ≅ F.functor ⋙ R') :
    E.functor ⋙ L' ≅ L ⋙ F.functor := by
  let r : F.inverse ⋙ R ≅ R' ⋙ E.inverse :=
    Functor.isoWhiskerLeft (F.inverse ⋙ R) E.unitIso ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft F.inverse sq) E.inverse ≪≫
      Functor.isoWhiskerRight F.counitIso (R' ⋙ E.inverse)
  exact ((E.toAdjunction.comp b).ofNatIsoRight r.symm).leftAdjointUniq
    (a.comp F.toAdjunction)

private theorem smallScalarAdjunction
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (f : R ⟶ S) : Nonempty (extend f ⊣ dres f) := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with toPreadditive := inferInstance }
  let : Abelian (Mod S) :=
    { (inferInstance : Abelian (Mod S)) with toPreadditive := inferInstance }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  have hpres {P Q : Cx R} (a : P ⟶ Q)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
      (ha : QuasiIso a) :
      QuasiIso (((change f).mapHomologicalComplex (.up ℤ)).map a) :=
    change_preserves_kFlat_quasiIso J f a
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mp hQ) ha
  obtain ⟨_, L, ε, hu, _, d, _⟩ := Adjunction.exists_leftDerived_adjunction
    (change f) (res f) (SheafOfModules.tensorAdjunction f)
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ by
      obtain ⟨Y, s, hY, _, hs, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
      exact ⟨Y, s, hY, hs⟩) hpres
  have : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := hu
  have : (extend f).IsLeftDerivedFunctor (extendComparison f)
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := (derivedExtension f).universal
  exact ⟨d.ofNatIsoLeft (Functor.leftDerivedUnique (extend f) L ε (extendComparison f)
    (HomologicalComplex.quasiIso (Mod R) (.up ℤ)))⟩

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Transport and inverse image commute with derived scalar extension, without any
assumption on cohomology, finite generation, or the coefficient homomorphism.

Source: Stacks Project, Cohomology on Sites, Tag 06YY; Modules on Sites, Tags 03CY and 03D1.
(blueprint: lem-weil-pbc-relative-finite-scalar-transport)

Proof: restriction of scalars and precomposition with AsSmall.down commute on
sections. Naturality of the two canonical constant-section isomorphisms identifies
the scalar actions as well, giving the commutative square of exact restriction
functors. The same holds for the restriction and inverse-image square, by the
canonical ring-sheaf change adjunction. Pass these exact functors and their
isomorphisms to the derived categories. The native scalar extension is left adjoint
to pbcDerivedRestrict and the small-site extension to ConstantCompletion.dres.
Compose the adjunctions with the inverse equivalences for relativeFiniteModelDerived
and with the inverse-image/direct-image adjunction. The two composite right adjoints
are isomorphic by the restriction squares. Uniqueness of left adjoints gives the
displayed isomorphism. On K-flat representatives it is the map identifying the same
pure tensors, so it agrees with the recorded adicFiniteExtension. No choice of a
new derived scalar extension is made. -/
theorem relativeFiniteScalarTransport {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] (f : B →+* R) :
    Nonempty ((pbcDerivedExtend ((constantSheaf (ProEt.topology X)
        CommRingCat.{u + 1}).map (CommRingCat.ofHom f)) ⋙
      adicTowerPullback g (adicLisseConstantRing X R) ⋙ relativeFiniteModelDerived g R) ≅
      (adicTowerPullback g (adicLisseConstantRing X B) ⋙
        relativeFiniteModelDerived g B ⋙
          adicFiniteExtension (proEtaleModelTopology Y) f)) := by
  let := HasDerivedCategory.standard (Mod (constant (proEtaleModelTopology Y) B))
  let := HasDerivedCategory.standard (Mod (constant (proEtaleModelTopology Y) R))
  let φ := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom f)
  let φ' := (adicTowerInverseImage g).map φ
  let ψ := (constantSheaf (proEtaleModelTopology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom f)
  obtain ⟨sq⟩ := relativeFiniteScalarRestriction g f
  let := (siteRestrictScalars_exact ψ).1
  let := (siteRestrictScalars_exact ψ).2
  let sqD := Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso sq ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  obtain ⟨adj⟩ := smallScalarAdjunction ψ
  let E := (relativeFiniteModelModules g B).mapDerivedCategory.asEquivalence
  let F := (relativeFiniteModelModules g R).mapDerivedCategory.asEquivalence
  let e : relativeFiniteModelDerived g B ⋙
        adicFiniteExtension (proEtaleModelTopology Y) f ≅
      pbcDerivedExtend φ' ⋙ relativeFiniteModelDerived g R :=
    transportLeftAdjoints E F (pbcDerivedScalarAdjunction φ')
      adj sqD
  exact ⟨Functor.isoWhiskerRight (pullbackScalarIso g φ) _ ≪≫
    Functor.isoWhiskerLeft (adicTowerPullback g (adicLisseConstantRing X B)) e.symm⟩

end AlgebraicGeometry.Scheme
