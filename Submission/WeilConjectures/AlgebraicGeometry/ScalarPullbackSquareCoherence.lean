/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import Submission.WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import Submission.WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import Submission.WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Submission.WeilConjectures.AlgebraicGeometry.FourCorners
public import Submission.WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import Submission.WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
public import Submission.WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
public import Submission.WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
public import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
public import Submission.WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
public import Submission.WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
public import Submission.WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import Submission.WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import Submission.WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Submission.WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import Submission.WeilConjectures.CategoryTheory.LocalCoefficientLocalization
public import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
public import Submission.WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import Submission.WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import Submission.WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
public import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import Submission.WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
public import Submission.WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Submission.WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
public import Submission.WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
public import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
public import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
public import Submission.WeilConjectures.CategoryTheory.TowerSplitEnvelope
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import Submission.WeilConjectures.RingTheory.FactorsThroughLocalization
public import Submission.WeilConjectures.RingTheory.FilteredColimitOfFactorization
public import Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import Submission.WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import Submission.WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Scalar pullback square coherence

Source: Stacks Project, Tags 03EK, 0D6D, 07A6 and 0E47.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapHomotopyCategory
  AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private instance module_tensor_two
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B : GradedObject ℤ (Modules R T)) : A.HasTensor B := by
  intro j
  infer_instance

private instance module_tensor_four
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C E : GradedObject ℤ (Modules R T)) :
    GradedObject.HasTensor₄ObjExt A B C E := by
  intro i j
  infer_instance

private instance module_tensor_left
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro i j
  infer_instance

private instance module_tensor_right
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro i j
  infer_instance

private instance module_kflat_derivable
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure
      (HomotopyCategory.quasiIso (Modules R T) (.up ℤ)).localizerMorphismKFlat := by
  infer_instance

private instance extension_kflat (φ : Λ ⟶ Λ') [IsMonHom φ] (T : Scheme.{u}) :
    (extension φ T).PreservesKFlatQuasiIso := by
  exact Mod.preservesKFlatQuasiIso (coefficientMap φ T)

/-- The canonical geometric compositor with the scalar interface exposed.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullbackComposition
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    L R (h ≫ k) ≅ L R k ⋙ L R h := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp R h k

/-- The canonical geometric pullback square with the scalar interface exposed.
Source: Stacks 07A7 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullbackSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    L R c ⋙ L R f' ≅ L R f ⋙ L R a :=
  (scalarPullbackComposition R f' c).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ L R h) sq.toCommSq.w.symm) ≪≫
    scalarPullbackComposition R a f

set_option maxHeartbeats 300000 in
-- Specializing the categorical lemma searches instances on categories of module objects.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStar Mod.extendScalars
  CondensedRing.upperStarComp CondensedRing.pullIso
  scalarCounit pullCounit

end AlgebraicGeometry.ProEtale.QuotientChange
