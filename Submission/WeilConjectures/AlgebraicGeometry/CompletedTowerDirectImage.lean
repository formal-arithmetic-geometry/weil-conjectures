/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedTowerPullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.LocalProperties
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Submission.WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import Submission.WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import Submission.WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.FourCorners
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import Submission.WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Submission.WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import Submission.WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import Submission.WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import Submission.WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import Submission.WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import Submission.WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
import Submission.WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Total direct image of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1276;
Stacks Project, Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The completed coefficient direct-image structure map adjoint to c_f.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedCoefficientDirectImageMap :
    pbcAdicCompletion Y d ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion X d) :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app (pbcAdicCompletion Y d) ≫
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (completedCoefficientMap f d)

@[instance]
theorem completedEvaluation_preservesKInjective (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (n : ℕ) :
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
      (op n)).PreservesKInjectiveComplexes := by
  constructor
  intro I hI
  exact tower_evaluation_isKInjective (pbcModules T R) I (op n)

end AlgebraicGeometry.Scheme
