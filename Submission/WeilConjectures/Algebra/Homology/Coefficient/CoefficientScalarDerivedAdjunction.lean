/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Submission.WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import Submission.WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Submission.WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import Submission.WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import Submission.WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.NormalizedLeftExtension
import Submission.WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import Submission.WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension
import Submission.WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import Submission.WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import Submission.WeilConjectures.Algebra.Homology.System.SystemScalarDerivedExtension
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
import Submission.WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import Submission.WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Scalar extension with its normalized derived adjunction

Source: Stacks Project, Tags 06YY, 06XN and 09T5.
(blueprint: lem-pur-coefficient-scalar-derived-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The family of universal derived quotient scalar extensions.
Source: Stacks Tags 06YY and 09T5
(blueprint: lem-pur-coefficient-scalar-derived-adjunction). -/
abbrev CoefficientScalarDerivedAssignment :=
  ∀ {m n : ℕ} (h : n ≤ m), DerivedCoefficientScalarExtension
    (coefficientTensor (J := J) (O := O) (ell := ell) h)
    (coefficientRestriction (J := J) O ell h)
    (coefficientTensorAdj (J := J) (O := O) (ell := ell) h)
    ((CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell m)))

end SheafOfModules
