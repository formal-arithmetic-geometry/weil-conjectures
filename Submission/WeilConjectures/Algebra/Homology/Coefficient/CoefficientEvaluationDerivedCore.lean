/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Deriving the coefficient evaluation adjunction

Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tags 06XN and 09T5.
(blueprint: lem-pur-coefficient-evaluation-derived-core).
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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

/-- A derived evaluation adjunction and its comparison on complex representatives.
Source: Zheng, Construction 4.1, p. 21; Stacks Tags 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-core). -/
structure CoefficientEvaluationDerivedCoreData
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] where
  evaluation : ∀ n, DerivedCategory (CoefficientSystem (J := J) O ell) ⥤
    DerivedCategory (coefficientLevelModules (J := J) O ell n)
  evaluationFactors : ∀ n, DerivedCategory.Q ⋙ evaluation n ≅
    (coefficientEvaluation (J := J) (O := O) (ell := ell) n).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q
  derivedExtension : ∀ n, DerivedCategory (coefficientLevelModules (J := J) O ell n) ⥤
    DerivedCategory (CoefficientSystem (J := J) O ell)
  counit : ∀ n, DerivedCategory.Q ⋙ derivedExtension n ⟶
    (ordinary.extension n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  pointwise : ∀ n,
    ((ordinary.extension n).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso (coefficientLevelModules (J := J) O ell n) (.up ℤ))
  isDerived : ∀ n, (derivedExtension n).IsLeftDerivedFunctor (counit n)
    (HomologicalComplex.quasiIso (coefficientLevelModules (J := J) O ell n) (.up ℤ))
  computes : ∀ n P, P.IsKFlatIndependentCoefficients → IsIso ((counit n).app P)
  derivedAdj : ∀ n, derivedExtension n ⊣ evaluation n
  transpose : ∀ n P K
      (f : ((ordinary.extension n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (derivedAdj n).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      ((counit n).app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map (((ordinary.adj n).mapHomologicalComplex (.up ℤ)).homEquiv
          P K f) ≫ (evaluationFactors n).inv.app K

end SheafOfModules
