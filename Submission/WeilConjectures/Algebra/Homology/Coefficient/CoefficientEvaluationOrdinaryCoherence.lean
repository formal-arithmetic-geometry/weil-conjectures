/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
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
import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationStrictSigma

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Strict tensor and truncation coherence on complexes

Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03EK.
(blueprint: lem-pur-coefficient-evaluation-ordinary-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
local notation "ev" => coefficientEvaluation (J := J) (O := O) (ell := ell)
local notation "tensor" => coefficientTensor (J := J) (O := O) (ell := ell)

/-- The normalized ordinary tensor comparisons, strict truncation inclusions and their
termwise complex lifts. Source: Zheng, Construction 4.1; Stacks Tag 03EK
(blueprint: lem-pur-coefficient-evaluation-ordinary-coherence). -/
structure CoefficientEvaluationOrdinaryCoherenceData
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] where
  tensorUnit : ∀ n, (tensor (Nat.le_refl n)) ≅ 𝟭 _
  tensorUnit_normalized : CoefficientTensorUnitNormalized tensorUnit
  tensorAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (tensor h₁) ⋙ (tensor h₂) ≅ (tensor (h₂.trans h₁))
  tensorAssoc_normalized : CoefficientTensorAssocNormalized tensorAssoc
  strictSigma : ∀ {m n} (h : n ≤ m),
    (tensor h) ⋙ ordinary.extension n ⟶ ordinary.extension m
  strictSigma_below : ∀ {m n q} (h : n ≤ m) (hq : q ≤ n) F,
    (ordinary.below hq).inv.app ((tensor h).obj F) ≫
      (ev q).map ((strictSigma h).app F) ≫ (ordinary.below (hq.trans h)).hom.app F =
        (tensorAssoc h hq).hom.app F
  strictSigma_above : ∀ {m n q} (h : n ≤ m) (_hq : n < q) F,
    (ev q).map ((strictSigma h).app F) = 0
  strictSigma_transpose : ∀ {m n} (h : n ≤ m) F,
    (ordinary.adj n).homEquiv _ _ ((strictSigma h).app F) =
      (ordinary.below h).inv.app F
  strictSigmaComplex : ∀ {m n} (h : n ≤ m) P,
    ((ordinary.extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((tensor h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ⟶
    ((ordinary.extension m).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  strictSigmaComplex_f : ∀ {m n} (h : n ≤ m) P i,
    (strictSigmaComplex h P).f i = (strictSigma h).app (P.X i)
  tensorUnitComplex : ∀ n P,
    ((tensor (Nat.le_refl n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ≅ P
  tensorUnitComplex_f : ∀ n P i,
    ((tensorUnitComplex n P).hom).f i = (tensorUnit n).hom.app (P.X i)
  tensorAssocComplex : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    ((tensor h₂).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj
      (((tensor h₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
    ((tensor (h₂.trans h₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
  tensorAssocComplex_f : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P i,
    ((tensorAssocComplex h₁ h₂ P).hom).f i = (tensorAssoc h₁ h₂).hom.app (P.X i)

end SheafOfModules
