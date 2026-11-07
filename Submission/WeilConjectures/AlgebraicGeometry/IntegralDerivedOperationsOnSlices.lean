/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import Submission.WeilConjectures.Algebra.Homology.DerivedTensor
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDifferential
public import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import Submission.WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import Submission.WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import Submission.WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
public import Submission.WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

set_option linter.privateModule false
/-!
# Completed integral operations on the global site and its slices

Source: Bhatt--Scholze, Definition 3.4.10 and Definition 3.5.2; Stacks Project,
Tags 06YY and 08TC (auxiliary; not a blueprint node).

The option is only an index for the two sites in the consumer: none is the global
site; some U is its actual over-site. Coefficients and quotient projections on the
latter are sectionwise restrictions. Site object and morphism sizes stay t+1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe a b c d e f r

private theorem completedCoconeLift_f (M : Type*) [Category* M] [Abelian M]
    {C K L : CochainComplex M ℤ} (φ : K ⟶ L) (u : C ⟶ K)
    (hu : u ≫ φ = 0) (p : ℤ) :
    (CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])).f p =
      u.f p ≫ (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) := by
  let l := CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])
  have h := CochainComplex.mappingCocone.id_X φ p (p + -1) rfl
  calc
    l.f p = l.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ := by
      rw [← h, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        CochainComplex.mappingCocone.lift_f_fst_f,
        CochainComplex.mappingCocone.lift_f_snd_v]
      simp

private theorem completedCoconeLift_natural (M : Type*) [Category* M] [Abelian M]
    {C D K₁ K₂ L₁ L₂ : CochainComplex M ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (α : C ⟶ D) (u : C ⟶ K₁) (v : D ⟶ K₂)
    (hu : u ≫ φ₁ = 0) (hv : v ≫ φ₂ = 0) (hn : α ≫ v = u ≫ a) :
    α ≫ CochainComplex.mappingCocone.lift φ₂ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu]) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro p
  have hi : (CochainComplex.mappingCocone.inl φ₁).v p p (add_zero p) ≫
      ((CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧').f p =
      a.f p ≫ (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) := by
    simp [CochainComplex.mappingCocone.inl,
      CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
      CochainComplex.mappingCone.map]
  simp only [HomologicalComplex.comp_f]
  rw [completedCoconeLift_f M φ₂ v hv p, completedCoconeLift_f M φ₁ u hu p,
    Category.assoc, hi, ← Category.assoc]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun z ↦ z.f p ≫
      (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p)) hn

namespace WeilConjectures
namespace IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

variable (U : Option X.ProEt)

section TransitionConstruction

end TransitionConstruction

attribute [local irreducible] SheafOfModules.monoidalCategory HasDerivedCategory.standard
  constantSheaf completedIntegralCoefficientSheafUnrestricted

end IntegralOnSlice
end WeilConjectures
