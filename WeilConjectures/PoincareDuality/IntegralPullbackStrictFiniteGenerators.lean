/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Generator calculation for a strict normalized pullback comparison

Source: Stacks Tags 03D3, 099N(5), and 0941.
(blueprint: lem-pod-integral-pullback-strict-finite-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- These proved implementation helpers are consumed with `import all`.
set_option linter.privateModule false
-- Replaying sectionwise transport proofs for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.mapDerivedCategoryCompIso
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local implicit_reducible] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local implicit_reducible] WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.coefficientConstantTowerEvaluation
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  CategoryTheory.NatIso.mapHomologicalComplex CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local irreducible] CategoryTheory.constantSheaf CategoryTheory.presheafToSheaf
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Proof

attribute [local instance 30000] zeroOfFiniteLimits

attribute [local instance 50] additiveOfFiniteLimits

private theorem exactSquare_fac
    {A₀ A₁ A₂ A₃ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian A₃]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁]
    [HasDerivedCategory A₂] [HasDerivedCategory A₃]
    (U : A₀ ⥤ A₁) (F : A₁ ⥤ A₃) (G : A₀ ⥤ A₂) (R : A₂ ⥤ A₃)
    [U.Additive] [F.Additive] [G.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : U ⋙ F ≅ G ⋙ R) (K : CochainComplex A₀ ℤ) :
    (((Functor.mapDerivedCategoryCompIso U F).symm ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso G R).hom.app
          (DerivedCategory.Q.obj K)) ≫
        R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      F.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, CategoryTheory.Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  erw [Functor.mapDerivedCategoryNatIso_fac]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_factors U F K]
  simp only [CategoryTheory.Category.assoc, Iso.inv_hom_id_app_assoc]

attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

attribute [local irreducible] restrictionEvaluation

attribute [local instance] finitePullback_limits finitePullback_colimits
  nativeFinitePullback_limits nativeFinitePullback_colimits
  mixedFinitePullback_limits mixedFinitePullback_colimits

attribute [local irreducible] finiteEvaluation

attribute [local irreducible] strictLevel

end Proof

end WeilConjectures
