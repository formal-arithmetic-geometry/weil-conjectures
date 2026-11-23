/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedScalarExtUnit

/-! # Degree-zero scalar Ext units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC uB vC vB wC wB wE
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
  (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- For exact additive `U` and `η : F ⟶ U H` with `DerivedUnit`, the degree-zero class
`mk₀ η` has `DerivedExtUnit`.
Source: Stacks Tags 0152, 06YY and 0GLZ. -/
theorem DerivedUnit.extUnit_zero {F : B} {H : C} {η : F ⟶ U.obj H}
    (h : U.DerivedUnit F H η) : U.DerivedExtUnit F H 0 (Ext.mk₀.{wE} η) := by
  unfold DerivedExtUnit DerivedUnit at *
  intro K
  let e := (shiftFunctorZero (DerivedCategory C) ℤ).app
    ((DerivedCategory.singleFunctor C 0).obj H)
  have hb := (h K).comp e.homFromEquiv.bijective
  have he (f : ((DerivedCategory.singleFunctor C 0).obj H)⟦(0 : ℤ)⟧ ⟶ K) :
      (Ext.mk₀.{wE} η).hom ≫
        ((U.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(0 : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (0 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj H) ≫ U.mapDerivedCategory.map f =
      (DerivedCategory.singleFunctor B 0).map η ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫
          U.mapDerivedCategory.map (e.inv ≫ f) := by
    simp only [Ext.mk₀_hom, ShiftedHom.mk₀, commShiftIso_zero,
      CommShift.isoZero_inv_app, Category.assoc]
    simp [shiftFunctorZero', ← Functor.map_comp, e]
  simp only [Function.comp_def, Iso.homFromEquiv_apply, ← he] at hb
  convert hb using 1
end CategoryTheory.Functor
