/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryOpenModuleIdentity
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Identity normalization for ordinary open exchange

Source: Stacks Project, Tags 03DI, 07A7 and 099N; the identity part of
proof step 7 of `thm-cbc-complete-proetale`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits

private theorem idFactors
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have h₁ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ := rfl
  have h₃ : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [h₁, h₂, h₃] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at h
  exact h

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] cbcDatumOrdinaryTransport AdicCoefficientDatum.pullId
  cbcModulePullId cbcOpenShriek cbcUnderivedInverseExchange cbcDerivedInverseExchange

attribute [local irreducible] cbcOrdinaryExchange
  cbcDatumOrdinaryExchange

end AlgebraicGeometry.Scheme
