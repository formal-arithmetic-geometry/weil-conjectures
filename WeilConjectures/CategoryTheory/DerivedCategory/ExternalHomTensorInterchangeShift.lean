/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.BraidingShift

/-!
# The middle-four interchange commutes with the signed derived shifts

Source: the evaluation transpose in sk-def-sf-kv-maps (iii), used in
lem-sf-kv-exact-comparisons, Step 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory

universe u v w

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]

attribute [local instance] braidedCategory'

/-- Middle-four interchange, natural in the first Hom factor. Source:
sk-def-sf-kv-maps (iii) (blueprint: lem-sf-external-hom-tensor-interchange-shifts). -/
def tensorInterchangeFirst (A B V : DerivedCategory C) :
    tensorRight V ⋙ tensorLeft (A ⊗ B) ⟶ tensorLeft A ⋙ tensorRight (B ⊗ V) where
  app U := tensorμ A B U V
  naturality U U' f := by
    simpa using tensorμ_natural_right A B f (𝟙 V)

private def braidFirst (B : DerivedCategory C) : tensorLeft B ⟶ tensorRight B :=
  (curriedBraidingNatIso _).hom.app B

private theorem braidFirst_shift (B : DerivedCategory C) :
    NatTrans.CommShift (braidFirst B) ℤ := by
  constructor
  intro n
  ext U
  exact (braiding_hom_commShiftIso_hom_app B U n).symm

set_option maxHeartbeats 1000000 in
-- Elaborating the native tensor structures in the pasted shift square is expensive.
set_option synthInstance.maxHeartbeats 200000 in
-- Instance inference expands the native derived tensor structures.
/-- Associator and braiding shift squares paste to give the interchange square.
Source: evaluation in sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-tensor-interchange-shifts). -/
theorem tensorInterchangeFirst_commShift (A B V : DerivedCategory C) :
    NatTrans.CommShift (tensorInterchangeFirst A B V) ℤ := by
  let D := DerivedCategory C
  have : ∀ U : D, IsIso ((associatorNatTrans₂ D B V).app U) := by
    intro U
    change IsIso (α_ B U V).hom
    infer_instance
  have : ∀ U : D, IsIso ((associatorNatTrans₂ D A (B ⊗ V)).app U) := by
    intro U
    change IsIso (α_ A U (B ⊗ V)).hom
    infer_instance
  have h₂ : IsIso (associatorNatTrans₂ D B V) := NatIso.isIso_of_isIso_app _
  have h₃ : IsIso (associatorNatTrans₂ D A (B ⊗ V)) := NatIso.isIso_of_isIso_app _
  have := braidFirst_shift B
  have : NatTrans.CommShift (inv (associatorNatTrans₂ D B V)) ℤ :=
    NatTrans.CommShift.of_isIso _ ℤ
  have : NatTrans.CommShift (inv (associatorNatTrans₂ D A (B ⊗ V))) ℤ :=
    NatTrans.CommShift.of_isIso _ ℤ
  let τ : tensorRight V ⋙ tensorLeft (A ⊗ B) ⟶
      tensorLeft A ⋙ tensorRight (B ⊗ V) :=
    Functor.whiskerLeft (tensorRight V) (associatorNatTrans₃ D A B) ≫
      (Functor.associator (tensorRight V) (tensorLeft B) (tensorLeft A)).inv ≫
      Functor.whiskerRight
        (inv (associatorNatTrans₂ D B V) ≫
          Functor.whiskerRight (braidFirst B) (tensorRight V) ≫
          associatorNatTrans₁ D B V) (tensorLeft A) ≫
      inv (associatorNatTrans₂ D A (B ⊗ V))
  have hτ : NatTrans.CommShift τ ℤ := by
    dsimp only [τ]
    infer_instance
  have he : tensorInterchangeFirst A B V = τ := by
    ext U
    simp only [tensorInterchangeFirst, τ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, NatIso.isIso_inv_app,
      associatorNatTrans₁_app, associatorNatTrans₂_app, associatorNatTrans₃_app,
      tensorLeft, tensorRight, Functor.flip_obj_map, curriedTensor_obj_map,
      curriedTensor_map_app, braidFirst, curriedBraidingNatIso_hom_app_app]
    simp only [tensorμ, IsIso.Iso.inv_hom, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    erw [Category.id_comp]
    rfl
  rw [he]
  exact hτ

/-- Middle-four interchange, natural in the second Hom factor. Source:
sk-def-sf-kv-maps (iii) (blueprint: lem-sf-external-hom-tensor-interchange-shifts). -/
def tensorInterchangeSecond (A B U : DerivedCategory C) :
    tensorLeft U ⋙ tensorLeft (A ⊗ B) ⟶ tensorLeft B ⋙ tensorLeft (A ⊗ U) where
  app V := tensorμ A B U V
  naturality V V' f := by
    simpa using tensorμ_natural_right A B (𝟙 U) f

set_option maxHeartbeats 1000000 in
-- Elaborating the native tensor structures in the pasted shift square is expensive.
set_option synthInstance.maxHeartbeats 200000 in
-- Instance inference expands the native derived tensor structures.
/-- The second Hom factor uses only the associator shift squares and the fixed
braiding between B and U. Source: evaluation in sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-tensor-interchange-shifts). -/
theorem tensorInterchangeSecond_commShift (A B U : DerivedCategory C) :
    NatTrans.CommShift (tensorInterchangeSecond A B U) ℤ := by
  let D := DerivedCategory C
  have : ∀ V : D, IsIso ((associatorNatTrans₃ D B U).app V) := by
    intro V
    change IsIso (α_ B U V).hom
    infer_instance
  have : ∀ V : D, IsIso ((associatorNatTrans₃ D A U).app V) := by
    intro V
    change IsIso (α_ A U V).hom
    infer_instance
  have : IsIso (associatorNatTrans₃ D B U) := NatIso.isIso_of_isIso_app _
  have : IsIso (associatorNatTrans₃ D A U) := NatIso.isIso_of_isIso_app _
  have : NatTrans.CommShift (inv (associatorNatTrans₃ D B U)) ℤ :=
    NatTrans.CommShift.of_isIso _ ℤ
  have : NatTrans.CommShift (inv (associatorNatTrans₃ D A U)) ℤ :=
    NatTrans.CommShift.of_isIso _ ℤ
  let τ : tensorLeft U ⋙ tensorLeft (A ⊗ B) ⟶ tensorLeft B ⋙ tensorLeft (A ⊗ U) :=
    Functor.whiskerLeft (tensorLeft U) (associatorNatTrans₃ D A B) ≫
      (Functor.associator (tensorLeft U) (tensorLeft B) (tensorLeft A)).inv ≫
      Functor.whiskerRight
        (inv (associatorNatTrans₃ D B U) ≫
          (curriedTensor D).map (β_ B U).hom ≫ associatorNatTrans₃ D U B)
        (tensorLeft A) ≫
      (Functor.associator (tensorLeft B) (tensorLeft U) (tensorLeft A)).hom ≫
      Functor.whiskerLeft (tensorLeft B) (inv (associatorNatTrans₃ D A U))
  have hτ : NatTrans.CommShift τ ℤ := by dsimp only [τ]; infer_instance
  have he : tensorInterchangeSecond A B U = τ := by
    ext V
    simp only [tensorInterchangeSecond, τ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      NatIso.isIso_inv_app, associatorNatTrans₃_app, curriedTensor_map_app, tensorμ,
      IsIso.Iso.inv_hom]
    erw [Category.id_comp, Category.id_comp]
    simp only [tensorLeft, curriedTensor_obj_map, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rfl
  rw [he]
  exact hτ

end DerivedCategory
