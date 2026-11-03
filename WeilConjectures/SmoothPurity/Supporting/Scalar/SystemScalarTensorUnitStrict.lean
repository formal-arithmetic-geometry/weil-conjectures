/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Yoneda

/-! # Extension of scalars of the unit sheaf of modules

For a morphism of sheaves of rings `α : R ⟶ R'` and any left adjoint `F` of the restriction
of scalars along `α`, the transpose of the ring map `unit R ⟶ α_* (unit R')` is an
isomorphism `F (unit R) ≅ unit R'`: both corepresent global sections.
Source: Stacks Project, Tag 03EL (extension of scalars of the structure sheaf).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w c v

open CategoryTheory

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R')

/-- The ring map `α`, as a morphism of sheaves of `R`-modules from the unit to the
restriction of scalars of the unit. -/
def unitToRestrictScalarsUnit :
    unit R ⟶ (restrictScalars α).obj (unit R') where
  val.app X := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (α.hom.app X)) (fun r ↦ by
    ext m
    exact ((α.hom.app X).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (α.hom.naturality f) _

lemma unitToRestrictScalarsUnit_val_app_apply {X : Cᵒᵖ} (a : R.obj.obj X) :
    (unitToRestrictScalarsUnit α).val.app X a = α.hom.app X a := rfl

/-- Global sections of a restriction of scalars are the global sections. -/
def restrictScalarsSectionsEquiv (M : SheafOfModules.{w} R') :
    ((restrictScalars α).obj M).sections ≃ M.sections where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma restrictScalarsSectionsEquiv_unitHomEquiv {M : SheafOfModules.{w} R'}
    (f : unit R' ⟶ M) :
    restrictScalarsSectionsEquiv α M (((restrictScalars α).obj M).unitHomEquiv
      (unitToRestrictScalarsUnit α ≫ (restrictScalars α).map f)) = M.unitHomEquiv f := by
  ext X
  change f.val.app X (α.hom.app X (1 : R.obj.obj X)) = f.val.app X (1 : R'.obj.obj X)
  rw [map_one]

/-- The transpose of `unitToRestrictScalarsUnit` along any adjunction is an isomorphism. -/
theorem isIso_unitToRestrictScalarsUnit_transpose
    {F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} R'} (adj : F ⊣ restrictScalars α) :
    IsIso ((adj.homEquiv _ _).symm (unitToRestrictScalarsUnit α)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← (adj.homEquiv _ _).bijective.of_comp_iff',
    ← (unitHomEquiv _).bijective.of_comp_iff',
    ← (restrictScalarsSectionsEquiv α M).bijective.of_comp_iff']
  convert (unitHomEquiv M).bijective using 1
  ext f : 1
  dsimp
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    restrictScalarsSectionsEquiv_unitHomEquiv]

lemma iso_hom_inv_val_app_apply {M N : SheafOfModules.{w} R} (e : M ≅ N) (X : Cᵒᵖ)
    (x : N.val.obj X) : e.hom.val.app X (e.inv.val.app X x) = x := by
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← comp_val, e.inv_hom_id]
  rfl

lemma iso_inv_hom_val_app_apply {M N : SheafOfModules.{w} R} (e : M ≅ N) (X : Cᵒᵖ)
    (x : M.val.obj X) : e.inv.val.app X (e.hom.val.app X x) = x := by
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← comp_val, e.hom_inv_id]
  rfl

end SheafOfModules
