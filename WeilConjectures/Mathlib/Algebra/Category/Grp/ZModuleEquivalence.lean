/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# Abelian groups as `ℤ`-modules

The functor `AddCommGrpCat.toModuleCatInt : AddCommGrpCat ⥤ ModuleCat ℤ` regards an abelian group
as a `ℤ`-module. It is right adjoint to the forgetful functor
(`ModuleCat.forget₂AddCommGrpToModuleCatIntAdj`).
-/

@[expose] public section

universe u

open CategoryTheory

/-- An abelian group regarded as a `ℤ`-module. -/
@[simps]
def AddCommGrpCat.toModuleCatInt : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

/-- The forgetful functor from `ℤ`-modules to abelian groups is left adjoint to regarding an
abelian group as a `ℤ`-module. -/
def ModuleCat.forget₂AddCommGrpToModuleCatIntAdj :
    forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} ⊣ AddCommGrpCat.toModuleCatInt :=
  Adjunction.mkOfHomEquiv
    { homEquiv M A :=
        { toFun f := ModuleCat.ofHom
            { toFun := f
              map_add' := map_add f.hom
              map_smul' n x := by
                convert! map_zsmul f.hom n x
                ext
                apply int_smul_eq_zsmul }
          invFun g := AddCommGrpCat.ofHom g.hom.toAddMonoidHom
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }
