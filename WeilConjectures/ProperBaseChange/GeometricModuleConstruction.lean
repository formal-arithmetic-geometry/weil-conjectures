/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Constructing module functors through a geometric morphism

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3 and 03D7.
(blueprint: lem-weil-pbc-geometric-module-construction).
-/

@[expose] public section

universe u uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace GeometricConstruction

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]

private noncomputable abbrev base (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev rset (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R

private noncomputable abbrev mset (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (base R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private noncomputable def action (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (base R)) : rset R ⊗ (mset R).obj M ⟶ (mset R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance x.1 x.2)
     naturality := by
       intro U W f
       ext x
       exact (M.val.map_smul f x.1 x.2).symm }⟩

private noncomputable def addition (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (base R)) : (mset R).obj M ⊗ (mset R).obj M ⟶
      (mset R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (M.val.obj W) inferInstance x.1 x.2)
     naturality := by intro U W f; ext x; exact ((M.val.map f).hom.map_add _ _).symm }⟩

private noncomputable def ringAdd (R : Sheaf J CommRingCat.{u}) :
    rset R ⊗ rset R ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (R.obj.obj W) inferInstance x.1 x.2)
     naturality := by intro U W f; ext x; exact ((R.obj.map f).hom.map_add _ _).symm }⟩

private noncomputable def ringMul (R : Sheaf J CommRingCat.{u}) :
    rset R ⊗ rset R ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Mul.mul (R.obj.obj W) inferInstance x.1 x.2)
     naturality := by intro U W f; ext x; exact ((R.obj.map f).hom.map_mul _ _).symm }⟩

private noncomputable def ringOne (R : Sheaf J CommRingCat.{u}) :
    𝟙_ (Sheaf J (Type u)) ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
     naturality := by intro U W f; ext x; exact (R.obj.map f).hom.map_one.symm }⟩

attribute [local instance] productExists

private noncomputable def fromProd
    {E : Type uE} [Category.{vE} E]
    {T : GrothendieckTopology E}
    (X Y : Sheaf T (Type u)) : X ⨯ Y ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift prod.fst prod.snd

end GeometricConstruction

open GeometricConstruction

-- Keep the pre-existing named nondependent forall binder `hRing` unchanged.
-- The statement records every operation and its underlying comparison.
end SheafOfModules
