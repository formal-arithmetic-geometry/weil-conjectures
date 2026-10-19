/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.CategoryTheory.ScalarObjects
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Module sheaves as scalar objects in abelian sheaves

Source: Stacks Project, Tag 04JQ, transport of module structures.
(blueprint: lem-exc-scalar-module-sheaves)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w r

open CategoryTheory Opposite

namespace CategoryTheory.ScalarObject

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]

/-- Forget only the scalar action on a sheaf of modules. -/
def moduleSheafToScalar : Sheaf J (ModuleCat.{max u v w} R) ⥤
    ScalarObject R (Sheaf J AddCommGrpCat.{max u v w}) where
  obj F :=
    { X := (sheafCompose J (forget₂ (ModuleCat R) AddCommGrpCat)).obj F
      ρ :=
        { toFun := fun a ↦ ⟨
            { app := fun U ↦ (F.obj.obj U).smul a
              naturality := fun U V f ↦ ModuleCat.smul_naturality (F.obj.map f) a }⟩
          map_one' := by
            apply ObjectProperty.hom_ext
            apply NatTrans.ext
            funext U
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            exact one_smul R (show F.obj.obj U from x)
          map_mul' a b := by
            apply ObjectProperty.hom_ext
            apply NatTrans.ext
            funext U
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            exact mul_smul a b (show F.obj.obj U from x)
          map_zero' := by
            apply ObjectProperty.hom_ext
            apply NatTrans.ext
            funext U
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            exact zero_smul R (show F.obj.obj U from x)
          map_add' a b := by
            apply ObjectProperty.hom_ext
            apply NatTrans.ext
            funext U
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            exact add_smul a b (show F.obj.obj U from x) } }
  map f :=
    { hom := (sheafCompose J (forget₂ (ModuleCat R) AddCommGrpCat)).map f
      comm := fun a ↦ by
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        exact (f.hom.app U).hom.map_smul a x }
  map_id F := hom_ext rfl
  map_comp f g := hom_ext rfl

/-- Evaluate a scalar object as a module at each object of the site. -/
def scalarToModulePresheaf (F : ScalarObject R (Sheaf J AddCommGrpCat.{max u v w})) :
    Cᵒᵖ ⥤ ModuleCat.{max u v w} R where
  obj U := ModuleCat.mkOfSMul ((mapEndRing
    ((sheafToPresheaf J AddCommGrpCat) ⋙ (evaluation _ _).obj U) F.X).comp F.ρ)
  map {U V} f := ModuleCat.ofHom
    { toFun := F.X.obj.map f
      map_add' := map_add _
      map_smul' := fun a x ↦ (ConcreteCategory.congr_hom ((F.ρ a).hom.naturality f) x).symm }
  map_id U := by ext x; exact ConcreteCategory.congr_hom (F.X.obj.map_id U) x
  map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.X.obj.map_comp f g) x

/-- The underlying abelian presheaf is unchanged, so it remains a sheaf. -/
def scalarToModuleSheaf : ScalarObject R (Sheaf J AddCommGrpCat.{max u v w}) ⥤
    Sheaf J (ModuleCat.{max u v w} R) where
  obj F := ⟨scalarToModulePresheaf J R F, by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ (ModuleCat R) AddCommGrpCat)
    exact F.X.property⟩
  map f := ⟨
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := f.hom.hom.app U
          map_add' := map_add _
          map_smul' := fun a x ↦
            ConcreteCategory.congr_hom (congrArg (fun t ↦ t.hom.app U) (f.comm a)) x }
      naturality := fun U V h ↦ by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.hom.naturality h) x }⟩
  map_id F := by ext U x; rfl
  map_comp f g := by ext U x; rfl

/-- Giving scalar operations in abelian sheaves is equivalent to giving module sheaves.
The two constructions retain sections and restrictions. The identity section maps give
both natural inverse isomorphisms. Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-module-sheaves) -/
noncomputable def moduleSheafEquivalence : Sheaf J (ModuleCat.{max u v w} R) ≌
    ScalarObject R (Sheaf J AddCommGrpCat.{max u v w}) where
  functor := moduleSheafToScalar J R
  inverse := scalarToModuleSheaf J R
  unitIso := NatIso.ofComponents (fun F ↦
    { hom := ⟨{ app := fun U ↦ ModuleCat.ofHom
                  { toFun := id
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := fun _ _ ↦ rfl }
                naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{ app := fun U ↦ ModuleCat.ofHom
                  { toFun := id
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := fun _ _ ↦ rfl }
                naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (by intros; ext U x; rfl)
  counitIso := NatIso.ofComponents (fun F ↦
    { hom := ⟨⟨{ app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
                , naturality := fun _ _ _ ↦ rfl }⟩, fun _ ↦ by ext U x; rfl⟩
      inv := ⟨⟨{ app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
                , naturality := fun _ _ _ ↦ rfl }⟩, fun _ ↦ by ext U x; rfl⟩
      hom_inv_id := hom_ext (by ext U x; rfl)
      inv_hom_id := hom_ext (by ext U x; rfl) }) (by intros; apply hom_ext; ext U x; rfl)
  functor_unitIso_comp F := hom_ext (by ext U x; rfl)

end CategoryTheory.ScalarObject
