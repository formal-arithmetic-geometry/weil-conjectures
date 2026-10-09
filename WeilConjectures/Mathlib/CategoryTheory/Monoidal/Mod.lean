/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Module objects over a monoid object acting on its own category

For a monoid object `A` of a monoidal category `C`, acting on `C` through the tensor product,
this file records the action `A ⊗ X ⟶ X` of an `A`-module object `X` and its axioms in terms of
the tensor product (`CategoryTheory.Mod.act`), and the basic properties of the forgetful functor
`Mod.forget A : Mod C A ⥤ C`: it is faithful and reflects isomorphisms.

It also provides the image of a module object under a lax monoidal functor
(`CategoryTheory.Functor.mapMod`), which mathlib lists as a TODO in
`Mathlib.CategoryTheory.Monoidal.Mon`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

namespace Mod

variable {A : C} [MonObj A]

/-- The action `A ⊗ X ⟶ X` of a monoid object `A` on an `A`-module object `X` of `C`. -/
abbrev act (X : C) [ModObj A X] : A ⊗ X ⟶ X :=
  γ[A, X]

@[reassoc (attr := simp)]
lemma one_act (X : C) [ModObj A X] : η[A] ▷ X ≫ act X = (λ_ X).hom :=
  ModObj.one_smul (M := A) X

@[reassoc (attr := simp)]
lemma mul_act (X : C) [ModObj A X] :
    μ[A] ▷ X ≫ act X = (α_ A A X).hom ≫ A ◁ act X ≫ act X :=
  ModObj.mul_smul (M := A) X

@[reassoc]
lemma act_comp {X Y : C} [ModObj A X] [ModObj A Y] (f : X ⟶ Y) [IsModHom A f] :
    act X ≫ f = A ◁ f ≫ act Y :=
  IsModHom.smul_hom

@[reassoc (attr := simp)]
lemma act_hom {M N : Mod C A} (f : M ⟶ N) : act M.X ≫ f.hom = A ◁ f.hom ≫ act N.X :=
  IsModHom.smul_hom

variable (A) in
/-- An `A`-module structure on an object of `C`, from an action `A ⊗ X ⟶ X` satisfying the
axioms, stated in terms of the tensor product. -/
@[implicit_reducible]
def _root_.CategoryTheory.ModObj.mk' {X : C} (smul : A ⊗ X ⟶ X)
    (one_smul : η[A] ▷ X ≫ smul = (λ_ X).hom)
    (mul_smul : μ[A] ▷ X ≫ smul = (α_ A A X).hom ≫ A ◁ smul ≫ smul) : ModObj A X where
  smul := smul
  one_smul := one_smul
  mul_smul := mul_smul

lemma isModHom_of_act {X Y : C} [ModObj A X] [ModObj A Y] (f : X ⟶ Y)
    (h : act X ≫ f = A ◁ f ≫ act Y) : IsModHom A f :=
  ⟨h⟩

/-- A morphism of `A`-modules from a morphism commuting with the actions. -/
@[simps]
def homMk {M N : Mod C A} (f : M.X ⟶ N.X) (h : act M.X ≫ f = A ◁ f ≫ act N.X) : M ⟶ N :=
  letI := isModHom_of_act f h
  ⟨f⟩

instance : (forget (D := C) A).Faithful where
  map_injective h := Mod.hom_ext _ _ h

instance {M N : Mod C A} (f : M ⟶ N) [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget A).map f))

instance : (forget (D := C) A).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have : IsIso f.hom := ‹IsIso ((forget A).map f)›
    let e : M.X ≅ N.X := asIso f.hom
    have : IsModHom A e.hom := inferInstanceAs (IsModHom A f.hom)
    exact ⟨⟨⟨e.inv⟩, Mod.hom_ext _ _ e.hom_inv_id, Mod.hom_ext _ _ e.inv_hom_id⟩⟩

/-- An isomorphism of `A`-modules from an isomorphism commuting with the actions. -/
@[simps!]
def isoMk {M N : Mod C A} (e : M.X ≅ N.X) (h : act M.X ≫ e.hom = A ◁ e.hom ≫ act N.X) :
    M ≅ N where
  hom := homMk e.hom h
  inv := homMk e.inv (by
    rw [Iso.comp_inv_eq, Category.assoc, h, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
  inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id

end Mod

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

open LaxMonoidal _root_.CategoryTheory.Mod

open scoped Obj

variable {A : C} [MonObj A]

/-- The image of an `A`-module object under a lax monoidal functor `F` is an `F A`-module
object, with the action `F A ⊗ F X ⟶ F (A ⊗ X) ⟶ F X`. -/
@[implicit_reducible]
def modObjObj (X : C) [ModObj A X] : ModObj (F.obj A) (F.obj X) :=
  .mk' _ (LaxMonoidal.μ F A X ≫ F.map (act X))
    (by
      rw [obj.η_def, comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
        ← F.map_comp, one_act, left_unitality])
    (by
      rw [obj.μ_def, comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
        mul_act, F.map_comp, F.map_comp]
      simp only [associativity_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        μ_natural_right_assoc])

variable (A) in
/-- A lax monoidal functor `F : C ⥤ D` takes `A`-module objects to `F A`-module objects. -/
@[simps]
def mapMod : Mod C A ⥤ Mod D (F.obj A) where
  obj M :=
    letI := F.modObjObj (A := A) M.X
    ⟨F.obj M.X⟩
  map {M N} f :=
    letI := F.modObjObj (A := A) M.X
    letI := F.modObjObj (A := A) N.X
    homMk (F.map f.hom) (by
      change (LaxMonoidal.μ F A M.X ≫ F.map (act M.X)) ≫ _ = _ ≫ LaxMonoidal.μ F A N.X ≫ F.map (act N.X)
      rw [Category.assoc, ← F.map_comp, act_hom, F.map_comp, μ_natural_right_assoc])

end Functor

end CategoryTheory
