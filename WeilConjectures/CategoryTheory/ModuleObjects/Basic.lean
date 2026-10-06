/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!

# Module objects over a ring object

Let `(C, ⊗, 𝟙)` be a monoidal category and `R : C` an algebra object, i.e. `[MonObj R]`
(see `WeilConjectures.CategoryTheory.RingObjects.Basic`). A *left `R`-module object* is an
object `M : C` with an action `γ : R ⊗ M ⟶ M` which is associative and unital; these are the
instances `[ModObj R M]` of Mathlib, and they form the category `Mod C R`, written
`Mod_R(C)` in the literature. Morphisms are the morphisms `f : M ⟶ N` of `C` with
`γ ≫ f = R ◁ f ≫ γ`.

This file contains the basic API of the forgetful functor `Mod.forget R : Mod C R ⥤ C`:
it is faithful and reflects isomorphisms, and isomorphisms of module objects can be built from
isomorphisms of the underlying objects compatible with the actions.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {R : C} [MonObj R]

@[reassoc (attr := simp)]
lemma smul_hom {M N : Mod C R} (f : M ⟶ N) : γ[R,M.X] ≫ f.hom = R ◁ f.hom ≫ γ[R,N.X] :=
  IsModHom.smul_hom

@[reassoc (attr := simp)]
lemma one_smul (M : Mod C R) : η[R] ▷ M.X ≫ γ[R,M.X] = (λ_ M.X).hom :=
  ModObj.one_smul_self R M.X

@[reassoc]
lemma mul_smul (M : Mod C R) :
    μ[R] ▷ M.X ≫ γ[R,M.X] = (α_ R R M.X).hom ≫ R ◁ γ[R,M.X] ≫ γ[R,M.X] :=
  ModObj.mul_smul_self R M.X

variable (C R) in
instance : (forget R : Mod C R ⥤ C).Faithful where
  map_injective h := hom_ext _ _ h

/-- Construct an isomorphism of module objects from an isomorphism of the underlying objects
which is compatible with the actions. -/
@[simps]
def isoMk {M N : Mod C R} (e : M.X ≅ N.X)
    (he : γ[R,M.X] ≫ e.hom = R ◁ e.hom ≫ γ[R,N.X] := by cat_disch) : M ≅ N where
  hom := Hom.mk' e.hom he
  inv := Hom.mk' e.inv (by
    change γ[R,N.X] ≫ e.inv = R ◁ e.inv ≫ γ[R,M.X]
    rw [Iso.comp_inv_eq, Category.assoc, he, ← whiskerLeft_comp_assoc, e.inv_hom_id,
      whiskerLeft_id, Category.id_comp])
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

variable (C R) in
instance : (forget R : Mod C R ⥤ C).ReflectsIsomorphisms where
  reflects {M N} f (_ : IsIso f.hom) :=
    (isoMk (asIso f.hom) (by simp)).isIso_hom

end CategoryTheory.Mod
