/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Basic

/-!

# Global sections of ring objects under lax monoidal functors

A lax monoidal functor `F : C ⥤ D` sends an algebra object `R` to the algebra object `F R`
(`Functor.monObjObj`), and a global section `s : 𝟙 ⟶ R` to the global section
`ε ≫ F s : 𝟙 ⟶ F R`. This is a monoid homomorphism `Γ R →* Γ (F R)`, and a ring homomorphism
when `F` is additive (`MonObj.Γ.mapFunctor`).

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Functor.LaxMonoidal

open scoped Obj

namespace CategoryTheory.MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] {R : C} [MonObj R]

/-- A lax monoidal functor induces a monoid homomorphism on global sections. -/
def Γ.mapFunctorMonoidHom : Γ R →* Γ (F.obj R) where
  toFun s := Γ.ofHom (ε F ≫ F.map s.hom)
  map_one' := by ext; simp
  map_mul' s t := by
    have h : ε F ≫ F.map (λ_ (𝟙_ C)).inv = (λ_ (𝟙_ D)).inv ≫ (ε F ⊗ₘ ε F) ≫
        Functor.LaxMonoidal.μ F _ _ := by
      rw [tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc, left_unitality_inv]
    ext
    simp only [Γ.hom_ofHom, Γ.mul_hom, F.map_comp, Functor.obj.μ_def]
    rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, reassoc_of% h]

@[simp]
lemma Γ.mapFunctorMonoidHom_hom (s : Γ R) :
    (Γ.mapFunctorMonoidHom F s).hom = ε F ≫ F.map s.hom :=
  rfl

variable [Preadditive C] [MonoidalPreadditive C] [Preadditive D] [MonoidalPreadditive D]
  [F.Additive]

/-- A lax monoidal additive functor induces a ring homomorphism on global sections. -/
def Γ.mapFunctor : Γ R →+* Γ (F.obj R) where
  __ := Γ.mapFunctorMonoidHom F
  map_zero' := by ext; simp [Γ.mapFunctorMonoidHom]
  map_add' s t := by ext; simp [Γ.mapFunctorMonoidHom]

@[simp]
lemma Γ.mapFunctor_hom (s : Γ R) : (Γ.mapFunctor F s).hom = ε F ≫ F.map s.hom :=
  rfl

end CategoryTheory.MonObj
