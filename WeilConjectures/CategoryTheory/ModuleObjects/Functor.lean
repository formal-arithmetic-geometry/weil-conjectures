/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Basic

/-!

# Module objects under lax monoidal functors

A lax monoidal functor `F : C ⥤ D` sends an algebra object `R` of `C` to the algebra object
`F R` of `D` (`Functor.monObjObj`), and an `R`-module object `M` to the `F R`-module object
`F M`, with action `F R ⊗ F M ⟶ F (R ⊗ M) ⟶ F M`. This gives the functor
`Functor.mapMod F R : Mod C R ⥤ Mod D (F.obj R)`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Functor.LaxMonoidal

open scoped Obj

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R]

/-- The image of a module object under a lax monoidal functor is a module object. -/
abbrev modObjObj (M : C) [ModObj R M] : ModObj (F.obj R) (F.obj M) where
  smul := LaxMonoidal.μ F R M ≫ F.map γ[R,M]
  one_smul := by
    change (LaxMonoidal.ε F ≫ F.map η[R]) ▷ F.obj M ≫ LaxMonoidal.μ F R M ≫ F.map γ[R,M] =
      (λ_ (F.obj M)).hom
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
      ModObj.one_smul_self, left_unitality]
  mul_smul := by
    change (LaxMonoidal.μ F R R ≫ F.map μ[R]) ▷ F.obj M ≫ LaxMonoidal.μ F R M ≫ F.map γ[R,M] =
      (α_ (F.obj R) (F.obj R) (F.obj M)).hom ≫ F.obj R ◁ (LaxMonoidal.μ F R M ≫ F.map γ[R,M]) ≫
        LaxMonoidal.μ F R M ≫ F.map γ[R,M]
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
      ModObj.mul_smul_self, F.map_comp, F.map_comp, associativity_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc, ← F.map_comp]

/-- A lax monoidal functor `F : C ⥤ D` sends `R`-module objects to `F R`-module objects. -/
@[simps]
def mapMod : Mod C R ⥤ Mod D (F.obj R) where
  obj M :=
    letI := F.modObjObj R M.X
    ⟨F.obj M.X⟩
  map {M N} f :=
    letI := F.modObjObj R M.X
    letI := F.modObjObj R N.X
    Mod.Hom.mk'' (F.map f.hom) (by
      change (LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X]) ≫ F.map f.hom =
        F.obj R ◁ F.map f.hom ≫ LaxMonoidal.μ F R N.X ≫ F.map γ[R,N.X]
      rw [Category.assoc, ← F.map_comp, Mod.smul_hom, F.map_comp, μ_natural_right_assoc])
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

lemma mapMod_obj_smul (M : Mod C R) :
    γ[F.obj R,((F.mapMod R).obj M).X] = LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] :=
  rfl

end CategoryTheory.Functor
