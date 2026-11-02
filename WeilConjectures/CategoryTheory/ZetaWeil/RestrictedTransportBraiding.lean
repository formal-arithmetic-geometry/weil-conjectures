/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Braiding for coefficient-normalized module inverse images -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
  [HasCoequalizers D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {A : C} [MonObj A] [IsCommMonObj A] {B : D} [MonObj B] [IsCommMonObj B]
  (a : B ⟶ F.obj A) [IsMonHom a] [IsIso a]

end CategoryTheory
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

end CategoryTheory

namespace CategoryTheory

private theorem restricted_tensor_projection (M N : Mod C A) :
    Mod.tensorObjπ ((F.mapMod A ⋙ Mod.comap a).obj M)
        ((F.mapMod A ⋙ Mod.comap a).obj N) ≫
      (Functor.LaxMonoidal.μ (F.mapMod A ⋙ Mod.comap a) M N).hom =
    Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) := by
  simp only [Functor.LaxMonoidal.comp_μ, Mod.comp_hom']
  change Mod.tensorObjπ _ _ ≫ (Mod.comapTensorIso a _ _).hom.hom ≫
    (F.mapModTensorIso M N).hom.hom = _
  rw [Mod.tensorπ_comapTensorIso_hom_hom_assoc]
  exact F.tensorπ_mapModTensorIso_hom_hom M N

end CategoryTheory
