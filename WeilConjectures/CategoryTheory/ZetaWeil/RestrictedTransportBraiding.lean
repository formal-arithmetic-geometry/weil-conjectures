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
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-- Coefficient-normalized transport preserves the usual braiding of module objects.
Source: the braiding formula on balanced tensor projections.
(blueprint: lem-zl-restricted-module-transport-braiding)

Proof: precompose with the balanced tensor projection and use the ordinary braided
functor equation; both tensor comparison projections are the same defining formula. -/
theorem restrictedModuleTransport_braiding
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
    {A : C} [MonObj A] [IsCommMonObj A] {B : D} [MonObj B] [IsCommMonObj B]
    (a : B ⟶ F.obj A) [IsMonHom a] [IsIso a] (M N : Mod C A) :
    Functor.LaxMonoidal.μ (F.mapMod A ⋙ Mod.comap a) M N ≫
      (F.mapMod A ⋙ Mod.comap a).map (β_ M N).hom =
    (β_ ((F.mapMod A ⋙ Mod.comap a).obj M)
      ((F.mapMod A ⋙ Mod.comap a).obj N)).hom ≫
        Functor.LaxMonoidal.μ (F.mapMod A ⋙ Mod.comap a) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ
    ((F.mapMod A ⋙ Mod.comap a).obj M) ((F.mapMod A ⋙ Mod.comap a).obj N))]
  change Mod.tensorObjπ _ _ ≫
      (Functor.LaxMonoidal.μ (F.mapMod A ⋙ Mod.comap a) M N).hom ≫
        F.map (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫
      (β_ ((F.mapMod A ⋙ Mod.comap a).obj M)
        ((F.mapMod A ⋙ Mod.comap a).obj N)).hom.hom ≫
      (Functor.LaxMonoidal.μ (F.mapMod A ⋙ Mod.comap a) N M).hom
  erw [reassoc_of% restricted_tensor_projection F a, ← F.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, F.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    restricted_tensor_projection F a]
  rfl

end CategoryTheory
