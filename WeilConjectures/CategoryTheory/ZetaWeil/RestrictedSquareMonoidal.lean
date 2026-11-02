/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import all WeilConjectures.CategoryTheory.ZetaWeil.RestrictedTransportBraiding

/-! # Monoidal squares of coefficient-normalized module inverse images -/

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

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [SymmetricCategory E]
  [HasCoequalizers E]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : Type u₄} [Category.{v₄} T] [MonoidalCategory T] [SymmetricCategory T]
  [HasCoequalizers T]
  [∀ X : T, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : T, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (G : D ⥤ T) (H : C ⥤ E) (I : E ⥤ T)
  [G.Braided] [H.Braided] [I.Braided]
  [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape WalkingParallelPair H]
  [PreservesColimitsOfShape WalkingParallelPair I]
  {R : E} [MonObj R] [IsCommMonObj R] {S : T} [MonObj S] [IsCommMonObj S]
  (b : S ⟶ G.obj B) [IsMonHom b] [IsIso b]
  (c : R ⟶ H.obj A) [IsMonHom c] [IsIso c]
  (d : S ⟶ I.obj R) [IsMonHom d] [IsIso d]

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

private theorem double_tensor_projection (M N : Mod C A) :
    let L := (F.mapMod A ⋙ Mod.comap a) ⋙ (G.mapMod B ⋙ Mod.comap b)
    Mod.tensorObjπ (L.obj M) (L.obj N) ≫ (Functor.LaxMonoidal.μ L M N).hom =
      Functor.LaxMonoidal.μ (F ⋙ G) M.X N.X ≫
        (F ⋙ G).map (Mod.tensorObjπ M N) := by
  dsimp only
  simp only [Functor.LaxMonoidal.comp_μ, Mod.comp_hom']
  change Mod.tensorObjπ _ _ ≫
    (Functor.LaxMonoidal.μ (G.mapMod B ⋙ Mod.comap b) _ _).hom ≫
      G.map (Functor.LaxMonoidal.μ (F.mapMod A ⋙ Mod.comap a) M N).hom = _
  erw [reassoc_of% restricted_tensor_projection G b]
  erw [← G.map_comp, restricted_tensor_projection F a]
  simp only [G.map_comp, Category.assoc, Functor.comp_map]
  rfl

/-- A module comparison whose underlying comparison is monoidal preserves balanced tensors
and their units. Source: the coequalizer construction of the relative tensor product.
(blueprint: lem-zl-restricted-module-square-monoidal)

Proof: precompose the tensor equation with the epimorphic balanced tensor projection.
The tensorator of each restricted module transport is the ordinary tensorator followed
by the image of the source projection. Thus the equation reduces to naturality of the
underlying comparison on that projection and its monoidal tensor equation. Invertibility
of the comparison and the tensorators then determine the unit equation. -/
theorem restrictedModuleSquare_monoidal
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [SymmetricCategory E]
    [HasCoequalizers E]
    [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {T : Type u₄} [Category.{v₄} T] [MonoidalCategory T] [SymmetricCategory T]
    [HasCoequalizers T]
    [∀ X : T, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : T, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (F : C ⥤ D) (G : D ⥤ T) (H : C ⥤ E) (I : E ⥤ T)
    [F.Braided] [G.Braided] [H.Braided] [I.Braided]
    [PreservesColimitsOfShape WalkingParallelPair F]
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesColimitsOfShape WalkingParallelPair H]
    [PreservesColimitsOfShape WalkingParallelPair I]
    {A : C} [MonObj A] [IsCommMonObj A] {B : D} [MonObj B] [IsCommMonObj B]
    {R : E} [MonObj R] [IsCommMonObj R] {S : T} [MonObj S] [IsCommMonObj S]
    (a : B ⟶ F.obj A) [IsMonHom a] [IsIso a]
    (b : S ⟶ G.obj B) [IsMonHom b] [IsIso b]
    (c : R ⟶ H.obj A) [IsMonHom c] [IsIso c]
    (d : S ⟶ I.obj R) [IsMonHom d] [IsIso d]
    (e : F ⋙ G ≅ H ⋙ I) [NatTrans.IsMonoidal e.hom]
    (ν : (F.mapMod A ⋙ Mod.comap a) ⋙ (G.mapMod B ⋙ Mod.comap b) ≅
      (H.mapMod A ⋙ Mod.comap c) ⋙ (I.mapMod R ⋙ Mod.comap d))
    (hν : ∀ M, (ν.hom.app M).hom = e.hom.app M.X) :
    NatTrans.IsMonoidal ν.hom := by
  have ht (M N : Mod C A) :
      Functor.LaxMonoidal.μ _ M N ≫ ν.hom.app (M ⊗ N) =
        (ν.hom.app M ⊗ₘ ν.hom.app N) ≫ Functor.LaxMonoidal.μ _ M N := by
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ _ _)]
    simp only [Mod.comp_hom']
    erw [reassoc_of% double_tensor_projection F a G b]
    rw [Mod.tensorObjπ_tensorHom_hom_whisker_assoc]
    erw [double_tensor_projection H c I d]
    rw [hν, hν, hν, ← tensorHom_def_assoc]
    erw [e.hom.naturality, NatTrans.IsMonoidal.tensor_assoc]
  apply monoidal_of_tensor_iso ν
  intro M N
  rw [← cancel_epi (Functor.LaxMonoidal.μ _ M N)]
  rw [← Category.assoc, ht, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Functor.Monoidal.μ_δ_assoc]

end CategoryTheory
