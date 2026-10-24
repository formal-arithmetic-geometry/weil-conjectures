/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric

/-!
# Transport and change of scalars of module objects are braided

Let `C` and `D` be symmetric monoidal categories whose tensor products preserve colimits, so that
module objects over commutative algebra objects carry the symmetric relative tensor product
(`CategoryTheory.Mod.braidedCategory`). Then:

* the transport `F.mapMod R` of module objects along a braided functor `F` preserving
  coequalizers is braided (`CategoryTheory.Functor.laxBraided_mapMod`);
* restriction of scalars along an isomorphism of commutative algebra objects is braided
  (`CategoryTheory.Mod.laxBraided_comap`);
* extension of scalars along an isomorphism of commutative algebra objects is braided
  (`CategoryTheory.Mod.laxBraided_extendScalars`).

In each case the tensorator is induced by that of `C` on the projections
`M ⊗ N ⟶ M ⊗_R N`, as is the braiding, so the braided axiom is checked after precomposing
with these projections.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

open scoped Obj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The transport `F.mapMod R` of module objects along a braided functor is braided. -/
noncomputable instance laxBraided_mapMod : (F.mapMod R).LaxBraided where
  braided M N := by
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N))]
    change _ ≫ (LaxMonoidal.μ (F.mapMod R) M N).hom ≫ F.map (Mod.braidingHomX M N) =
      _ ≫ Mod.braidingHomX ((F.mapMod R).obj M) ((F.mapMod R).obj N) ≫
        (LaxMonoidal.μ (F.mapMod R) N M).hom
    rw [mapMod_μ_hom, mapMod_μ_hom, ← mapModTensorIso_hom_hom, ← mapModTensorIso_hom_hom,
      tensorπ_mapModTensorIso_hom_hom_assoc, ← F.map_comp, Mod.tensorObjπ_braidingHomX,
      Mod.tensorObjπ_braidingHomX_assoc, tensorπ_mapModTensorIso_hom_hom, F.map_comp]
    exact LaxBraided.braided_assoc (F := F) M.X N.X _

noncomputable instance braided_mapMod : (F.mapMod R).Braided where

end Functor

namespace Mod

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (ψ : S ⟶ R)
  [IsMonHom ψ] [IsIso ψ]

/-- Restriction of scalars along an isomorphism of commutative algebra objects is braided. -/
noncomputable instance laxBraided_comap : (comap ψ : Mod C R ⥤ Mod C S).LaxBraided where
  braided M N := by
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N))]
    change _ ≫ (comapTensorIso ψ M N).hom.hom ≫ braidingHomX M N =
      _ ≫ braidingHomX ((comap ψ).obj M) ((comap ψ).obj N) ≫ (comapTensorIso ψ N M).hom.hom
    rw [tensorπ_comapTensorIso_hom_hom_assoc, tensorObjπ_braidingHomX,
      tensorObjπ_braidingHomX_assoc, tensorπ_comapTensorIso_hom_hom]
    rfl

noncomputable instance braided_comap : (comap ψ : Mod C R ⥤ Mod C S).Braided where

section ExtendScalars

variable [MonoidalClosed C] [HasEqualizers C] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

/-- Extension of scalars along an isomorphism of commutative algebra objects is braided: its
monoidal structure is transported from restriction of scalars along the inverse, which is
braided. -/
noncomputable instance laxBraided_extendScalars : (extendScalars φ).LaxBraided where
  braided M N := by
    have hμ (X Y : Mod C R) : Functor.LaxMonoidal.μ (extendScalars φ) X Y =
        ((extendScalarsIsoComapInv φ).symm.inv.app X ⊗ₘ
          (extendScalarsIsoComapInv φ).symm.inv.app Y) ≫
        Functor.LaxMonoidal.μ (comap (asIso φ).inv) X Y ≫
        (extendScalarsIsoComapInv φ).symm.hom.app (X ⊗ Y) :=
      Functor.Monoidal.transport_μ _ X Y
    have hn := (extendScalarsIsoComapInv φ).symm.hom.naturality (β_ M N).hom
    rw [hμ, hμ]
    simp only [Category.assoc]
    rw [← hn, Functor.LaxBraided.braided_assoc, ← BraidedCategory.braiding_naturality_assoc]

noncomputable instance braided_extendScalars : (extendScalars φ).Braided where

end ExtendScalars


end Mod

end CategoryTheory
