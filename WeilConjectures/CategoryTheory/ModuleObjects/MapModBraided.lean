/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-!

# `mapMod` and change of scalars along an isomorphism are braided

Let `C` and `D` be symmetric monoidal categories with coequalizers preserved by tensoring on
either side, so that the module objects over a commutative algebra object carry the symmetric
relative tensor product `⊗_R` (`WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`). The
strong monoidal functors of `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal` are
compatible with these braidings:

* `F.mapMod : Mod C R ⥤ Mod D (F.obj R)` for a braided functor `F : C ⥤ D` preserving
  coequalizers (`Functor.laxBraided_mapMod`);
* `Mod.comap ψ` for an isomorphism `ψ : S ⟶ R` of commutative algebra objects
  (`Mod.laxBraided_comap`);
* `Mod.extendScalars φ` for an isomorphism `φ : R ⟶ S` of commutative algebra objects
  (`Mod.laxBraided_extendScalars`), which is the restriction of scalars along `φ⁻¹`.

In each case the identity is checked after precomposition with the projection
`M ⊗ N ⟶ M ⊗_R N`, where the braiding of `⊗_R` is induced by the braiding of `C`.

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

/-- The transport `F.mapMod` of module objects along a braided functor preserving coequalizers is
braided for the symmetric relative tensor products. -/
noncomputable instance laxBraided_mapMod : (F.mapMod R).LaxBraided where
  braided M N := by
    apply Mod.Hom.ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N))]
    simp only [Mod.comp_hom', mapMod_μ_hom]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc, Mod.tensorObjπ_braidingHomX_assoc,
      tensorπ_mapModTensorIso_hom_hom]
    rw [show ((F.mapMod R).map (β_ M N).hom).hom = F.map (Mod.braidingHomX M N) from rfl,
      ← F.map_comp]
    erw [Mod.tensorObjπ_braidingHomX]
    rw [F.map_comp, LaxBraided.braided_assoc]
    rfl

end Functor

namespace Mod

section Comap

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (ψ : S ⟶ R)
  [IsMonHom ψ] [IsIso ψ]

/-- Restriction of scalars along an isomorphism of commutative algebra objects is braided for the
symmetric relative tensor products. -/
noncomputable instance laxBraided_comap : (comap ψ : Mod C R ⥤ Mod C S).LaxBraided where
  braided M N := by
    apply Mod.Hom.ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N))]
    simp only [comp_hom', comap_map_hom]
    erw [tensorπ_comapTensorIso_hom_hom_assoc, tensorObjπ_braidingHomX_assoc,
      tensorπ_comapTensorIso_hom_hom, tensorObjπ_braidingHomX]
    rfl

end Comap

section ExtendScalars

variable [MonoidalClosed C] [HasEqualizers C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [IsIso φ]

/-- Extension of scalars along an isomorphism of commutative algebra objects is braided for the
symmetric relative tensor products: its monoidal structure is transported from that of the
braided restriction of scalars along `φ⁻¹`. -/
noncomputable instance laxBraided_extendScalars : (extendScalars φ).LaxBraided :=
  have := Functor.Monoidal.natTransIsMonoidal_of_transport (extendScalarsIsoComapInv φ).symm
  Functor.LaxBraided.ofNatIso (extendScalarsIsoComapInv φ).symm

end ExtendScalars

end Mod

end CategoryTheory
