/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Additive functors on morphisms between finite powers of an object

Let `F : C ⥤ D` be an additive functor and `e : F P ≅ Q`. Then `F (Pᵐ) ≅ Qᵐ`
(`CategoryTheory.Functor.mapBiproductPowIso`), and the image under `F` of a morphism
`φ : Pᵐ ⟶ Pⁿ`, transported along these isomorphisms, has the components `e⁻¹ ≫ F φᵢⱼ ≫ e`
(`CategoryTheory.Functor.ι_mapBiproductPowIso_inv_map_hom_π`).

If moreover `F` and an additive functor `c : E ⥤ D` preserve cokernels, and `e : F P ≅ c K`
identifies the components of `φ` with the images under `c` of endomorphisms `yⱼᵢ` of `K`, then
`F (coker φ) ≅ c (coker (yⱼᵢ))` (`CategoryTheory.Functor.cokernelIsoOfComponents`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- The isomorphism `F (Pᵐ) ≅ Qᵐ` induced by `e : F P ≅ Q`, for an additive functor `F`. -/
noncomputable def mapBiproductPowIso (F : C ⥤ D) [F.Additive] {P : C} {Q : D}
    (e : F.obj P ≅ Q) (m : ℕ) :
    F.obj (⨁ fun _ : Fin m ↦ P) ≅ ⨁ fun _ : Fin m ↦ Q :=
  F.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ e

/-- The components of the image of a morphism between finite powers, transported along
`mapBiproductPowIso`. -/
@[reassoc]
lemma ι_mapBiproductPowIso_inv_map_hom_π (F : C ⥤ D) [F.Additive] {P : C} {Q : D}
    (e : F.obj P ≅ Q) {m n : ℕ} (φ : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin n ↦ P)
    (j : Fin m) (i : Fin n) :
    biproduct.ι (fun _ : Fin m ↦ Q) j ≫ (F.mapBiproductPowIso e m).inv ≫ F.map φ ≫
        (F.mapBiproductPowIso e n).hom ≫ biproduct.π (fun _ : Fin n ↦ Q) i =
      e.inv ≫ F.map (biproduct.ι (fun _ : Fin m ↦ P) j ≫ φ ≫ biproduct.π (fun _ : Fin n ↦ P) i) ≫
        e.hom := by
  simp [mapBiproductPowIso, biproduct.mapIso]

variable {E : Type*} [Category* E] [Preadditive E] [HasFiniteBiproducts E] [HasCokernels C]
  [HasCokernels D] [HasCokernels E]

/-- Let `F : C ⥤ D` and `c : E ⥤ D` be additive functors preserving cokernels, `e : F P ≅ c K`
and `φ : Pᵐ ⟶ Pⁿ` a morphism whose components correspond under `e` to the images under `c` of
endomorphisms `y j i` of `K`. Then `F (coker φ) ≅ c (coker y)`, `y` viewed as a morphism
`Kᵐ ⟶ Kⁿ`. -/
noncomputable def cokernelIsoOfComponents (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] (c : E ⥤ D) [c.Additive]
    [PreservesColimitsOfShape WalkingParallelPair c] {P : C} {K : E} (e : F.obj P ≅ c.obj K)
    {m n : ℕ} (φ : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin n ↦ P) (y : Fin m → Fin n → (K ⟶ K))
    (h : ∀ j i, e.inv ≫ F.map (biproduct.ι (fun _ : Fin m ↦ P) j ≫ φ ≫
      biproduct.π (fun _ : Fin n ↦ P) i) ≫ e.hom = c.map (y j i)) :
    F.obj (cokernel φ) ≅ c.obj (cokernel (biproduct.matrix y)) :=
  PreservesCokernel.iso F φ ≪≫
    cokernel.mapIso (F.map φ) (c.map (biproduct.matrix y))
      (F.mapBiproductPowIso e m ≪≫ (c.mapBiproductPowIso (Iso.refl _) m).symm)
      (F.mapBiproductPowIso e n ≪≫ (c.mapBiproductPowIso (Iso.refl _) n).symm) (by
        have key : (F.mapBiproductPowIso e m).inv ≫ F.map φ ≫ (F.mapBiproductPowIso e n).hom =
            (c.mapBiproductPowIso (Iso.refl _) m).inv ≫ c.map (biproduct.matrix y) ≫
              (c.mapBiproductPowIso (Iso.refl _) n).hom := by
          refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun i ↦ ?_
          simp only [Category.assoc]
          rw [ι_mapBiproductPowIso_inv_map_hom_π, ι_mapBiproductPowIso_inv_map_hom_π, h,
            biproduct.ι_matrix_assoc, biproduct.lift_π]
          simp
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
        rw [← Iso.inv_comp_eq, reassoc_of% key]
        simp) ≪≫
    (PreservesCokernel.iso c (biproduct.matrix y)).symm

end CategoryTheory.Functor
