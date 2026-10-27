/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Lifting morphisms between finite biproducts along an additive functor

If an additive functor `F` is surjective on morphisms `F U ⟶ F M`, it is surjective on morphisms
`F (⨁ U) ⟶ F (⨁ M)` between images of finite biproducts of copies of `U` and of `M`
(`CategoryTheory.Functor.exists_map_eq_biproduct`): a morphism between biproducts is determined by
its matrix of components.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- An additive functor which is surjective on morphisms `F U ⟶ F M` is surjective on morphisms
`F (⨁ U) ⟶ F (⨁ M)` between finite biproducts of copies of `U` and `M`. -/
lemma exists_map_eq_biproduct {J K : Type} [Finite J] [Finite K] [HasBiproductsOfShape J C]
    [HasBiproductsOfShape K C] (U M : C)
    (h : ∀ ψ : F.obj U ⟶ F.obj M, ∃ d : U ⟶ M, F.map d = ψ)
    (T : F.obj (⨁ fun _ : J ↦ U) ⟶ F.obj (⨁ fun _ : K ↦ M)) :
    ∃ T' : (⨁ fun _ : J ↦ U) ⟶ ⨁ fun _ : K ↦ M, F.map T' = T := by
  have := Fintype.ofFinite J
  have := Fintype.ofFinite K
  choose d hd using fun (j : J) (k : K) ↦ h (F.map (biproduct.ι (fun _ : J ↦ U) j) ≫ T ≫
    F.map (biproduct.π (fun _ : K ↦ M) k))
  refine ⟨∑ j, ∑ k, biproduct.π (fun _ : J ↦ U) j ≫ d j k ≫ biproduct.ι (fun _ : K ↦ M) k, ?_⟩
  have hJ : (∑ j, biproduct.π (fun _ : J ↦ U) j ≫ biproduct.ι (fun _ : J ↦ U) j) = 𝟙 _ :=
    biproduct.total (f := fun _ : J ↦ U)
  have hK : (∑ k, biproduct.π (fun _ : K ↦ M) k ≫ biproduct.ι (fun _ : K ↦ M) k) = 𝟙 _ :=
    biproduct.total (f := fun _ : K ↦ M)
  calc F.map (∑ j, ∑ k, biproduct.π (fun _ : J ↦ U) j ≫ d j k ≫ biproduct.ι (fun _ : K ↦ M) k)
      = ∑ j, ∑ k, F.map (biproduct.π (fun _ : J ↦ U) j) ≫
          (F.map (biproduct.ι (fun _ : J ↦ U) j) ≫ T ≫ F.map (biproduct.π (fun _ : K ↦ M) k)) ≫
            F.map (biproduct.ι (fun _ : K ↦ M) k) := by
        simp only [F.map_sum, F.map_comp, hd]
    _ = F.map (∑ j, biproduct.π (fun _ : J ↦ U) j ≫ biproduct.ι (fun _ : J ↦ U) j) ≫ T ≫
          F.map (∑ k, biproduct.π (fun _ : K ↦ M) k ≫ biproduct.ι (fun _ : K ↦ M) k) := by
        simp only [F.map_sum, F.map_comp, Preadditive.sum_comp, Preadditive.comp_sum,
          Category.assoc]
        exact Finset.sum_comm
    _ = T := by rw [hJ, hK, F.map_id, F.map_id, Category.id_comp, Category.comp_id]

end CategoryTheory.Functor
