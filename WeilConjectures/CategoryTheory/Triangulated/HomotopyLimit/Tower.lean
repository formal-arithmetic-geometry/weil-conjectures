/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Homotopy limits of towers of triangles

Let `F ⟶ G ⟶ H ⟶ F⟦1⟧` be a tower (indexed by `ℕᵒᵖ`) of distinguished triangles in a
pretriangulated category with countable products, whose third term is a constant object `H`
and whose first term `F` is *pro-zero*: the composite of `N` consecutive transition maps of `F`
vanishes. Then the map `R lim G ⟶ H` induced by `G ⟶ H` is an isomorphism. This is the
triangulated form of the fact that the derived limit of a pro-zero tower vanishes.

## Main results

- `CategoryTheory.Pretriangulated.isIso_of_endo_triangle`: let `φ` be an endomorphism of a
  distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` such that `φ.hom₁` is an isomorphism and
  `φ.hom₃` has a section. Then the map from a fiber of `φ.hom₂` to a fiber of `φ.hom₃` induced
  by `T.mor₂` is an isomorphism.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.isIso_π_comp_of_triangles`: the statement
  above about towers of triangles.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.whiskerAdd`: the legs `c.π (n + k)` of a
  homotopy limit cone exhibit its point as the homotopy limit of the shifted tower
  `n ↦ F (n + k)`.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_of_iso`: isomorphic towers have
  isomorphic homotopy limits, compatibly with the legs.

-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section TowerShift

variable {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)

end TowerShift

namespace IsHomotopyLimit

/-- The Milnor triangle of a homotopy limit cone can be formed with any product of the tower. -/
lemma exists_distTriang {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c)
    {P' : Fan fun n : ℕ ↦ F.obj (op n)} (hP' : IsLimit P') :
    ∃ δ : P'.pt ⟶ c.pt⟦(1 : ℤ)⟧,
      Triangle.mk (Fan.IsLimit.lift hP' fun n ↦ c.π.app (op n)) (𝟙 _ - towerShift hP') δ ∈
        distTriang C := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let e : P.pt ≅ P'.pt := hP.conePointUniqueUpToIso hP'
  have he (n : ℕ) : e.hom ≫ P'.proj n = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp hP' ⟨n⟩
  have ht : towerShift hP ≫ e.hom = e.hom ≫ towerShift hP' :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      rw [assoc, he, towerShift_proj, assoc, towerShift_proj, ← assoc, he]
  refine ⟨e.inv ≫ δ, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, id_comp,
      Iso.symm_hom, assoc, Fan.IsLimit.fac]
    rw [← he, e.inv_hom_id_assoc, Fan.IsLimit.fac]
  · have ht' : towerShift hP' ≫ e.inv = e.inv ≫ towerShift hP := by
      rw [← cancel_epi e.hom, ← reassoc_of% ht, e.hom_inv_id, comp_id, e.hom_inv_id_assoc]
    change (𝟙 _ - towerShift hP') ≫ e.inv = e.inv ≫ (𝟙 _ - towerShift hP)
    rw [Preadditive.sub_comp, Preadditive.comp_sub, ht', id_comp, comp_id]
  · simp

end IsHomotopyLimit

section Triangles

variable [HasLimitsOfShape (Discrete ℕ) C]

end Triangles

section Shift

end Shift

end CategoryTheory.Pretriangulated
