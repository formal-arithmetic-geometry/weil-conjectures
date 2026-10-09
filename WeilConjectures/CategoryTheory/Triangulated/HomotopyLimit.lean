/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Homotopy limits of towers in a pretriangulated category

Let `F : ℕᵒᵖ ⥤ C` be a tower `⋯ ⟶ F₂ ⟶ F₁ ⟶ F₀` in a pretriangulated category. A categorical
limit of `F` rarely exists in a triangulated category, and when it does it is not the derived
limit. The *homotopy limit* `R lim F` is instead characterised, up to non-unique isomorphism,
by the Milnor (or Roos) triangle

```
  R lim F ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ⟶ (R lim F)[1]
```

where `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. In the derived category of an
abelian category with exact countable products, such as sheaves on a replete topos, this is
the derived functor of `lim` applied to the tower.

## Main definitions

- `CategoryTheory.Pretriangulated.towerShift`: the map `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ`.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit`: a cone over a tower is a homotopy limit
  cone if its legs fit into a distinguished Milnor triangle.

## Main statements

- `CategoryTheory.Pretriangulated.IsHomotopyLimit.of_iso`: being a homotopy limit cone is
  invariant under isomorphisms of towers and of cone points.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.map`: a triangulated functor preserving the
  product `∏ₙ Fₙ` sends homotopy limit cones to homotopy limit cones.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The transition endomorphism `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` of a product of the terms of a tower
`F : ℕᵒᵖ ⥤ C`, with components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
noncomputable def towerShift {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) : P.pt ⟶ P.pt :=
  Fan.IsLimit.lift hP fun n ↦ P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op

/-- A cone `c` over a tower `F : ℕᵒᵖ ⥤ C` is a *homotopy limit* cone if, for a product
`∏ₙ Fₙ`, the Milnor triangle

```
  c.pt ──(c.π n)ₙ──▶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ──δ──▶ c.pt⟦1⟧
```

is distinguished for some `δ`, where `t` is `towerShift`. The point of a homotopy limit cone is
then the derived limit `R lim F`, determined up to non-unique isomorphism. -/
def IsHomotopyLimit {F : ℕᵒᵖ ⥤ C} (c : Cone F) : Prop :=
  ∃ (P : Fan fun n : ℕ ↦ F.obj (op n)) (hP : IsLimit P) (δ : P.pt ⟶ c.pt⟦(1 : ℤ)⟧),
    Triangle.mk (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) (𝟙 P.pt - towerShift hP) δ ∈
      distTriang C

namespace IsHomotopyLimit

/-- Being a homotopy limit cone is invariant under isomorphisms: if `c` is a homotopy limit
cone over `F`, `e : F ≅ G` and `eπ : c.pt ≅ c'.pt` are compatible with the legs, then `c'` is a
homotopy limit cone over `G`. -/
lemma of_iso {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) {c : Cone F} (hc : IsHomotopyLimit c) (c' : Cone G)
    (eπ : c.pt ≅ c'.pt)
    (h : ∀ n : ℕ, c.π.app (op n) ≫ e.hom.app (op n) = eπ.hom ≫ c'.π.app (op n)) :
    IsHomotopyLimit c' := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let P' : Fan fun n : ℕ ↦ G.obj (op n) := Fan.mk P.pt fun n ↦ P.proj n ≫ e.hom.app (op n)
  have hP' : IsLimit P' := Fan.IsLimit.mk _
    (fun s ↦ Fan.IsLimit.lift hP fun n ↦ s.proj n ≫ e.inv.app (op n))
    (fun s n ↦ by simp [P'])
    (fun s m hm ↦ Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [← hm n, P'])
  have ht : towerShift hP' = towerShift hP := Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
    rw [towerShift, Fan.IsLimit.fac]
    simp only [P', fan_mk_proj, towerShift, Category.assoc, Fan.IsLimit.fac_assoc,
      NatTrans.naturality]
  refine ⟨P', hP', δ ≫ (shiftFunctor C (1 : ℤ)).map eπ.hom,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ eπ.symm (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hP' _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Fan.IsLimit.fac,
      Iso.symm_hom, Category.assoc]
    simp only [P', fan_mk_proj, Fan.IsLimit.fac_assoc, h, Iso.inv_hom_id_assoc]
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp, ht]
    rfl
  · simp [← Functor.map_comp]

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A triangulated functor `Φ` that preserves the product `∏ₙ Fₙ` sends a homotopy limit
cone over `F` to a homotopy limit cone over `F ⋙ Φ`: it sends the Milnor triangle of `F` to that
of `F ⋙ Φ`. -/
lemma map {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c) (Φ : C ⥤ D) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Additive]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ F.obj (op n)) Φ] :
    IsHomotopyLimit (Φ.mapCone c) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let hP' := isLimitFanMkObjOfIsLimit Φ (fun n : ℕ ↦ F.obj (op n)) P.proj hP
  have ht : towerShift (F := F ⋙ Φ) hP' = Φ.map (towerShift hP) :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      rw [towerShift, Fan.IsLimit.fac]
      simp only [fan_mk_proj, Functor.comp_map, ← Functor.map_comp, towerShift,
        Fan.IsLimit.fac]
  refine ⟨_, hP', Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app c.pt,
    isomorphic_distinguished _ (Φ.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hP' _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [Fan.IsLimit.fac]
    change _ = Φ.map (Fan.IsLimit.lift hP _) ≫ Φ.map (P.proj n)
    rw [← Functor.map_comp, Fan.IsLimit.fac]
    rfl
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp]
    change _ = Φ.map (𝟙 P.pt - towerShift hP)
    rw [ht, Functor.map_sub, Functor.map_id]
    rfl
  · simp only [Iso.refl_hom, Functor.map_id, Category.comp_id, Category.id_comp]
    rfl

end IsHomotopyLimit

end CategoryTheory.Pretriangulated
