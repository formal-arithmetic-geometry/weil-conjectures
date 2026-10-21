/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Right-action evaluation of a tensor arrow mate

Source: Stacks Project, Tag 0B56, equation-projection-formula-map, and Tag 0037;
arbitrary-arrow categorical expansion of the adjunct construction
(blueprint: lem-weil-pbc-tensor-arrow-mate-right-unit).

The tensor operations are bare bifunctors. The formulas for beta, alpha and k
are expanded directly in the two equalities, without introducing new notions.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

/-- Right-action evaluation for the tensor mate of an arbitrary arrow.

Source: Stacks Project, Tag 0B56, equation-projection-formula-map, with the unit
naturality of Tag 0037 (blueprint: lem-weil-pbc-tensor-arrow-mate-right-unit).

Proof: bifunctoriality identifies the two composites of `c` in the first variable
and `u.hom` in the second variable with the image of their pair. Naturality of
`rhoD.hom` at `c` therefore gives `k_E (c tensor 1) = c k_(L K)`. Precompose
with `mu.hom.app (K, oneC)` and use `right_action K` to obtain the first equality.
For the second equality, expand alpha as the unit followed by `R` of beta.
Functoriality of `R` and the first equality replace beta followed by k with
`L` of the right action followed by `c`. Naturality of `adj.unit` at
`rhoC.hom.app K` then gives the required composite. The natural unit is the one
in lem-weil-pbc-adjunction-of-natural-bijection, represented by Mathlib's
`Adjunction` (and constructed from natural hom bijections by `Adjunction.mkOfHomEquiv`).
-/
theorem tensorArrowMate_right_unit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (mu : TC ⋙ L ≅ L.prod L ⋙ TD)
    (oneC : C) (oneD : D)
    (rhoC : (𝟭 C).prod' ((Functor.const C).obj oneC) ⋙ TC ≅ 𝟭 C)
    (rhoD : (𝟭 D).prod' ((Functor.const D).obj oneD) ⋙ TD ≅ 𝟭 D)
    (u : L.obj oneC ≅ oneD)
    (right_action : ∀ M : C,
      mu.hom.app (M, oneC) ≫ TD.map (Prod.mkHom (𝟙 (L.obj M)) u.hom) ≫
        rhoD.hom.app (L.obj M) = L.map (rhoC.hom.app M))
    (K : C) (E : D) (c : L.obj K ⟶ E) :
    (mu.hom.app (K, oneC) ≫ TD.map (Prod.mkHom c (𝟙 (L.obj oneC)))) ≫
        (TD.map (Prod.mkHom (𝟙 E) u.hom) ≫ rhoD.hom.app E) =
      L.map (rhoC.hom.app K) ≫ c ∧
    (adj.unit.app (TC.obj (K, oneC)) ≫
        R.map (mu.hom.app (K, oneC) ≫ TD.map (Prod.mkHom c (𝟙 (L.obj oneC))))) ≫
        R.map (TD.map (Prod.mkHom (𝟙 E) u.hom) ≫ rhoD.hom.app E) =
      rhoC.hom.app K ≫ adj.unit.app K ≫ R.map c := by
  have interchange :
      TD.map (Prod.mkHom c (𝟙 (L.obj oneC))) ≫ TD.map (Prod.mkHom (𝟙 E) u.hom) =
        TD.map (Prod.mkHom (𝟙 (L.obj K)) u.hom) ≫
          TD.map (Prod.mkHom c (𝟙 oneD)) := by
    simp only [← TD.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  have naturality :
      TD.map (Prod.mkHom c (𝟙 oneD)) ≫ rhoD.hom.app E =
        rhoD.hom.app (L.obj K) ≫ c := by
    simpa using rhoD.hom.naturality c
  have beta :
      (mu.hom.app (K, oneC) ≫ TD.map (Prod.mkHom c (𝟙 (L.obj oneC)))) ≫
          (TD.map (Prod.mkHom (𝟙 E) u.hom) ≫ rhoD.hom.app E) =
        L.map (rhoC.hom.app K) ≫ c := by
    rw [Category.assoc, ← Category.assoc (TD.map (Prod.mkHom c _)), interchange,
      Category.assoc, naturality]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ c) (right_action K)
  refine ⟨beta, ?_⟩
  rw [Category.assoc, ← R.map_comp, beta, R.map_comp]
  simpa only [Category.assoc, Functor.comp_obj, Functor.prod'_obj, Functor.id_obj,
    Functor.const_obj_obj] using
    congrArg (fun f ↦ f ≫ R.map c) (adj.unit_naturality (rhoC.hom.app K))

end CategoryTheory.Adjunction
