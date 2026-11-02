/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus

/-! # Invariance of a direct condensed point-fibre representative

Source: latest blueprint, sec-six-functors-basics/sk-thm-sfb-proper-base-change/
def-weil-finite-coefficient-point.md, final paragraph; scalar transitivity in
sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md.
(blueprint: lem-weil-point-fibre-representative-transport).

All complexes are in the direct condensed-coefficient categories. Morphisms of their
full subcategories are written in the ambient derived categories. In particular equality
after `fiber` is the equality in the ordinary bounded finite-dimensional full subcategory,
read through its faithful inclusion. No field-of-definition category is used.
-/

@[expose] public section
set_option autoImplicit false

universe u v₀ v₁ v₂ u₀ u₁ u₂

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

private theorem representative_transport
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E]
    (T : C ⥤ D) (U : D ⥤ E) (V : C ⥤ E) (β : T ⋙ U ≅ V)
    {A B : C} {A' B' : D} {AΩ BΩ : E}
    (αA : T.obj A ≅ A') (αB : T.obj B ≅ B')
    (κAG : V.obj A ≅ AΩ) (κBG : V.obj B ≅ BΩ)
    (κAH : U.obj A' ≅ AΩ) (κBH : U.obj B' ≅ BΩ)
    (hA : U.map αA.hom ≫ κAH.hom = β.hom.app A ≫ κAG.hom)
    (hB : U.map αB.hom ≫ κBH.hom = β.hom.app B ≫ κBG.hom)
    (f : A ⟶ B) :
    κAH.inv ≫ U.map (αA.inv ≫ T.map f ≫ αB.hom) ≫ κBH.hom =
      κAG.inv ≫ V.map f ≫ κBG.hom := by
  have hA' : κAH.inv ≫ U.map αA.inv = κAG.inv ≫ β.inv.app A := by
    apply (cancel_mono (U.map αA.hom ≫ κAH.hom)).mp
    simp only [Category.assoc, ← U.map_comp_assoc, Iso.inv_hom_id, U.map_id,
      Category.id_comp, Iso.inv_hom_id]
    rw [hA]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hA']
  simp only [Category.assoc]
  rw [hB]
  have hn := β.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp

set_option maxHeartbeats 2000000 in
-- Scalar-tower functors carry large dependent coefficient-category presentations.
end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
