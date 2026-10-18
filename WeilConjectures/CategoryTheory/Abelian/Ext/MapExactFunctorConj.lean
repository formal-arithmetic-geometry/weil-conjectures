/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor

/-!
# Exact functors and `Ext`-classes composed with morphisms on both sides

For morphisms `a : X' ⟶ X`, `b : Y ⟶ Y'` and `y ∈ Extⁿ(X, Y)`, write
`CategoryTheory.Abelian.Ext.mk₀CompMk₀ a y b = a ∘ y ∘ b ∈ Extⁿ(X', Y')`. This file records how
these composites behave under composition and under pushforward along exact functors, and
deduces the comparison of two "pullback" operations on `Ext`-classes intertwined by an exact
functor (`CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀CompMk₀_of_iso`): if `τ : G₂ ⋙ G_B ≅
G_A ⋙ G₂`, then pushing `a ∘ G₂(x) ∘ b` forward along `G_B` is `G₂` of the conjugate
`α⁻¹ ∘ G_A(x) ∘ α`, up to explicit morphisms on both sides.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

section Comp

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The class `a ∘ y ∘ b ∈ Extⁿ(X', Y')` for `y ∈ Extⁿ(X, Y)` and morphisms `a : X' ⟶ X`,
`b : Y ⟶ Y'`. -/
noncomputable def mk₀CompMk₀ {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') : Ext.{w} X' Y' n :=
  (mk₀ a).comp (y.comp (mk₀ b) (add_zero n)) (zero_add n)

lemma mk₀CompMk₀_mk₀CompMk₀ {X'' X' X Y Y' Y'' : C} {n : ℕ} (a' : X'' ⟶ X') (a : X' ⟶ X)
    (y : Ext.{w} X Y n) (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    mk₀CompMk₀ a' (mk₀CompMk₀ a y b) b' = mk₀CompMk₀ (a' ≫ a) y (b ≫ b') := by
  simp only [mk₀CompMk₀, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, mk₀_comp_mk₀_assoc]

@[simp]
lemma mk₀CompMk₀_id {X Y : C} {n : ℕ} (y : Ext.{w} X Y n) : mk₀CompMk₀ (𝟙 X) y (𝟙 Y) = y := by
  simp [mk₀CompMk₀]

lemma mk₀CompMk₀_add {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y y' : Ext.{w} X Y n)
    (b : Y ⟶ Y') : mk₀CompMk₀ a (y + y') b = mk₀CompMk₀ a y b + mk₀CompMk₀ a y' b := by
  simp [mk₀CompMk₀, add_comp, comp_add]


end Comp

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]

lemma mapExactFunctor_mk₀CompMk₀ (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') :
    (mk₀CompMk₀ a y b).mapExactFunctor F =
      mk₀CompMk₀ (F.map a) (y.mapExactFunctor F) (F.map b) := by
  simp only [mk₀CompMk₀, mapExactFunctor_comp, mapExactFunctor_mk₀]

/-- `mapExactFunctor_eq_of_iso`, in terms of `mk₀CompMk₀`. -/
lemma mapExactFunctor_eq_mk₀CompMk₀_of_iso [EnoughInjectives C] {G G' : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G'.Additive]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (τ : G ≅ G') {A B : C} {n : ℕ}
    (x : Ext.{w} A B n) :
    x.mapExactFunctor G' = mk₀CompMk₀ (τ.inv.app A) (x.mapExactFunctor G) (τ.hom.app B) :=
  mapExactFunctor_eq_of_iso τ x

/-- **Pullbacks of `Ext`-classes intertwined by an exact functor.** Let `G₂ : C ⥤ D`,
`G_C : C ⥤ C`, `G_D : D ⥤ D` be exact and `τ : G₂ ⋙ G_D ≅ G_C ⋙ G₂`. For `x ∈ Extⁿ(P, P)`,
pushing `ζ ∘ G_D(U ∘ G₂(x) ∘ V) ∘ κ` is `L ∘ G₂(α⁻¹ ∘ G_C(x) ∘ α) ∘ R` for explicit `L`, `R`. -/
lemma mapExactFunctor_mk₀CompMk₀_of_iso [EnoughInjectives C] (G₂ : C ⥤ D) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (GC : C ⥤ C) [GC.Additive]
    [PreservesFiniteLimits GC] [PreservesFiniteColimits GC] (GD : D ⥤ D) [GD.Additive]
    [PreservesFiniteLimits GD] [PreservesFiniteColimits GD]
    [PreservesFiniteLimits (G₂ ⋙ GD)] [PreservesFiniteColimits (G₂ ⋙ GD)]
    [PreservesFiniteLimits (GC ⋙ G₂)] [PreservesFiniteColimits (GC ⋙ G₂)]
    (τ : G₂ ⋙ GD ≅ GC ⋙ G₂) {P : C} {I J : D} (U : I ⟶ G₂.obj P) (V : G₂.obj P ⟶ J)
    (ζ : I ⟶ GD.obj I) (κ : GD.obj J ⟶ J) (α : GC.obj P ≅ P) {n : ℕ} (x : Ext.{w} P P n) :
    mk₀CompMk₀ ζ ((mk₀CompMk₀ U (x.mapExactFunctor G₂) V).mapExactFunctor GD) κ =
      mk₀CompMk₀ (ζ ≫ GD.map U ≫ τ.hom.app P ≫ G₂.map α.hom)
        ((mk₀CompMk₀ α.inv (x.mapExactFunctor GC) α.hom).mapExactFunctor G₂)
        (G₂.map α.inv ≫ τ.inv.app P ≫ GD.map V ≫ κ) := by
  rw [mapExactFunctor_mk₀CompMk₀, mapExactFunctor_mk₀CompMk₀, mapExactFunctor_mapExactFunctor,
    mapExactFunctor_mapExactFunctor (G₁ := GC), mapExactFunctor_eq_mk₀CompMk₀_of_iso τ.symm]
  simp only [mk₀CompMk₀_mk₀CompMk₀]
  congr 1 <;> simp [← Functor.map_comp, ← Functor.map_comp_assoc]

end CategoryTheory.Abelian.Ext
