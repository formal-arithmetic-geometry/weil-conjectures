/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
/-! # Computation maps for conjugates of localized adjunctions -/
@[expose] public section
set_option autoImplicit false
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory
namespace CategoryTheory
/-- A conjugate is computed by the original conjugate whenever both adjunction units and
the right-adjoint comparison are computed by the given localization maps.
Source: naturality and the unit characterization of mates
(blueprint: lem-sf-derived-conjugate-normalization).
Proof: apply the second localized adjunction's hom equivalence. The conjugate unit equation,
then naturality and the two unit computation equations, identify the transposes with the
localized ordinary conjugate unit equation. Injectivity of the hom equivalence concludes. -/
theorem conjugate_normalization
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (Q : C ⥤ C') (V : D ⥤ D')
    {L₀ L₁ : C ⥤ D} {R₀ R₁ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁)
    {L₀' L₁' : C' ⥤ D'} {R₀' R₁' : D' ⥤ C'}
    (b₀ : L₀' ⊣ R₀') (b₁ : L₁' ⊣ R₁')
    (c₀ : Q ⋙ L₀' ⟶ L₀ ⋙ V) (c₁ : Q ⋙ L₁' ⟶ L₁ ⋙ V)
    (d₀ : R₀ ⋙ Q ⟶ V ⋙ R₀') (d₁ : R₁ ⋙ Q ⟶ V ⋙ R₁')
    (h₀ : ∀ P, b₀.unit.app (Q.obj P) ≫ R₀'.map (c₀.app P) =
      Q.map (a₀.unit.app P) ≫ d₀.app (L₀.obj P))
    (h₁ : ∀ P, b₁.unit.app (Q.obj P) ≫ R₁'.map (c₁.app P) =
      Q.map (a₁.unit.app P) ≫ d₁.app (L₁.obj P))
    (r : R₀ ⟶ R₁) (r' : R₀' ⟶ R₁')
    (hr : ∀ N, d₀.app N ≫ r'.app (V.obj N) = Q.map (r.app N) ≫ d₁.app N)
    (P : C) :
    ((conjugateEquiv b₀ b₁).symm r').app (Q.obj P) ≫ c₀.app P =
      c₁.app P ≫ V.map (((conjugateEquiv a₀ a₁).symm r).app P) := by
  apply (b₁.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← unit_conjugateEquiv_symm b₀ b₁ r' (Q.obj P), Category.assoc,
    ← r'.naturality, ← Category.assoc, h₀, Category.assoc]
  simp only [Functor.comp_obj]
  rw [hr,
    ← Category.assoc, ← Q.map_comp, unit_conjugateEquiv_symm a₀ a₁ r P,
    Q.map_comp, Category.assoc]
  have hd := d₁.naturality (((conjugateEquiv a₀ a₁).symm r).app P)
  dsimp at hd
  rw [hd]
  simp only [← Category.assoc]
  rw [← h₁]
/-- Unit computation is preserved by composing two adjunctions.
Source: composite adjunction unit and naturality
(blueprint: lem-sf-derived-adjunction-composite-normalization).
Proof: expand the composite unit; move the first left computation through the second unit.
Apply the two unit equations, and move the remaining ordinary unit through the first right
computation by naturality. -/
theorem unit_normalization_comp
    {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    (Q : A ⥤ A') (V : B ⥤ B') (W : C ⥤ C')
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : B' ⥤ C'} {S' : C' ⥤ B'}
    (a : F ⊣ R) (b : G ⊣ S) (a' : F' ⊣ R') (b' : G' ⊣ S')
    (c : Q ⋙ F' ⟶ F ⋙ V) (d : V ⋙ G' ⟶ G ⋙ W)
    (e : R ⋙ Q ⟶ V ⋙ R') (f : S ⋙ V ⟶ W ⋙ S')
    (hc : ∀ P, a'.unit.app (Q.obj P) ≫ R'.map (c.app P) =
      Q.map (a.unit.app P) ≫ e.app (F.obj P))
    (hd : ∀ P, b'.unit.app (V.obj P) ≫ S'.map (d.app P) =
      V.map (b.unit.app P) ≫ f.app (G.obj P)) (P : A) :
    (a'.comp b').unit.app (Q.obj P) ≫
        R'.map (S'.map (G'.map (c.app P) ≫ d.app (F.obj P))) =
      Q.map ((a.comp b).unit.app P) ≫
        e.app (S.obj (G.obj (F.obj P))) ≫ R'.map (f.app (G.obj (F.obj P))) := by
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  have hb := b'.unit.naturality (c.app P)
  dsimp at hb
  rw [← R'.map_comp_assoc, ← hb, R'.map_comp_assoc,
    ← Category.assoc, hc]
  simp only [Category.assoc]
  rw [← R'.map_comp, hd, R'.map_comp]
  have he := e.naturality (b.unit.app (F.obj P))
  dsimp at he
  rw [← reassoc_of% he]
end CategoryTheory
