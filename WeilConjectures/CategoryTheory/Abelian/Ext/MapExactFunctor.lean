/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Functoriality of pushing `Ext`-classes along exact functors

Pushing an `Ext`-class forward along exact functors (`CategoryTheory.Abelian.Ext.mapExactFunctor`)
is compatible with composition of functors and, up to conjugation, with natural isomorphisms of
functors. Both are proved by dimension shifting along an injective presentation, where the
extension classes are compared with `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`.

## Main statements

- `CategoryTheory.Abelian.Ext.mapExactFunctor_mapExactFunctor`: pushing forward along `G₁` and
  then `G₂` is pushing forward along `G₁ ⋙ G₂`.
- `CategoryTheory.Abelian.Ext.mapExactFunctor_eq_of_iso`: pushing forward along isomorphic
  functors gives conjugate classes.
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E] [EnoughInjectives C]

/-- Pushing an `Ext`-class forward along `G₁` and then `G₂` is pushing it forward along
`G₁ ⋙ G₂`. -/
lemma mapExactFunctor_mapExactFunctor (G₁ : C ⥤ D) [G₁.Additive] [PreservesFiniteLimits G₁]
    [PreservesFiniteColimits G₁] (G₂ : D ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂]
    [PreservesFiniteColimits G₂] [PreservesFiniteLimits (G₁ ⋙ G₂)]
    [PreservesFiniteColimits (G₁ ⋙ G₂)] {A B : C} {n : ℕ} (x : Ext.{w} A B n) :
    (x.mapExactFunctor G₁).mapExactFunctor G₂ = x.mapExactFunctor (G₁ ⋙ G₂) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective A B).2 x
    simp [mapExactFunctor_mk₀]
  | succ n ih =>
    let ι := Injective.ι B
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) rfl
    have h₁ := (hS.map_of_exact G₁).map_of_exact G₂
    have h₂ := hS.map_of_exact (G₁ ⋙ G₂)
    let φ : (S.map G₁).map G₂ ⟶ S.map (G₁ ⋙ G₂) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by dsimp; rw [Category.id_comp, Category.comp_id]
        comm₂₃ := by dsimp; rw [Category.id_comp, Category.comp_id] }
    have hnat := ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ
    have hnat' : h₁.extClass.comp (mk₀ (𝟙 _)) (add_zero 1) =
        (mk₀ (𝟙 _)).comp h₂.extClass (zero_add 1) := hnat
    have e3 : h₁.extClass = h₂.extClass :=
      (comp_mk₀_id _).symm.trans (hnat'.trans (mk₀_id_comp _))
    have e1 : ((hS.map_of_exact G₁).extClass).mapExactFunctor G₂ = h₁.extClass :=
      mapExactFunctor_extClass G₂ (hS.map_of_exact G₁)
    have e2 : hS.extClass.mapExactFunctor (G₁ ⋙ G₂) = h₂.extClass :=
      mapExactFunctor_extClass _ hS
    rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_comp, ih,
      mapExactFunctor_extClass]
    exact congrArg (fun z ↦ (mapExactFunctor (G₁ ⋙ G₂) y).comp z _)
      (e1.trans (e3.trans e2.symm))

omit [HasExt.{w''} E] [EnoughInjectives C] [HasExt.{w} C] in
/-- Reassociation of a composite of `Ext`-classes along a commuting square. -/
lemma comp_comp_comp_aux {X Y Z W V V' : D} {n : ℕ} (i : Ext.{w'} X Y 0) (g : Ext Y Z n)
    (t₃ : Ext Z W 0) (e' : Ext W V 1) (e : Ext Z V' 1) (t : Ext V' V 0)
    (h : e.comp t (add_zero 1) = t₃.comp e' (zero_add 1)) :
    (i.comp (g.comp t₃ (add_zero n)) (zero_add n)).comp e' rfl =
      i.comp ((g.comp e rfl).comp t (add_zero _)) (zero_add _) := by
  rw [comp_assoc_of_third_deg_zero, h, ← comp_assoc_of_second_deg_zero]
  exact comp_assoc _ _ _ _ _ (by lia)

omit [HasExt.{w''} E] in
/-- Pushing an `Ext`-class forward along isomorphic exact functors gives conjugate classes. -/
lemma mapExactFunctor_eq_of_iso {G G' : C ⥤ D} [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [G'.Additive] [PreservesFiniteLimits G']
    [PreservesFiniteColimits G'] (τ : G ≅ G') {A B : C} {n : ℕ} (x : Ext.{w} A B n) :
    x.mapExactFunctor G' = (mk₀ (τ.inv.app A)).comp
      ((x.mapExactFunctor G).comp (mk₀ (τ.hom.app B)) (add_zero n)) (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective A B).2 x
    simp [mapExactFunctor_mk₀, mk₀_comp_mk₀]
  | succ n ih =>
    let ι := Injective.ι B
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) rfl
    have h₁ := hS.map_of_exact G
    have h₂ := hS.map_of_exact G'
    let φ : S.map G ⟶ S.map G' :=
      { τ₁ := τ.hom.app _, τ₂ := τ.hom.app _, τ₃ := τ.hom.app _
        comm₁₂ := (τ.hom.naturality S.f).symm, comm₂₃ := (τ.hom.naturality S.g).symm }
    have hnat : h₁.extClass.comp (mk₀ (τ.hom.app B)) (add_zero 1) =
        (mk₀ (τ.hom.app S.X₃)).comp h₂.extClass (zero_add 1) :=
      ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ
    have e1 : hS.extClass.mapExactFunctor G = h₁.extClass := mapExactFunctor_extClass _ hS
    have e2 : hS.extClass.mapExactFunctor G' = h₂.extClass := mapExactFunctor_extClass _ hS
    rw [mapExactFunctor_comp, mapExactFunctor_comp, ih, e1, e2]
    exact comp_comp_comp_aux _ _ _ _ _ _ hnat

end CategoryTheory.Abelian.Ext
