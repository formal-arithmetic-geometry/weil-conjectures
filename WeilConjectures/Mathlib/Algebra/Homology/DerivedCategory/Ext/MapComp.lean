/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Pushing `Ext`-classes forward along a composite of exact functors

Let `G₁ : C ⥤ D`, `G₂ : D ⥤ E` and `G : C ⥤ E` be exact functors between abelian categories
together with an isomorphism `τ : G ≅ G₁ ⋙ G₂`. Pushing an `Ext`-class forward along `G₁` and
then along `G₂` is pushing it forward along `G`, up to the isomorphisms given by `τ`.

## Main statements

- `CategoryTheory.Abelian.Ext.mapExactFunctor_mapExactFunctor_of_iso`: the comparison of the
  two push-forwards.
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

namespace CategoryTheory.Abelian.Ext

open Limits

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Precomposing with an isomorphism of degree `0` does not change whether a class vanishes. -/
lemma mk₀_comp_eq_zero_iff {A A' B : C} {n : ℕ} (u : A' ⟶ A) [IsIso u] (y : Ext A B n) :
    (mk₀ u).comp y (zero_add n) = 0 ↔ y = 0 := by
  refine ⟨fun hy ↦ ?_, fun hy ↦ by rw [hy, comp_zero]⟩
  have := congrArg (fun z ↦ (mk₀ (inv u)).comp z (zero_add n)) hy
  simpa only [mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, mk₀_id_comp, comp_zero] using this

/-- Postcomposing with an isomorphism of degree `0` does not change whether a class vanishes. -/
lemma comp_mk₀_eq_zero_iff {A B B' : C} {n : ℕ} (v : B ⟶ B') [IsIso v] (y : Ext A B n) :
    y.comp (mk₀ v) (add_zero n) = 0 ↔ y = 0 := by
  refine ⟨fun hy ↦ ?_, fun hy ↦ by rw [hy, zero_comp]⟩
  have := congrArg (fun z ↦ z.comp (mk₀ (inv v)) (add_zero n)) hy
  simpa only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, IsIso.hom_inv_id, comp_mk₀_id,
    zero_comp] using this

end

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]
  [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E] [EnoughInjectives C]

/-- Pushing an `Ext`-class forward along `G₁` and then along `G₂` is pushing it forward along
a functor `G ≅ G₁ ⋙ G₂`, conjugated by the components of the isomorphism. -/
lemma mapExactFunctor_mapExactFunctor_of_iso (G₁ : C ⥤ D) [G₁.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁] (G₂ : D ⥤ E) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (G : C ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : G ≅ G₁ ⋙ G₂) {A B : C} {n : ℕ}
    (x : Ext A B n) :
    (x.mapExactFunctor G₁).mapExactFunctor G₂ =
      (mk₀ (τ.inv.app A)).comp ((x.mapExactFunctor G).comp (mk₀ (τ.hom.app B)) (add_zero n))
        (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective A B).2 x
    rw [mapExactFunctor_mk₀, mapExactFunctor_mk₀, mapExactFunctor_mk₀, mk₀_comp_mk₀,
      mk₀_comp_mk₀]
    congr 1
    simp
  | succ n ih =>
    let ι := Injective.ι B
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) rfl
    have h₁ := hS.map_of_exact G₁
    have h₁₂ := h₁.map_of_exact G₂
    have h := hS.map_of_exact G
    let φ : S.map G ⟶ (S.map G₁).map G₂ :=
      { τ₁ := τ.hom.app S.X₁
        τ₂ := τ.hom.app S.X₂
        τ₃ := τ.hom.app S.X₃
        comm₁₂ := (τ.hom.naturality S.f).symm
        comm₂₃ := (τ.hom.naturality S.g).symm }
    have hφ : h.extClass.comp (mk₀ (τ.hom.app B)) (add_zero 1) =
        (mk₀ (τ.hom.app S.X₃)).comp h₁₂.extClass (zero_add 1) :=
      h.extClass_naturality h₁₂ φ
    have e₁ : ((y.comp hS.extClass rfl).mapExactFunctor G₁).mapExactFunctor G₂ =
        ((y.mapExactFunctor G₁).mapExactFunctor G₂).comp h₁₂.extClass rfl := by
      rw [mapExactFunctor_comp, mapExactFunctor_extClass, mapExactFunctor_comp,
        mapExactFunctor_extClass]
    have e₂ : (y.comp hS.extClass rfl).mapExactFunctor G =
        (y.mapExactFunctor G).comp h.extClass rfl := by
      rw [mapExactFunctor_comp, mapExactFunctor_extClass]
    rw [e₁, e₂, ih y, comp_assoc_of_third_deg_zero (y.mapExactFunctor G) h.extClass, hφ,
      comp_assoc _ _ _ (zero_add n) rfl (by omega), comp_assoc_of_second_deg_zero]

end CategoryTheory.Abelian.Ext
