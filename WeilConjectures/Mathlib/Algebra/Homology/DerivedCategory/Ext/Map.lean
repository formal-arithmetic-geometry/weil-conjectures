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
# Vanishing of `Ext¹`-classes pushed along an exact functor

Let `G : C ⥤ D` be an exact functor between abelian categories and `S` a short exact sequence
in `C`. A class of `Ext¹(A, S.X₁)` of the form `a ∘ δ_S`, with `a : A ⟶ S.X₃` and `δ_S` the
extension class of `S`, pushed forward along `G` and pulled back along some `u : A' ⟶ G A`,
vanishes exactly when `u ≫ G a` lifts along `G S.g`. When `S.X₂` is injective every class of
`Ext¹(A, S.X₁)` has this form, so the vanishing of the pushed-forward class only depends on the
functor `G` up to isomorphism and on `u` up to precomposition.

## Main statements

- `CategoryTheory.Abelian.Ext.mk₀_comp_mapExactFunctor_eq_zero_iff`: the lifting criterion.
- `CategoryTheory.Abelian.Ext.mk₀_comp_mapExactFunctor_comp_eq_zero_iff`: the class pushed
  forward along `G₁` and then along `G₂` vanishes exactly when it vanishes pushed forward
  along any functor isomorphic to `G₁ ⋙ G₂`.
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- A class `a ∘ δ_S` of `Ext¹(A, S.X₁)`, pushed forward along an exact functor `G` and pulled
back along `u : A' ⟶ G A`, is the class `(u ≫ G a) ∘ δ_{G S}`. -/
lemma mk₀_comp_mapExactFunctor_mk₀_comp_extClass (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {S : ShortComplex C}
    (hS : S.ShortExact) {A : C} {A' : D} (a : A ⟶ S.X₃) (u : A' ⟶ G.obj A) :
    (mk₀ u).comp (((mk₀ a).comp hS.extClass (zero_add 1)).mapExactFunctor G) (zero_add 1) =
      (mk₀ (u ≫ G.map a)).comp (hS.map_of_exact G).extClass (zero_add 1) := by
  rw [mapExactFunctor_comp, mapExactFunctor_mk₀, mapExactFunctor_extClass,
    ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]

/-- A class `a ∘ δ_S` of `Ext¹(A, S.X₁)`, pushed forward along an exact functor `G` and pulled
back along `u : A' ⟶ G A`, vanishes exactly when `u ≫ G a` lifts along `G S.g`. -/
lemma mk₀_comp_mapExactFunctor_eq_zero_iff (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] {S : ShortComplex C} (hS : S.ShortExact) {A : C} {A' : D}
    (a : A ⟶ S.X₃) (u : A' ⟶ G.obj A) :
    (mk₀ u).comp (((mk₀ a).comp hS.extClass (zero_add 1)).mapExactFunctor G) (zero_add 1) = 0 ↔
      ∃ c : A' ⟶ G.obj S.X₂, u ≫ G.map a = c ≫ G.map S.g := by
  have hGS := hS.map_of_exact G
  rw [mk₀_comp_mapExactFunctor_mk₀_comp_extClass]
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ A' hGS (mk₀ (u ≫ G.map a)) (zero_add 1) h
    obtain ⟨c, rfl⟩ := (mk₀_bijective A' (G.obj S.X₂)).2 x₂
    refine ⟨c, (mk₀_bijective _ _).1 ?_⟩
    rw [← hx₂, mk₀_comp_mk₀]
    rfl
  · rintro ⟨c, hc⟩
    rw [hc, ← mk₀_comp_mk₀, comp_assoc_of_second_deg_zero]
    have : (mk₀ (S.map G).g).comp hGS.extClass (zero_add 1) = 0 := hGS.comp_extClass
    rw [show G.map S.g = (S.map G).g from rfl, this, comp_zero]

variable {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E] [EnoughInjectives C]

/-- Let `G₁ : C ⥤ D`, `G₂ : D ⥤ E` and `G : C ⥤ E` be exact functors with `G ≅ G₁ ⋙ G₂`, and
let `x` be a class of `Ext¹(A, B)`. Pushing `x` forward along `G₁`, pulling it back along an
isomorphism `u₁ : A₁ ⟶ G₁ A`, pushing forward along `G₂` and pulling back along an isomorphism
`u₂ : A₂ ⟶ G₂ A₁` gives zero exactly when pushing `x` forward along `G` and pulling it back
along an isomorphism `u : A₂ ⟶ G A` gives zero. -/
lemma mk₀_comp_mapExactFunctor_comp_eq_zero_iff (G₁ : C ⥤ D) [G₁.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁] (G₂ : D ⥤ E) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (G : C ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : G ≅ G₁ ⋙ G₂) {A B : C}
    {A₁ : D} {A₂ : E} (u₁ : A₁ ⟶ G₁.obj A) (u₂ : A₂ ⟶ G₂.obj A₁) (u : A₂ ⟶ G.obj A)
    [IsIso u₁] [IsIso u₂] [IsIso u] (x : Ext A B 1) :
    (mk₀ u₂).comp (((mk₀ u₁).comp (x.mapExactFunctor G₁) (zero_add 1)).mapExactFunctor G₂)
        (zero_add 1) = 0 ↔
      (mk₀ u).comp (x.mapExactFunctor G) (zero_add 1) = 0 := by
  let ι := Injective.ι B
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) (zero_add 1)
  obtain ⟨a, rfl⟩ := (mk₀_bijective A S.X₃).2 x₃
  subst hx₃
  rw [mk₀_comp_mapExactFunctor_mk₀_comp_extClass,
    mk₀_comp_mapExactFunctor_eq_zero_iff G₂ (hS.map_of_exact G₁),
    mk₀_comp_mapExactFunctor_eq_zero_iff G hS]
  have hτ {Z Z' : C} (f : Z ⟶ Z') :
      G₂.map (G₁.map f) = τ.inv.app Z ≫ G.map f ≫ τ.hom.app Z' := by
    simp
  change (∃ c, u₂ ≫ G₂.map (u₁ ≫ G₁.map a) = c ≫ G₂.map (G₁.map S.g)) ↔ _
  rw [Functor.map_comp, hτ a, hτ S.g]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨u ≫ τ.hom.app A ≫ inv (G₂.map u₁) ≫ inv u₂ ≫ c ≫ τ.inv.app S.X₂, ?_⟩
    have hc' := hc =≫ τ.inv.app S.X₃
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hc'
    simp [← hc']
  · rintro ⟨c, hc⟩
    refine ⟨u₂ ≫ G₂.map u₁ ≫ τ.inv.app A ≫ inv u ≫ c ≫ τ.hom.app S.X₂, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← reassoc_of% hc,
      IsIso.inv_hom_id_assoc]

omit [HasExt.{w'} D] [EnoughInjectives C] in
lemma mk₀_comp_eq_zero_iff_of_isIso {A A' B : C} (a : A' ⟶ A) [IsIso a] {n : ℕ}
    (y : Ext A B n) : (mk₀ a).comp y (zero_add n) = 0 ↔ y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, comp_zero]⟩
  have := congrArg (fun z ↦ (mk₀ (inv a)).comp z (zero_add n)) h
  simpa [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀] using this

omit [HasExt.{w'} D] [EnoughInjectives C] in
lemma comp_mk₀_eq_zero_iff_of_isIso {A B B' : C} (b : B ⟶ B') [IsIso b] {n : ℕ}
    (y : Ext A B n) : y.comp (mk₀ b) (add_zero n) = 0 ↔ y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zero_comp]⟩
  have := congrArg (fun z ↦ z.comp (mk₀ (inv b)) (add_zero n)) h
  simpa [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀] using this

omit [HasExt.{w'} D] in
/-- Pushing a class forward along the identity functor does not change it. -/
lemma mapExactFunctor_id {A : C} (n : ℕ) :
    ∀ {B : C} (x : Ext A B n), x.mapExactFunctor (𝟭 C) = x := by
  induction n with
  | zero =>
    intro B x
    obtain ⟨a, rfl⟩ := (mk₀_bijective A B).2 x
    rw [mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    intro B x
    let ι := Injective.ι B
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) rfl
    rw [mapExactFunctor_comp, ih, mapExactFunctor_extClass]

end CategoryTheory.Abelian.Ext
