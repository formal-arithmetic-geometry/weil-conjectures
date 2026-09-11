/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# `Ext` and an adjunction with an exact right adjoint

Let `adj : L ⊣ R` be an adjunction between abelian categories, with `R` exact and `L` left
exact. Then, for `A` in the source of `L` and `B` in the source of `R`, applying `R` and
precomposing with the unit of the adjunction gives a map

`Ext^n (L.obj A) B ⟶ Ext^n A (R.obj B)`,

and this map is bijective.

For `n = 0` this is the adjunction itself. The general case is proved by dimension shifting
along an injective resolution of `B`, using the covariant long exact sequence of `Ext` and
the five lemma. This is a variant of Mathlib's
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, which cannot be used
here: it compares `Ext (L.obj A) B` with `Ext (R.obj (L.obj A)) (R.obj B)` rather than with
`Ext A (R.obj B)`.

## Main definitions and results

* `CategoryTheory.Adjunction.extAddHom` — the map `Ext^n (L.obj A) B →+ Ext^n A (R.obj B)`.
* `CategoryTheory.Adjunction.extAddHom_bijective` — it is bijective.
* `CategoryTheory.Adjunction.extAddEquiv` — the resulting isomorphism of additive groups.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w'} D]

namespace Adjunction

/-- Given an adjunction `adj : L ⊣ R` with `R` exact, this is the map
`Ext^n (L.obj A) B →+ Ext^n A (R.obj B)` obtained by applying `R` and precomposing with the
unit of the adjunction. For `n = 0` it is `adj.homEquiv`, see `Adjunction.extAddHom_mk₀`. -/
noncomputable def extAddHom (A : D) (B : C) (n : ℕ) :
    Ext.{w} (L.obj A) B n →+ Ext.{w'} A (R.obj B) n where
  toFun e := (Ext.mk₀ (adj.unit.app A)).comp (e.mapExactFunctor R) (zero_add n)
  map_zero' := by simp
  map_add' e e' := by simp [Ext.comp_add]

lemma extAddHom_apply (A : D) (B : C) (n : ℕ) (e : Ext.{w} (L.obj A) B n) :
    adj.extAddHom A B n e = (Ext.mk₀ (adj.unit.app A)).comp (e.mapExactFunctor R) (zero_add n) :=
  rfl

/-- In degree `0`, the map `Adjunction.extAddHom` is the bijection of the adjunction. -/
lemma extAddHom_mk₀ (A : D) (B : C) (f : L.obj A ⟶ B) :
    adj.extAddHom A B 0 (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv A B f) := by
  rw [extAddHom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, adj.homEquiv_unit]

/-- `Adjunction.extAddHom` is natural in the second variable. -/
lemma extAddHom_comp_mk₀ (A : D) {B B' : C} (g : B ⟶ B') (n : ℕ) (e : Ext.{w} (L.obj A) B n) :
    adj.extAddHom A B' n (e.comp (Ext.mk₀ g) (add_zero n)) =
      (adj.extAddHom A B n e).comp (Ext.mk₀ (R.map g)) (add_zero n) := by
  rw [extAddHom_apply, extAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- `Adjunction.extAddHom` commutes with the connecting map of a short exact sequence. -/
lemma extAddHom_comp_extClass (A : D) {S : ShortComplex C} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (e : Ext.{w} (L.obj A) S.X₃ n₀) :
    adj.extAddHom A S.X₁ n₁ (e.comp hS.extClass h) =
      (adj.extAddHom A S.X₃ n₀ e).comp (hS.map_of_exact R).extClass h := by
  rw [extAddHom_apply, extAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc _ _ _ (zero_add n₀) h (by lia)]

attribute [local instance] Ext.subsingleton_of_injective in
/-- Let `adj : L ⊣ R` be an adjunction between abelian categories, with `R` exact and `L`
preserving monomorphisms. Then applying `R` and precomposing with the unit identifies
`Ext^n (L.obj A) B` with `Ext^n A (R.obj B)`. -/
lemma extAddHom_bijective [L.PreservesMonomorphisms] [EnoughInjectives C] (A : D) (B : C)
    (n : ℕ) : Function.Bijective (adj.extAddHom A B n) := by
  have hinj : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing B with
  | zero =>
    constructor
    · intro e e' he
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (L.obj A) B).2 e
      obtain ⟨f', rfl⟩ := (Ext.mk₀_bijective (L.obj A) B).2 e'
      rw [adj.extAddHom_mk₀, adj.extAddHom_mk₀] at he
      exact congrArg _ ((adj.homEquiv A B).injective ((Ext.mk₀_bijective A (R.obj B)).1 he))
    · intro e
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A (R.obj B)).2 e
      exact ⟨Ext.mk₀ ((adj.homEquiv A B).symm g), by rw [adj.extAddHom_mk₀, Equiv.apply_symm_apply]⟩
  | succ n hn =>
    let I : InjectivePresentation B := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hI : Injective S.X₂ := I.injective
    have hRI : Injective (S.map R).X₂ := hinj.injective_obj hI
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (adj.extAddHom A S.X₂ n) (adj.extAddHom A S.X₃ n) (adj.extAddHom A S.X₁ (n + 1))
      (by ext e; dsimp; exact (adj.extAddHom_comp_mk₀ A S.g n e).symm)
      (by ext e; dsimp; exact (adj.extAddHom_comp_extClass A hS rfl e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj A) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁ (by subsingleton) rfl)

/-- Let `adj : L ⊣ R` be an adjunction between abelian categories, with `R` exact and `L`
preserving monomorphisms. Then applying `R` and precomposing with the unit identifies
`Ext^n (L.obj A) B` with `Ext^n A (R.obj B)`. -/
@[simps! apply]
noncomputable def extAddEquiv [L.PreservesMonomorphisms] [EnoughInjectives C] (A : D) (B : C)
    (n : ℕ) : Ext.{w} (L.obj A) B n ≃+ Ext.{w'} A (R.obj B) n :=
  AddEquiv.ofBijective (adj.extAddHom A B n) (adj.extAddHom_bijective A B n)

end Adjunction

end CategoryTheory
