/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Comparing `Ext` along an exact functor and a corepresenting morphism

Let `F : C ⥤ D` be an exact functor between abelian categories, `E₀ : C`, `Z : D` and
`u : Z ⟶ F E₀` a morphism such that `x ↦ u ≫ F x` is a bijection `(E₀ ⟶ Y) ≃ (Z ⟶ F Y)` for every
`Y : C` (for instance the unit of an adjunction `G ⊣ F` with `E₀ = G Z`). Pushing an `Ext`-class
forward along `F` and precomposing with `u` gives maps

```
  Ext E₀ Y n ──F──▶ Ext (F E₀) (F Y) n ──u──▶ Ext Z (F Y) n
```

(`CategoryTheory.Abelian.Ext.mapExactFunctorPrecomp`). If `C` has enough injectives and
`Ext Z (F I) (q + 1) = 0` for every injective `I`, these maps are bijective in all degrees
(`CategoryTheory.Abelian.Ext.bijective_mapExactFunctorPrecomp`): this is the comparison of the
derived functors of `Hom(E₀, -)` and of `Hom(Z, F -)`, proven by dimension shifting.

They are compatible with the composition of `Ext`-classes
(`CategoryTheory.Abelian.Ext.mapExactFunctorPrecomp_comp`).
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The map `Ext E₀ Y n ⟶ Ext Z (F Y) n`: push forward along `F`, then precompose with
`u : Z ⟶ F E₀`. -/
noncomputable def mapExactFunctorPrecomp {E₀ : C} {Z : D} (u : Z ⟶ F.obj E₀) (Y : C) (n : ℕ) :
    Ext E₀ Y n →+ Ext Z (F.obj Y) n :=
  ((mk₀ u).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom E₀ Y n)

lemma mapExactFunctorPrecomp_apply {E₀ : C} {Z : D} (u : Z ⟶ F.obj E₀) {Y : C} {n : ℕ}
    (x : Ext E₀ Y n) :
    mapExactFunctorPrecomp F u Y n x = (mk₀ u).comp (x.mapExactFunctor F) (zero_add n) :=
  rfl

/-- The comparison is compatible with the composition of `Ext`-classes. -/
lemma mapExactFunctorPrecomp_comp {E₀ : C} {Z : D} (u : Z ⟶ F.obj E₀) {Y Y' : C} {a b c : ℕ}
    (x : Ext E₀ Y a) (y : Ext Y Y' b) (h : a + b = c) :
    mapExactFunctorPrecomp F u Y' c (x.comp y h) =
      (mapExactFunctorPrecomp F u Y a x).comp (y.mapExactFunctor F) h := by
  rw [mapExactFunctorPrecomp_apply, mapExactFunctorPrecomp_apply, mapExactFunctor_comp,
    comp_assoc _ _ _ (zero_add a) h (by lia)]

lemma mapExactFunctorPrecomp_mk₀ {E₀ : C} {Z : D} (u : Z ⟶ F.obj E₀) {Y : C} (x : E₀ ⟶ Y) :
    mapExactFunctorPrecomp F u Y 0 (mk₀ x) = mk₀ (u ≫ F.map x) := by
  rw [mapExactFunctorPrecomp_apply, mapExactFunctor_mk₀, mk₀_comp_mk₀]

attribute [local instance] subsingleton_of_injective in
/-- **The comparison is bijective.** If `x ↦ u ≫ F x` is a bijection `(E₀ ⟶ Y) ≃ (Z ⟶ F Y)` for
every `Y`, `C` has enough injectives and `Ext Z (F I) (q + 1) = 0` for every injective `I`, then
`Ext E₀ Y n ⟶ Ext Z (F Y) n` is bijective. -/
theorem bijective_mapExactFunctorPrecomp [EnoughInjectives C] {E₀ : C} {Z : D}
    (u : Z ⟶ F.obj E₀) (hu : ∀ Y : C, Function.Bijective fun x : E₀ ⟶ Y ↦ u ≫ F.map x)
    (hI : ∀ (I : C) [Injective I] (q : ℕ), Subsingleton (Ext Z (F.obj I) (q + 1))) (Y : C)
    (n : ℕ) : Function.Bijective (mapExactFunctorPrecomp F u Y n) := by
  induction n generalizing Y with
  | zero =>
    have h : mapExactFunctorPrecomp F u Y 0 =
        (fun x : E₀ ⟶ Y ↦ mk₀ (u ≫ F.map x)) ∘ (Equiv.ofBijective _ (mk₀_bijective E₀ Y)).symm := by
      funext x
      obtain ⟨y, rfl⟩ := (mk₀_bijective E₀ Y).2 x
      rw [Function.comp_apply, Equiv.ofBijective_symm_apply_apply, mapExactFunctorPrecomp_mk₀]
    rw [h]
    refine ((mk₀_bijective Z (F.obj Y)).comp (hu Y)).comp ?_
    exact (Equiv.ofBijective _ (mk₀_bijective E₀ Y)).symm.bijective
  | succ n hn =>
    let P : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition P.f)
    have : Injective S.X₂ := P.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel P.f }
    have hSF := hS.map_of_exact F
    have : Subsingleton (Ext Z (S.map F).X₂ (n + 1)) := hI S.X₂ n
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((mk₀ S.g).postcomp E₀ (add_zero n)) (hS.extClass.postcomp E₀ rfl)
      ((mk₀ (F.map S.g)).postcomp Z (add_zero n)) (hSF.extClass.postcomp Z rfl)
      (mapExactFunctorPrecomp F u S.X₂ n) (mapExactFunctorPrecomp F u S.X₃ n)
      (mapExactFunctorPrecomp F u S.X₁ (n + 1)) ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (covariant_sequence_exact₃' E₀ hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (covariant_sequence_exact₃' Z hSF n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ covariant_sequence_exact₁ _ hSF y₁ (by subsingleton) rfl)
    · ext x
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.flip_apply,
        bilinearComp_apply_apply]
      rw [mapExactFunctorPrecomp_comp, mapExactFunctor_mk₀]
    · ext x
      exact ((mapExactFunctorPrecomp_comp F u x hS.extClass rfl).trans
        (congrArg (fun e ↦ (mapExactFunctorPrecomp F u S.X₃ n x).comp e rfl)
          (mapExactFunctor_extClass F hS))).symm

end CategoryTheory.Abelian.Ext
