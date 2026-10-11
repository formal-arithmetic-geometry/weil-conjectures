/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# `Ext` out of a cofiltered system and an exact functor

Let `G : C ⥤ D` be an exact functor of abelian categories, `M : J ⥤ C` a cofiltered system of
objects of `C`, `N` an object of `D` and `sⱼ : N ⟶ G (M j)` compatible morphisms. For every
object `F` of `C` the classes of `Extᵠ(M j, F)` give classes of `Extᵠ(N, G F)`, by applying `G`
and pulling back along `sⱼ` (`CategoryTheory.Abelian.Ext.limitComparison`), compatibly with the
transition maps `Extᵠ(M j, F) ⟶ Extᵠ(M k, F)` along `k ⟶ j`.

We show that `colimⱼ Extᵠ(M j, F) ⟶ Extᵠ(N, G F)` is bijective for all `q` and `F` as soon as
this holds for `q = 0` and `G` sends injective objects of `C` to objects without higher `Ext`
out of `N`. The proof is by dimension shifting along `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective.

The typical example: `C` and `D` are the categories of étale sheaves on a scheme `S` and on a
cofiltered limit `X = lim Dⱼ` of étale `S`-schemes, `G` is the pullback, `M j` the free sheaf
on `Dⱼ` and `N` the constant sheaf on `X`; this gives the continuity of étale cohomology.

## Main definitions

- `CategoryTheory.Abelian.Ext.limitComparison`: the comparison map.
- `CategoryTheory.Abelian.Ext.CommutesWithLimit`: the elementwise bijectivity of the comparison
  maps out of the colimit.

## Main statements

- `CategoryTheory.Abelian.Ext.commutesWithLimit_of_isCofiltered`: the dimension shifting
  argument.
-/

@[expose] public section

universe w w' t t' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] {J : Type t} [Category.{t'} J] (M : J ⥤ C) (N : D)
  (s : ∀ j, N ⟶ G.obj (M.obj j))

/-- The comparison map `Extᵠ(M j, F) ⟶ Extᵠ(N, G F)`: apply the exact functor `G` and pull back
along `sⱼ : N ⟶ G (M j)`. -/
noncomputable def limitComparison (j : J) (F : C) (q : ℕ) :
    Ext.{w} (M.obj j) F q →+ Ext.{w'} N (G.obj F) q where
  toFun y := (mk₀ (s j)).comp (y.mapExactFunctor G) (zero_add q)
  map_zero' := by simp
  map_add' _ _ := by simp

lemma limitComparison_apply (j : J) (F : C) (q : ℕ) (y : Ext.{w} (M.obj j) F q) :
    limitComparison G M N s j F q y = (mk₀ (s j)).comp (y.mapExactFunctor G) (zero_add q) :=
  rfl

variable {G M N s} in
/-- The comparison maps are compatible with the transition maps. -/
lemma limitComparison_mk₀_comp (hs : ∀ {j k : J} (f : j ⟶ k), s j ≫ G.map (M.map f) = s k)
    {j k : J} (f : k ⟶ j) (F : C) (q : ℕ) (y : Ext.{w} (M.obj j) F q) :
    limitComparison G M N s k F q ((mk₀ (M.map f)).comp y (zero_add q)) =
      limitComparison G M N s j F q y := by
  rw [limitComparison_apply, limitComparison_apply, mapExactFunctor_comp, mapExactFunctor_mk₀,
    mk₀_comp_mk₀_assoc, hs]

/-- The comparison maps are natural in the second argument. -/
lemma limitComparison_comp_mk₀ (j : J) {F F' : C} (φ : F ⟶ F') (q : ℕ)
    (y : Ext.{w} (M.obj j) F q) :
    limitComparison G M N s j F' q (y.comp (mk₀ φ) (add_zero q)) =
      (limitComparison G M N s j F q y).comp (mk₀ (G.map φ)) (add_zero q) := by
  rw [limitComparison_apply, limitComparison_apply, mapExactFunctor_comp, mapExactFunctor_mk₀,
    comp_assoc_of_third_deg_zero]

/-- The comparison maps are compatible with the connecting homomorphisms. -/
lemma limitComparison_comp_extClass (j : J) {S : ShortComplex C} (hS : S.ShortExact) (q : ℕ)
    (y : Ext.{w} (M.obj j) S.X₃ q) :
    limitComparison G M N s j S.X₁ (q + 1) (y.comp hS.extClass rfl) =
      (limitComparison G M N s j S.X₃ q y).comp (hS.map_of_exact G).extClass rfl := by
  rw [limitComparison_apply, limitComparison_apply, mapExactFunctor_comp,
    mapExactFunctor_extClass]
  exact (comp_assoc _ _ _ (zero_add q) rfl (by lia)).symm

/-- `colimⱼ Extᵠ(M j, F) ⟶ Extᵠ(N, G F)` is bijective, elementwise: every class of
`Extᵠ(N, G F)` comes from some `Extᵠ(M j, F)`, and a class of `Extᵠ(M j, F)` with vanishing
image already vanishes in some `Extᵠ(M k, F)`, `k ⟶ j`. -/
def CommutesWithLimit (q : ℕ) (F : C) : Prop :=
  (∀ x : Ext.{w'} N (G.obj F) q, ∃ (j : J) (y : Ext.{w} (M.obj j) F q),
    limitComparison G M N s j F q y = x) ∧
  ∀ (j : J) (y : Ext.{w} (M.obj j) F q), limitComparison G M N s j F q y = 0 →
    ∃ (k : J) (f : k ⟶ j), (mk₀ (M.map f)).comp y (zero_add q) = 0

variable [IsCofiltered J] [EnoughInjectives C]

/-- **`Ext` out of a cofiltered system.** Let `G : C ⥤ D` be exact, `M : J ⥤ C` cofiltered and
`sⱼ : N ⟶ G (M j)` compatible. If `colimⱼ Hom(M j, F) ⟶ Hom(N, G F)` is bijective for every `F`
and `G` sends injective objects to objects without higher `Ext` out of `N`, then
`colimⱼ Extᵠ(M j, F) ⟶ Extᵠ(N, G F)` is bijective for every `q` and `F`.

The proof is by induction on `q`, dimension shifting along `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I`
injective, so that `Extᵠ⁺¹(M j, F)` is a quotient of `Extᵠ(M j, Q)` and `Extᵠ⁺¹(N, G F)` one of
`Extᵠ(N, G Q)`. -/
theorem commutesWithLimit_of_isCofiltered
    (hs : ∀ {j k : J} (f : j ⟶ k), s j ≫ G.map (M.map f) = s k)
    (h₀ : ∀ F : C, CommutesWithLimit G M N s 0 F)
    (hI : ∀ (I : C) [Injective I] (q : ℕ) (x : Ext.{w'} N (G.obj I) (q + 1)), x = 0)
    (q : ℕ) (F : C) : CommutesWithLimit G M N s q F := by
  induction q generalizing F with
  | zero => exact h₀ F
  | succ q ih =>
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hGS := hS.map_of_exact G
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := covariant_sequence_exact₁ N hGS x (hI S.X₂ q _) rfl
    obtain ⟨j, z, rfl⟩ := (ih S.X₃).1 w
    exact ⟨j, z.comp hS.extClass rfl, limitComparison_comp_extClass G M N s j hS q z⟩
  · obtain ⟨z, rfl⟩ := covariant_sequence_exact₁ _ hS y (eq_zero_of_injective _) rfl
    obtain ⟨w, hw⟩ := covariant_sequence_exact₃ N hGS _ rfl
      ((limitComparison_comp_extClass G M N s j hS q z).symm.trans hy)
    cases q with
    | zero =>
      obtain ⟨k, w', rfl⟩ := (ih S.X₂).1 w
      let l := IsCofiltered.min j k
      let a : l ⟶ j := IsCofiltered.minToLeft j k
      let b : l ⟶ k := IsCofiltered.minToRight j k
      have hc : limitComparison G M N s l S.X₃ 0
          ((mk₀ (M.map a)).comp z (zero_add 0) -
            (mk₀ (M.map b)).comp (w'.comp (mk₀ S.g) (add_zero 0)) (zero_add 0)) = 0 := by
        rw [map_sub, limitComparison_mk₀_comp hs, limitComparison_mk₀_comp hs,
          limitComparison_comp_mk₀, ← hw]
        exact sub_self _
      obtain ⟨m, f, hf⟩ := (ih S.X₃).2 l _ hc
      refine ⟨m, f ≫ a, ?_⟩
      rw [sub_eq_add_neg, comp_add, comp_neg, ← sub_eq_add_neg, sub_eq_zero,
        mk₀_comp_mk₀_assoc, mk₀_comp_mk₀_assoc, ← M.map_comp, ← M.map_comp] at hf
      calc (mk₀ (M.map (f ≫ a))).comp (z.comp hS.extClass rfl) (zero_add _)
          = ((mk₀ (M.map (f ≫ a))).comp z (zero_add 0)).comp hS.extClass rfl :=
            (comp_assoc _ _ _ _ _ (by lia)).symm
        _ = ((mk₀ (M.map (f ≫ b))).comp (w'.comp (mk₀ S.g) (add_zero 0)) (zero_add 0)).comp
            hS.extClass rfl := by rw [hf]
        _ = 0 := by
          rw [comp_assoc_of_second_deg_zero, comp_assoc_of_second_deg_zero, hS.comp_extClass,
            comp_zero, comp_zero]
    | succ q =>
      rw [hI S.X₂ q w, zero_comp] at hw
      obtain ⟨k, f, hf⟩ := (ih S.X₃).2 j z hw.symm
      refine ⟨k, f, ?_⟩
      calc (mk₀ (M.map f)).comp (z.comp hS.extClass rfl) (zero_add _)
          = ((mk₀ (M.map f)).comp z (zero_add _)).comp hS.extClass rfl :=
            (comp_assoc _ _ _ _ _ (by lia)).symm
        _ = 0 := by rw [hf, zero_comp]

end CategoryTheory.Abelian.Ext
