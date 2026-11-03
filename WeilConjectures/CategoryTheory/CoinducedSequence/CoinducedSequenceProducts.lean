/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Products of coinduced objects and the adjacent difference

Source: Stacks 0941, the two-term coinduced resolution.
(blueprint: lem-coef-coinduced-products-lifting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w z
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.CoinducedSequence

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : ℕ → Type w} [∀ n, Category.{z} (D n)] [∀ n, Preadditive (D n)]
  (E : ∀ n, C ⥤ D n) (R : ∀ n, D n ⥤ C)
  (a : ∀ n, E n ⊣ R n) (S : ∀ n, D n ⥤ D (n + 1))
  (t : ∀ n, E (n + 1) ⟶ E n ⋙ S n)
  [∀ n, (E n).Additive] [∀ n, (R n).Additive] [∀ n, (S n).Additive]
  [HasCountableProducts C]

/-- The first coinduced product. Source: Stacks 0941
(blueprint: lem-coef-coinduced-products-lifting). -/
def product (N : C) : C := ∏ᶜ fun n ↦ (R n).obj ((E n).obj N)

/-- The second coinduced product. Source: Stacks 0941
(blueprint: lem-coef-coinduced-products-lifting). -/
def relations (N : C) : C :=
  ∏ᶜ fun n ↦ (R (n + 1)).obj ((S n).obj ((E n).obj N))

/-- Evaluation of a map into the first product by adjunction.
Source: Stacks 0941 (blueprint: lem-coef-coinduced-products-lifting). -/
def components {M N : C} (f : M ⟶ product E R N) (n : ℕ) :
    (E n).obj M ⟶ (E n).obj N :=
  (a n).homEquiv M ((E n).obj N) |>.symm
    (f ≫ Pi.π (fun n ↦ (R n).obj ((E n).obj N)) n)

/-- The diagonal coinduced augmentation.
Source: Stacks 0941 (blueprint: lem-coef-coinduced-products-lifting). -/
def augmentation (N : C) : N ⟶ product E R N := Pi.lift fun n ↦ (a n).unit.app N

/-- The adjacent difference, specified by the coinduced adjunctions.
Source: Stacks 0941 (blueprint: lem-coef-coinduced-products-lifting). -/
def difference (N : C) : product E R N ⟶ relations E R S N :=
  Pi.lift fun n ↦ (a (n + 1)).homEquiv _ _
    ((show (E (n + 1)).obj (product E R N) ⟶ (S n).obj ((E n).obj N) from
      components E R a (𝟙 (product E R N)) (n + 1) ≫ (t n).app N) -
      (t n).app (product E R N) ≫
        (S n).map (components E R a (𝟙 (product E R N)) n))

/-- The augmentation evaluates to the original map.
Source: Stacks 0941 (blueprint: lem-coef-coinduced-products-lifting).
Proof: the product projection is the adjunction unit. Naturality in the source
and the unit inverse identity give precisely E_n(g). -/
theorem components_augmentation {M N : C} (g : M ⟶ N) (n : ℕ) :
    components E R a (g ≫ augmentation E R a N) n = (E n).map g := by
  simp only [components, augmentation, Category.assoc, limit.lift_π, Fan.mk_π_app]
  rw [(a n).homEquiv_naturality_left_symm, (a n).homEquiv_symm_unit,
    Category.comp_id]

/-- Postcomposition by the coinduced difference is the adjacent compatibility defect.
Source: Stacks 0941 (blueprint: lem-coef-coinduced-products-lifting).
Proof: project to n, transpose the result, and use naturality of adjunction,
the transition t, and the additive scalar restriction functor. -/
theorem difference_component {M N : C} (b : M ⟶ product E R N) (n : ℕ) :
    ((a (n + 1)).homEquiv _ _).symm
      (b ≫ difference E R a S t N ≫
        Pi.π (fun n ↦ (R (n + 1)).obj ((S n).obj ((E n).obj N))) n) =
    (show (E (n + 1)).obj M ⟶ (S n).obj ((E n).obj N) from
      components E R a b (n + 1) ≫ (t n).app N) -
      (t n).app M ≫ (S n).map (components E R a b n) := by
  simp only [difference, limit.lift_π, Fan.mk_π_app]
  rw [(a (n + 1)).homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Preadditive.comp_sub, ← Category.assoc]
  have h (k : ℕ) : components E R a b k =
      (E k).map b ≫ components E R a (𝟙 (product E R N)) k := by
    simp only [components, Category.id_comp]
    exact (a k).homEquiv_naturality_left_symm b _
  rw [h (n + 1), h n, Functor.map_comp]
  simp only [Category.assoc]
  have ht := (t n).naturality b
  change (E (n + 1)).map b ≫ (t n).app (product E R N) =
    (t n).app M ≫ (S n).map ((E n).map b) at ht
  rw [← Category.assoc ((E (n + 1)).map b) ((t n).app _), ht]
  simp only [Category.assoc]

/-- The augmentation is killed by the adjacent difference.
Source: Stacks 0941 (blueprint: lem-coef-coinduced-products-lifting).
Proof: the augmentation has identity components. The two terms of each
compatibility defect are therefore the same transition. -/
theorem augmentation_difference (N : C) :
    augmentation E R a N ≫ difference E R a S t N = 0 := by
  have h (n : ℕ) : components E R a (augmentation E R a N) n = 𝟙 _ := by
    simpa using components_augmentation E R a (𝟙 N) n
  apply Pi.hom_ext
  intro n
  apply ((a (n + 1)).homEquiv _ _).symm.injective
  rw [Category.assoc, difference_component E R a S t, h, h]
  simp

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end CategoryTheory.CoinducedSequence
