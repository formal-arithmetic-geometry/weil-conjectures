/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Isomorphisms in the first variable of `Ext`

`CategoryTheory.Abelian.Ext.precompAddEquiv` is the isomorphism `Ext X' Y n ≃+ Ext X Y n`
of additive groups induced by an isomorphism `X ≅ X'`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- An isomorphism `e : X ≅ X'` induces an isomorphism `Ext X' Y n ≃+ Ext X Y n`, by
precomposition with `e`. -/
noncomputable def precompAddEquiv {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ) :
    Ext.{w} X' Y n ≃+ Ext.{w} X Y n where
  toFun := (Ext.mk₀ e.hom).precomp Y (zero_add n)
  invFun := (Ext.mk₀ e.inv).precomp Y (zero_add n)
  left_inv α := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp α (zero_add n)) (zero_add n) = α
    rw [← Ext.comp_assoc _ _ _ (add_zero 0) (zero_add n) (by lia), Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.mk₀_id_comp]
  right_inv α := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp α (zero_add n)) (zero_add n) = α
    rw [← Ext.comp_assoc _ _ _ (add_zero 0) (zero_add n) (by lia), Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.mk₀_id_comp]
  map_add' := map_add _

@[simp]
lemma precompAddEquiv_apply {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ) (α : Ext.{w} X' Y n) :
    precompAddEquiv e Y n α = (Ext.mk₀ e.hom).comp α (zero_add n) :=
  rfl

@[simp]
lemma precompAddEquiv_symm_apply {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ) (α : Ext.{w} X Y n) :
    (precompAddEquiv e Y n).symm α = (Ext.mk₀ e.inv).comp α (zero_add n) :=
  rfl

end CategoryTheory.Abelian.Ext
