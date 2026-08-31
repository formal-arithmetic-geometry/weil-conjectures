/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Precomposition with an isomorphism on `Ext`-groups

- `CategoryTheory.Abelian.Ext.precompAddEquiv`: an isomorphism `e : X ≅ X'` induces an
  isomorphism `Ext X' Z n ≃+ Ext X Z n` of `Ext`-groups by precomposition.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X X' : C}

/-- An isomorphism `e : X ≅ X'` induces an isomorphism `Ext X' Z n ≃+ Ext X Z n` of
`Ext`-groups by precomposition with `e`. -/
@[simps! apply]
noncomputable def precompAddEquiv (e : X ≅ X') (Z : C) (n : ℕ) : Ext X' Z n ≃+ Ext X Z n where
  __ := (Ext.mk₀ e.hom).precomp Z (zero_add n)
  invFun := (Ext.mk₀ e.inv).precomp Z (zero_add n)
  left_inv α := by simp [Ext.mk₀_comp_mk₀_assoc]
  right_inv α := by simp [Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory.Abelian.Ext
