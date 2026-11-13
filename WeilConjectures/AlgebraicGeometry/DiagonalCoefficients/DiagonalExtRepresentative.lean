/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Named actual Ext representative with an inverse API
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w t
open CategoryTheory CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- If `C` has small Ext groups, then morphisms between shifted single complexes are small in
the derived category.
Source: Mathlib `HasExt` and `HasSmallLocalizedShiftedHom`. -/
theorem cyclicSmallShiftedSingleHom
    {C : Type u} [Category.{v} C] [Abelian C] [h : HasExt.{w} C]
    (X Y : C) (a b : ℤ) :
    Localization.HasSmallLocalizedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (((CochainComplex.singleFunctor C 0).obj X)⟦a⟧)
      (((CochainComplex.singleFunctor C 0).obj Y)⟦b⟧) := by
  exact h X Y a b

/-- The actual Hom representative, kept behind a named function.
Source: Mathlib Ext.Basic. -/
@[irreducible] def cyclicExtRepresentative
    {C : Type u} [Category.{v} C] [Abelian C]
    [dC : HasDerivedCategory.{t} C] [eC : HasExt.{w} C]
    {X Y : C} {n : ℕ} (c : Ext.{w} X Y n) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ := c.hom

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
