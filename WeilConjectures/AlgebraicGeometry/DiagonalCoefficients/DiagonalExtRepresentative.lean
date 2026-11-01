/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Named actual Ext representative with an inverse API

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-ext-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w t
open CategoryTheory CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

/-- The actual Hom representative, kept behind a named function.
Source: Mathlib Ext.Basic (blueprint: def-diagonal-ext-representative). -/
@[irreducible] def cyclicExtRepresentative
    {C : Type u} [Category.{v} C] [Abelian C]
    [dC : HasDerivedCategory.{t} C] [eC : HasExt.{w} C]
    {X Y : C} {n : ℕ} (c : Ext.{w} X Y n) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ := c.hom

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
