/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# `Ext`-groups as morphisms in the bounded below derived category

For objects `X` and `Y` of an abelian category `C`, morphisms `X[0] ⟶ Y[0][n]` in the bounded
below derived category `DerivedCategory.Plus C` are the `Ext`-groups `Ext^n(X, Y)`
(`DerivedCategory.Plus.singleFunctorHomEquivExt`): the bounded below derived category is a full
subcategory of `DerivedCategory C`, stable under shifts.
-/

@[expose] public section

universe w w' v u

open CategoryTheory

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C] [HasExt.{w} C]

/-- Morphisms `X[0] ⟶ Y[0][n]` in the bounded below derived category are the elements of
`Ext^n(X, Y)`. -/
noncomputable def singleFunctorHomEquivExt (X Y : C) (n : ℕ) :
    ((singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) ≃
      Abelian.Ext.{w} X Y n :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans
    ((Iso.homCongr (Iso.refl _) ((Plus.ι.commShiftIso (n : ℤ)).app _)).trans
      Abelian.Ext.homEquiv.symm)

end DerivedCategory.Plus
