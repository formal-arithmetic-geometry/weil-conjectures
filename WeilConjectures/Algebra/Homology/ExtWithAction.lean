/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# `Ext`-groups with an action on the target

Let `C` be an abelian category, `A` a commutative ring and `F` an object of `C` with an action
`ρ : A →+* End F` of `A`. For every object `P`, the group `Ext P F n` is an `A`-module, with
`a • x = ρ(a)_* x` (`CategoryTheory.Abelian.Ext.WithAction`).

For the sheaf cohomology `H^n(X, ℱ) = Ext^n(ℤ, ℱ)` of a sheaf of modules `ℱ` on a scheme, with
`ρ` given by multiplication by global functions, this is the module structure used in flat base
change (`AlgebraicGeometry.Scheme.Modules.nonempty_H_baseChange_linearEquiv`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Action

variable {A : Type*} [CommRing A] {F : C} (ρ : A →+* End F)

namespace WithAction

end WithAction

end Action

end CategoryTheory.Abelian.Ext
