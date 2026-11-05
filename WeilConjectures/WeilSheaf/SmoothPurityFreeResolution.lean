/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointBijective

/-!
# Universal arrows for triangulated functors of derived Weil objects

The free resolution argument applies to every additive triangulated functor. In
particular it applies to a compactly supported direct image, which is a composite
of an exact extension by zero and a right derived pushforward.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C]
  (RW : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
  [RW.Additive] [RW.CommShift ℤ] [RW.IsTriangulated]

end CategoryTheory.Endofunctor.IsoAlgebra
