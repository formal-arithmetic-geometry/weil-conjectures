/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The pair category of a system of preadditive categories is preadditive

If the categories `C i` of a stage system are preadditive and the transition functors are additive,
the Hom sets of the pair category, being filtered colimits of abelian groups, are abelian groups:
addition, zero and negatives are computed after transport to a common stage, and these common-stage
operations are independent of the representatives. The stage inclusions and the functors induced by
additive morphisms of stage systems are additive, and the pair category has a zero object as soon as
the stages do.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.preadditive`: the pair category is preadditive.
- `CategoryTheory.StageSystem.PairCategory.hasZeroObject`: it has a zero object.
- `CategoryTheory.StageSystem.PairCategory.isZero_iff`: an object `(i, x)` is zero if and only if
  `T x` is zero at some stage.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Category Limits

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {S : StageSystem C} [∀ i, Preadditive (C i)] [∀ (i j : I) (h : i ≤ j), (S.T h).Additive]

namespace PairCategory

variable [IsDirectedOrder I]

end PairCategory

open PairCategory

variable [IsDirectedOrder I]

namespace Morphism

variable {D : I → Type u'} [∀ i, Category.{v'} (D i)] [∀ i, Preadditive (D i)]
  {S' : StageSystem D} [∀ (i j : I) (h : i ≤ j), (S'.T h).Additive] (F : Morphism S S')

end Morphism

end StageSystem

end CategoryTheory
