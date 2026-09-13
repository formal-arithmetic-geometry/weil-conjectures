/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The functor `CommGrpCat ⥤ AddCommGrpCat` is an equivalence

Mathlib records the equivalence `commGroupAddCommGroupEquivalence` between commutative groups
and additive commutative groups, but does not register its functor `CommGrpCat.toAddCommGrp`
as being an equivalence. This file supplies the missing instance; it is what makes
`CommGrpCat.toAddCommGrp` a right adjoint, and hence limit-preserving.
-/

@[expose] public section

universe u

open CategoryTheory

instance : CommGrpCat.toAddCommGrp.{u}.IsEquivalence :=
  inferInstanceAs commGroupAddCommGroupEquivalence.{u}.functor.IsEquivalence
