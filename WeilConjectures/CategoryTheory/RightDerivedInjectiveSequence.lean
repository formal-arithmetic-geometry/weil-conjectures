/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Derived sequence for three functors exact on injectives

Source: Stacks Project, Tags 0A50 and 0117.
(blueprint: lem-weil-pbc-right-derived-injective-sequence)
-/

@[expose] public section

universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

section
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  (A B E : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] [E.Additive]
  (a : A ⟶ B) (c : B ⟶ E)
  (hexact : ∀ (I : C), Injective I → Function.Exact (a.app I) (c.app I))

end

end CategoryTheory
