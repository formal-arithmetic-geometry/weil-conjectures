/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.CategoryTheory.SingleHomologyShiftComparison
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Shifted single-object normalization

Source: Stacks Project, Tags 05TC (2) and 05TD (3).
(blueprint: new-lem-pc-derived-single-shift-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [EnoughInjectives C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

end CategoryTheory.Functor
