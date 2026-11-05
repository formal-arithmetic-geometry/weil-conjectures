/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.DerivedCyclesMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Abelian.DerivedSingleShiftNormalization

/-! # Derived-unit naturality on canonical cycles
Source: Stacks Project, Tags 05TC (2) and 05TD (3).
(blueprint: new-lem-pc-derived-cycles-unit-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

end CategoryTheory.Functor
