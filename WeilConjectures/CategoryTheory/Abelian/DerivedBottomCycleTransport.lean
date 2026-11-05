/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Abelian.DerivedSingleShiftNormalization
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomInclusion
import WeilConjectures.CategoryTheory.Abelian.DerivedCyclesUnitNaturality

/-! # Canonical-cycle transport to the double truncation

Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-cycle-transport).
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
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

end CategoryTheory.Functor
