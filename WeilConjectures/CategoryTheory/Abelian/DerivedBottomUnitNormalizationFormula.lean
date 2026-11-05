/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.DerivedBottomComparison
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomCycleTransport

/-! # Canonical-cycle normalization of the specified bottom comparison

Source: Stacks Project, Tags 05TC, 08D4 and 0AVW.
(blueprint: new-lem-pc-derived-bottom-unit-normalization-formula).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
end CategoryTheory.Functor
