/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.RingedToposMorphism

/-!
# Ringed-topos morphisms with their induced module direct images

Source: Stacks Project, Sites, Definition 00XA; Modules on Sites, morphisms of ringed
topoi and pushforward of modules (blueprint: def-weil-pbc-ringed-topos-morphism).

The structural map is written on inverse-image underlying sheaves. Ring operations and
module actions are specified using generalized elements. This avoids requiring a morphism
of the presented sites: arbitrary geometric morphisms of the sheaf topoi are allowed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [instance] RingedToposMorphism.additive

end CategoryTheory

-- Universe-general extension, N0 stage-2 repair; the original interface above is retained.
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe uC vC uD vD

namespace CategoryTheory


end CategoryTheory
