/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionInflation
public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Grothendieck structure and exact restriction of internal sheaf actions

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-formulated categorical input
(blueprint: lem-sfb-sheaf-action-grothendieck-inflation).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]
  {K L : Cᵒᵖ ⥤ GrpCat.{u}} {R : Cᵒᵖ ⥤ RingCat.{u}}

end CategoryTheory.InternalActionSite
