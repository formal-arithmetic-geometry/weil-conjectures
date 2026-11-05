/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# The free abelian presentation of a torsor extension

Source: Stacks Project, Lemma 02FQ, first construction.
(blueprint: lem-sc-zariski-torsor-free-extension-short-exact)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u})
variable {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (T : Torsor G)

namespace FreeExtension

end FreeExtension
end CategoryTheory.Sheaf.Torsor
