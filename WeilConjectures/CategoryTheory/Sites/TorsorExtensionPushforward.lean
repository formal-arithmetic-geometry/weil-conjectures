/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise

/-!
# Direct image of an extension and its fibre torsor

Source: Stacks Project, Cohomology of Sheaves, Tags 02UV and 02FQ, and Sheaves of Modules,
Tag 01AX (blueprint: lem-sc-torsor-h1-ext-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

end CategoryTheory.Sheaf.Torsor
