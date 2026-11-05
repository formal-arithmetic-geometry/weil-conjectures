/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Passing from Hom comparison to Isom comparison by inverse pairs

Source: Stacks Project, Tag 00WJ, exactness of set sheafification, applied to inverse pairs.
(blueprint: lem-weil-pbc-derived-isom-comparison-from-hom)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
variable (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B]
variable (A D G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

end CategoryTheory

namespace AlgebraicGeometry.Scheme

attribute [local instance] preservesFiniteLimits_proEtaleSiteComparison

end AlgebraicGeometry.Scheme
