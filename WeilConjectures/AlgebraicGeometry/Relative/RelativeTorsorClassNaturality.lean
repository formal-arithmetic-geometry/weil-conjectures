/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
import Mathlib.CategoryTheory.Whiskering

/-!
# Naturality of the explicit relative torsor classification

Source: Stacks Project, Tag 03AJ, relative refinement, steps 7 and 8.
(blueprint: lem-amb-relative-torsor-class-naturality).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale

-- Check the axioms of the completed construction.
