/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # K-flat cone presentations of distinguished triangles

Source: Stacks Project, Tag 06Y4; Mathlib's cone presentation of
triangles in the derived category.
(blueprint: lem-pc-kflat-cone-triangle-presentation).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

end ModuleCat
