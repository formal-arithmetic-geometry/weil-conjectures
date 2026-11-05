/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Topology.PointwiseTruncationLimitExists
import WeilConjectures.Topology.PointwiseTruncationLimitIsIso

/-! # Pointwise bounds and the derived limit of lower truncations

Source: Stacks Project, Cohomology, Tag 0D62; Derived Categories, Remark 0H72
(blueprint: lem-pc-ringed-space-pointwise-truncation-limit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

end AlgebraicGeometry.RingedSpace
