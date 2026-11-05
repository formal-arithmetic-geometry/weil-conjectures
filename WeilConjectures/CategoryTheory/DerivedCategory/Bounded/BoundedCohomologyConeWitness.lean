/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Finite cohomology cone witnesses
Source: Stacks Project, Derived Categories, Tags 08J5 and 0118; the Complexes paragraph
of blueprint sk-cor-coefficient-heart-ii-generation.
(blueprint: lem-sfb-bounded-cohomology-cone-witness)
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace DerivedCategory

open CategoryTheory.Pretriangulated

end DerivedCategory
