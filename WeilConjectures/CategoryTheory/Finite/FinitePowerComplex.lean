/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite power functors and complexes

Source: Stacks Project, Modules on Sites, Tag 03DB.
(blueprint: lem-pur-finite-power-complex).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A : Type u} [Category.{v} A]

section
variable [HasFiniteProducts A]

end

section
variable [Preadditive A] [HasFiniteProducts A]

end

section
variable [Abelian A]

end

section
variable [Abelian A]

end

end CategoryTheory
