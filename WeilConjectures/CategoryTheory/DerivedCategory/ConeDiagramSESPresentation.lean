/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Functorial short exact presentations of mapping cones -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
variable {C : Type u} [Category C] [Abelian C]
variable {A B A' B' : CochainComplex C ℤ}

section
variable [HasDerivedCategory.{w} C]

end

