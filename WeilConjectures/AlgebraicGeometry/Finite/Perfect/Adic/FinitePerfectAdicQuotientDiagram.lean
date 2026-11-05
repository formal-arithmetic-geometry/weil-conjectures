/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerExtraction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The canonical algebraic quotient diagram and compatible markings

Source: Stacks Project, Tag 09C6 and More on Algebra, Tag 09AW.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

end AlgebraicGeometry.Scheme
