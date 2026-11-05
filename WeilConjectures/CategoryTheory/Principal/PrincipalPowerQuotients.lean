/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Principal-power quotient ring sheaves

Source: blueprint, integral criterion reductions, second paragraph; Stacks Project,
Sites, Section 00YR
(blueprint: def-pe-principal-power-ring-quotients).
The quotient is the sheafification of the actual sectionwise quotient rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r
open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (B : Sheaf J CommRingCat.{r}) (t : (B.obj ⋙ forget CommRingCat.{r}).sections)

variable [HasSheafify J CommRingCat.{r}]

attribute [irreducible] principalPowerRingQuotient

end CategoryTheory
