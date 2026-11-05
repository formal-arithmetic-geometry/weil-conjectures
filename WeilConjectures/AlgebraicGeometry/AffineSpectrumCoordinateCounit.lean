/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Counit compatibility in equivalence coordinates

Source: Mathlib.CategoryTheory.Adjunction.Mates, `conjugateEquiv_counit`;
Stacks Project, Tag 08HY, the counit description of base change.
(blueprint: new-affine-spectrum-coordinate-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

