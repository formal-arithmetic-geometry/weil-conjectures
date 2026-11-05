/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Extending an ordinary homology comparison square

Source: Stacks Project, Tag 05G3, scalar extension and its adjunction;
Tag 06Y6, passage from ordinary tensor comparison to coefficient extension.
(blueprint: lem-pc-semilinear-scalar-extension-homology-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

end ModuleCat
