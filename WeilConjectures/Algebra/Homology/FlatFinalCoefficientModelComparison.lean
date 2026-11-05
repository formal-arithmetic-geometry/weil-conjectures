/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import Mathlib.Algebra.Category.ModuleCat.Descent

import WeilConjectures.Algebra.Homology.FlatIteratedScalarExtensionHomologySquare

/-! # Flat change of the final coefficient ring of a tensor cohomology model

Source: Stacks Project, Tags 06Y6 and 00HD.
(blueprint: lem-pc-flat-final-coefficient-model-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace ModuleCat

end ModuleCat
