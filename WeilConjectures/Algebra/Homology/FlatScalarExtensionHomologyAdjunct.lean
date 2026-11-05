/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Cohomology of flat extension of coefficients

Source: Stacks Project, Tags 00HD and 0A1D, lemma-base-change-tensor.
(blueprint: lem-pc-flat-scalar-extension-homology-adjunct).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

end ModuleCat
