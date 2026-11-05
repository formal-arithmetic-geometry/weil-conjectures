/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import Mathlib.CategoryTheory.EqToHom

/-! # Natural isomorphisms between prescribed raw bilinear scalar extensions

Source: the existing rawBilinearIso_existsUnique proof in DerivedPullbackTensorHom.
(blueprint: lem-weil-raw-bilinear-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe r s u₁ v₁ u₂ v₂
open TensorProduct CategoryTheory

namespace WeilConjectures.RawBilinearScalarComparison

attribute [local irreducible] ScalarLocalization.composition

end WeilConjectures.RawBilinearScalarComparison
