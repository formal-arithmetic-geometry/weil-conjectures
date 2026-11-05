/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteProjection
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
/-! # Compatibility and limit lift of completed constant projections

Source: Stacks Project, Modules on Sites, Tags 03EK and 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedConstantProjection

namespace CompletedConstantProjection

end CompletedConstantProjection

end AlgebraicGeometry.Scheme
