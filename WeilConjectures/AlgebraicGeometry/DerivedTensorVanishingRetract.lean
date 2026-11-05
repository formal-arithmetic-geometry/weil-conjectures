/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.CategoryTheory.Retract
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal

/-! # Derived tensor cohomology vanishing passes to retracts

Source: Stacks Project, Cohomology of Sheaves, Tag 08CK.
(blueprint: lem-pc-derived-tensor-vanishing-retract).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
