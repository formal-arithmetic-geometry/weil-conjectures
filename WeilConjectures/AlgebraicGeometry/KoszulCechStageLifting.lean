/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Finite-stage lifting for the Koszul-to-Čech cocone

Source: Stacks, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-stage-lifting)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Clear denominators separately, then enlarge every power to a common positive exponent.

-- Prescribe all exterior-basis values in every nonpositive source degree.

end AlgebraicGeometry
