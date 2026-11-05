/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Saturation of the degree-zero Koszul boundaries

Source: Stacks Project, Tag 062F, the degree-zero quotient calculation.
(blueprint: lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation).
-/

@[expose] public section

universe u v

namespace ExteriorAlgebra

open scoped TensorProduct

end ExteriorAlgebra
