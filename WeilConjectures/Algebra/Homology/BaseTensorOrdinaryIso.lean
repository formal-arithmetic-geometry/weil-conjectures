/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryDegreeIso

/-!
# Ordinary base tensor associativity

Source: Stacks Project, Tags 06Y6 and 08IB
(blueprint: lem-pc-base-tensor-ordinary-iso).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

end ModuleCat
