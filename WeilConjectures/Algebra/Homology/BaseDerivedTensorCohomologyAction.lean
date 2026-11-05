/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionLinear
import WeilConjectures.Algebra.Homology.TensorActionOfAdditiveFunctor
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCounitLinear
import Mathlib.Algebra.Homology.Linear

/-!
# Derived base tensor cohomology with its coefficient action

Source: Stacks Project, Tags 06Y6 and 08IB
(blueprint: lem-pc-base-derived-tensor-cohomology-action).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB v} B)]

end ModuleCat
