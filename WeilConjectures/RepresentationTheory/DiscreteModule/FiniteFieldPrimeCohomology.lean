/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
import WeilConjectures.SixFunctors.Finite.FiniteFieldAbsoluteGalois
import WeilConjectures.RepresentationTheory.DiscreteModule.ProfiniteIntegerSmoothPrimitives

/-!
# Degree two with prime coefficients over a finite field

Source: the finite cyclic quotient argument in `sk-lem-base-field-cd-finite-field`.
(blueprint: lem-sfb-finite-field-prime-degree-two)
-/

@[expose] public section

set_option autoImplicit false

universe w u

namespace DiscreteModule

open CategoryTheory Limits Action

end DiscreteModule
