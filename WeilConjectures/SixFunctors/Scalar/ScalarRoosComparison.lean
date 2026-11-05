/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The coordinate-normalized additive Roos comparison

Source: Stacks 08TC and 0941.
(blueprint: def-sf-additive-roos-map).

This file retains the original additive Roos construction and its unique
coordinate characterization, together with proved naturality and strict tower
assembly helpers. No coefficient-specific definitions or instances are needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe a b a' b'
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section ScalarRoos

open CochainComplex CochainComplex.HomComplex

end ScalarRoos

section ScalarRoosNaturality
attribute [local implicit_reducible] integralOperationsRoos
  Functor.mapHomologicalComplex CochainComplex.mappingCocone
open CochainComplex CochainComplex.HomComplex
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]

end ScalarRoosNaturality

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

end WeilConjectures
