/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.NatIso

/-! # Transport of a system composition law along fully faithful reductions

Source: Stacks 07A4 and 0941; the transport step of the reduced integral
pullback/tensor composition equation
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

Integral pullbacks and tensors are related to system pullbacks and tensors by
natural comparisons with a reduction functor. If the integral tensor comparisons
are the reductions of the system comparisons conjugated by these natural
comparisons, and the integral compositor reduces to the system compositor, then
the system composition law transports to the reduced integral composition law.
-/

@[expose] public section

open CategoryTheory

namespace WeilConjectures

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {CY : Type u₁} {CX : Type u₂} {CZ : Type u₃} {DY : Type u₄} {DX : Type u₅}
  {DZ : Type u₆} [Category.{v₁} CY] [Category.{v₂} CX] [Category.{v₃} CZ]
  [Category.{v₄} DY] [Category.{v₅} DX] [Category.{v₆} DZ]

end WeilConjectures
