/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Stupid Colimit Instance Needed for Total Complex

-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace CategoryTheory

/-- The fiber over `j` of the total degree map `(p, q) ↦ p + q` on `ℤ × ℤ` is in
bijection with `ℤ`, via `p ↦ (p, j - p)`. -/
def ComplexShape.πUpIntFiberEquiv (j : ℤ) :
    ℤ ≃ ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}) where
  toFun p := ⟨(p, j - p), show p + (j - p) = j by omega⟩
  invFun x := x.1.1
  left_inv p := rfl
  right_inv := fun ⟨⟨p, q⟩, h⟩ => by
    have h' : p + q = j := h
    obtain rfl : q = j - p := by omega
    rfl

instance hasColimitsOfShape_discrete_π_up_int {C : Type u} [Category.{v} C]
    [HasColimitsOfShape (Discrete ℤ) C] (j : ℤ) :
    HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) C :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (ComplexShape.πUpIntFiberEquiv j))

end CategoryTheory
