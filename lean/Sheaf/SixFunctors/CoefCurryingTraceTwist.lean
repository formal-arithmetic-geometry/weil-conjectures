/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring

/-! # A trace twist on two components -/

@[expose] public section
set_option autoImplicit false

namespace WeilConjectures

/-- An isomorphism of the compact-support module does not preserve a dualizing trace.
The sum trace after the displayed invertible linear change is first projection.
Its coordinatewise multiplication pairing annihilates the nonzero second basis vector.
Source: elementary two-component test of the finite pairing in blueprint
prop-coef-integral-dualizing, proof paragraph 2
(blueprint: lem-coef-currying-trace-twist).

Proof: take e(x,y)=(x-y,y), with inverse (x,y)=(x+y,y). The sum of its coordinates
is x. For multiplication by (0,1), the first coordinate is zero, while (0,1) is
nonzero over every nontrivial ring. This works in characteristic two as well. -/
theorem coefCurrying_trace_twist (A : Type*) [CommRing A] [Nontrivial A] :
    ∃ e : (A × A) ≃ₗ[A] (A × A),
      (∀ x : A × A, (e x).1 + (e x).2 = x.1) ∧
      (0, 1) ≠ (0 : A × A) ∧
      ∀ h : A × A,
        (e (h.1 * 0, h.2 * 1)).1 + (e (h.1 * 0, h.2 * 1)).2 = 0 := by
  let e : (A × A) ≃ₗ[A] (A × A) :=
    { toFun := fun x ↦ (x.1 - x.2, x.2)
      invFun := fun x ↦ (x.1 + x.2, x.2)
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp
      map_add' := by
        intro x y
        apply Prod.ext
        · dsimp
          ring
        · rfl
      map_smul' := by
        intro a x
        apply Prod.ext
        · simp [smul_eq_mul, mul_sub]
        · rfl }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    exact sub_add_cancel x.1 x.2
  · intro h
    exact one_ne_zero (congrArg Prod.snd h)
  · intro h
    change (h.1 * 0 - h.2 * 1) + h.2 * 1 = 0
    simp

end WeilConjectures
