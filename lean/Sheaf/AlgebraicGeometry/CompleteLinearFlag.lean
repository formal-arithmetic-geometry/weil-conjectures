/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.RingTheory.Grassmannian

/-! # Complete flags in a finite free module

Source: Milne, Algebraic Groups (2017), preceding Proposition 7.29, printed p.146
(blueprint: def-sfb-complete-linear-flag).

The quotient convention for Mathlib's Grassmannian means that the i-th submodule
has quotient locally free of rank n-i. In a finite free ambient module this is
exactly a locally free direct summand of rank i. Submodules, rather than bases or
isomorphism classes of abstract modules, are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- Complete flags of embedded locally direct summands in A^n. The quotient is
finite projective of constant rank n-i, equivalently the submodule is locally a
free direct summand of rank i. The lifted index only matches the universe of GL.
Source: Milne, preceding Proposition 7.29, printed p.146
(blueprint: def-sfb-complete-linear-flag). -/
structure CompleteLinearFlag (A : Type u) [CommRing A] (n : ℕ) where
  step (i : Fin (n + 1)) :
    Module.Grassmannian A (ULift.{u} (Fin n) → A) (n - i.val)
  monotone : Monotone (fun i ↦ (step i).toSubmodule)
  zero : (step 0).toSubmodule = ⊥
  last : (step (Fin.last n)).toSubmodule = ⊤

/-- The submodule obtained by scalar extension is the B-span of coefficientwise
images. This is the image of B tensor_A N in B^n, and requires no flatness.
Source: Milne, flag functor preceding Proposition 7.29, printed p.146
(blueprint: def-sfb-complete-linear-flag). -/
def completeFlagScalarImage {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {n : ℕ} (N : Submodule A (ULift.{u} (Fin n) → A)) :
    Submodule B (ULift.{u} (Fin n) → B) :=
  Submodule.span B
    ((fun (v : ULift.{u} (Fin n) → A) j ↦ f (v j)) ''
      (N : Set (ULift.{u} (Fin n) → A)))

end AlgebraicGeometry
