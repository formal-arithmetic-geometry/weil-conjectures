/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Restriction of scalars preserves finite limits

Mathlib knows that `ModuleCat.restrictScalars f` preserves any limit whose sections form a
small type, and that it is a right adjoint when both rings are commutative. This file records
the consequence that it preserves finite limits over an arbitrary ring homomorphism, where the
smallness hypothesis is automatic.
-/

@[expose] public section

universe v u₁ u₂

open CategoryTheory Limits

namespace ModuleCat

noncomputable instance preservesFiniteLimits_restrictScalars
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    PreservesFiniteLimits (restrictScalars.{v} f) where
  preservesFiniteLimits _ := ⟨fun {_} => inferInstance⟩

end ModuleCat
