/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Right exact functors preserving monomorphisms are exact

An additive functor between abelian categories which preserves finite colimits and
monomorphisms preserves finite limits
(`CategoryTheory.Functor.preservesFiniteLimits_of_preservesMonomorphisms`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A right exact additive functor between abelian categories which preserves monomorphisms
is left exact. -/
lemma preservesFiniteLimits_of_preservesMonomorphisms (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesMonomorphisms] : PreservesFiniteLimits F :=
  have : F.PreservesHomology := preservesHomology_of_preservesMonos_and_cokernels F
  F.preservesFiniteLimits_of_preservesHomology

end CategoryTheory.Functor
