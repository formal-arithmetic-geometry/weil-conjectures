/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The tautological basis of the free module on a type

`ModuleCat.free R` sends a type `X` to the free `R`-module on `X`, whose tautological family of
elements is `ModuleCat.freeMk`. This file records that this family is a basis, and in particular
spans the free module.

## Main declarations

- `ModuleCat.freeBasis`: `ModuleCat.freeMk` is a basis of `(ModuleCat.free R).obj X`.
- `ModuleCat.span_range_freeMk`: `ModuleCat.freeMk` spans `(ModuleCat.free R).obj X`.
-/

@[expose] public section

universe u

namespace ModuleCat

variable (R : Type u) [Ring R] (X : Type u)

/-- **The tautological family of the free module on a type is a basis of it.** -/
noncomputable def freeBasis : Module.Basis X R ((free R).obj X) :=
  Finsupp.basisSingleOne

@[simp]
lemma coe_freeBasis : ⇑(freeBasis R X) = freeMk (R := R) (X := X) :=
  Finsupp.coe_basisSingleOne

/-- The elements `ModuleCat.freeMk x` span `(ModuleCat.free R).obj X`. -/
@[simp]
theorem span_range_freeMk :
    Submodule.span R (Set.range (freeMk (R := R) (X := X))) = ⊤ := by
  rw [← coe_freeBasis]
  exact (freeBasis R X).span_eq

end ModuleCat
