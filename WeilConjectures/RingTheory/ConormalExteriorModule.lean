/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Exterior powers of the conormal module

The exterior powers `⋀^n (I/I²)` of the conormal module of an ideal `I ⊆ A`, regarded as
`A`-modules.

## References

* [Stacks, Tag 062I]
-/

@[expose] public section
set_option autoImplicit false
universe u
/-- The exterior power `⋀^n (I/I²)` over `A/I`, regarded as a module over the ambient
ring `A`.
-/
noncomputable abbrev conormalExteriorModule (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent))

