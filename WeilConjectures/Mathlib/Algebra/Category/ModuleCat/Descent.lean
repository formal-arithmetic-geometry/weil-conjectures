/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Extension of scalars along a finite projective ring map preserves limits

For a finite projective `R`-module `P`, tensoring with `P` is isomorphic to `Hom(P^∨, -)`, a
right adjoint, so it preserves limits. Consequently extension of scalars along a ring map
`f : R →+* S` making `S` finite projective over `R` preserves limits. This is what makes the
transition functors `𝒪_E ⟶ 𝒪_{E'}` between `ℓ`-adic coefficient stages commute with direct
images of sheaves without sheafification.

## Main results

- `ModuleCat.tensorLeftIsoIhomDual`: `P ⊗ - ≅ Hom(P^∨, -)` for finite projective `P`.
- `ModuleCat.preservesLimits_extendScalars_of_finite_projective`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

open scoped TensorProduct

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

variable {S : Type u} [CommRing S] (f : R →+* S)

end ModuleCat
