/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Mittag-Leffler modules

Source: Stacks Project, Algebra, Proposition 059M, condition (2), equivalent to
Definition 059F (blueprint: def-trf-mittag-leffler-module).
-/

@[expose] public section

universe u v w t

namespace Module

/-- An `R`-module `P` is Mittag-Leffler if tensoring with `P` maps every product of
`R`-modules injectively into the product of their tensor products. The canonical map is
`TensorProduct.piRightHom R R P Q`, sending `p ⊗ₜ q` to `fun j ↦ p ⊗ₜ q j`.
Products are dependent function types with their componentwise module structures.
The index and test-module universes are arbitrary; the latter is at least that of `R` and `P`.
Source: Stacks Project, Algebra, Proposition 059M (2), equivalent to Definition 059F
(blueprint: def-trf-mittag-leffler-module). -/
def IsMittagLeffler (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P]
    [Module R P] : Prop :=
  ∀ (J : Type w) (Q : J → Type (max u v t))
    [∀ j : J, AddCommGroup (Q j)] [∀ j : J, Module R (Q j)],
    Function.Injective (TensorProduct.piRightHom R R P Q)

end Module
