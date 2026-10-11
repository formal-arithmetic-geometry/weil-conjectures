/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra `R[X]` with `X` primitive

The polynomial ring `R[X]` over a commutative ring `R` is a commutative and cocommutative Hopf
algebra in which the variable is primitive: the comultiplication, counit and antipode are the
`R`-algebra homomorphisms with `Δ(X) = X ⊗ 1 + 1 ⊗ X`, `ε(X) = 0` and `S(X) = -X`. This is the
coordinate ring of the additive group `𝔾ₐ = Spec R[X]`: the three structure maps are dual to the
addition `(x, y) ↦ x + y`, the zero `0` and the negation `x ↦ -x`.

This is the special case `M = R` of the bialgebra structure `SymmetricAlgebra.instBialgebra` on
the symmetric algebra, in which every generator is primitive.

## Main definitions

- `Polynomial.instBialgebra`: the bialgebra structure on `R[X]` with `X` primitive.
- `Polynomial.instHopfAlgebra`: the Hopf algebra structure on `R[X]`, with antipode `X ↦ -X`.

## Blueprint

- `def-sc-gm-ga`: the coordinate ring `k[y]` of the additive group `𝐆_a`, with
  `m^*(y) = y ⊗ 1 + 1 ⊗ y`, `ε(y) = 0` and `i^*(y) = -y`.
-/

@[expose] public section

open TensorProduct

namespace Polynomial

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The bialgebra structure on `R[X]` in which `X` is primitive: `Δ(X) = X ⊗ 1 + 1 ⊗ X` and
`ε(X) = 0`. (blueprint: `def-sc-gm-ga`) -/
noncomputable instance instBialgebra : Bialgebra R R[X] :=
  .ofAlgHom (aeval (X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] X)) (aeval 0)
    (by
      ext
      simp [Algebra.TensorProduct.one_def, add_tmul, tmul_add]
      abel)
    (by ext; simp)
    (by ext; simp)

variable {R}

@[simp]
theorem comul_X : Coalgebra.comul (R := R) (X : R[X]) = X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] X :=
  aeval_X _

@[simp]
theorem counit_X : Coalgebra.counit (R := R) (X : R[X]) = 0 :=
  aeval_X _

@[simp]
theorem comulAlgHom_X : Bialgebra.comulAlgHom R R[X] X = X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] X :=
  comul_X

@[simp]
theorem counitAlgHom_X : Bialgebra.counitAlgHom R R[X] X = 0 :=
  counit_X

instance instIsCocomm : Coalgebra.IsCocomm R R[X] where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm R R[X] R[X]).toAlgHom.comp
        (Bialgebra.comulAlgHom R R[X]) = Bialgebra.comulAlgHom R R[X] := by
      ext
      simp [add_comm]
    exact congr(($h).toLinearMap)

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

/-- The Hopf algebra structure on `R[X]` with `X` primitive: the antipode is `X ↦ -X`.
(blueprint: `def-sc-gm-ga`) -/
noncomputable instance instHopfAlgebra : HopfAlgebra R R[X] :=
  .ofAlgHom (aeval (-X)) (by ext; simp) (by ext; simp)

variable {R}

@[simp]
theorem antipode_X : HopfAlgebra.antipode R (X : R[X]) = -X :=
  aeval_X _

end CommRing

end Polynomial
