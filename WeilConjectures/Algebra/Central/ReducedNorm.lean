/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.JacobsonNoether
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import WeilConjectures.Mathlib.Algebra.Central.TensorProduct
public import WeilConjectures.Mathlib.RingTheory.MatrixAlgebra

/-!
# The reduced norm of a central division algebra

Let `D` be a finite-dimensional central division algebra over a field `K`. Over a separable
closure `K^sep` of `K` it becomes a matrix algebra, `K^sep ⊗[K] D ≅ M_d(K^sep)`, so
`dim_K D = d ^ 2`. The determinant of `∑ Tᵢ (1 ⊗ bᵢ)` for a `K`-basis `(bᵢ)` of `D` is a form of
degree `d` in `d ^ 2` variables, the *reduced norm*. Its coefficients are fixed by
`Gal(K^sep / K)`, since the Galois conjugate of a splitting is another splitting and the two
differ by an automorphism of `M_d(K^sep)`, which is inner. Hence the reduced norm is defined
over `K`, and it vanishes only at `0` because nonzero elements of `D` are invertible.

## Main statements

- `Algebra.IsCentral.exists_algEquiv_matrix_of_isSepClosed`: a central simple algebra splits
  over a separably closed field.
- `Algebra.IsCentral.exists_isHomogeneous_eval_ne_zero`: the reduced norm of a central division
  algebra `D` of dimension `d ^ 2` is a form of degree `d` with no nontrivial zero.
-/

@[expose] public section

open TensorProduct

namespace Algebra.IsCentral

/-- **Splitting over a separably closed field.** A finite-dimensional central simple algebra `A`
over `K` becomes a matrix algebra over every separably closed field `F` containing `K`: by
Wedderburn's theorem `F ⊗[K] A ≅ M_d(E)` for a central division algebra `E` over `F`, and
`E = F` by the Jacobson–Noether theorem.
(blueprint: `lem-sc-c1-brauer-trivial`) -/
@[stacks 03R2]
theorem exists_algEquiv_matrix_of_isSepClosed (K A F : Type*) [Field K] [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [Field F] [IsSepClosed F]
    [Algebra K F] :
    ∃ (d : ℕ) (_ : NeZero d), Nonempty (F ⊗[K] A ≃ₐ[F] Matrix (Fin d) (Fin d) F) :=
  sorry

/-- **The reduced norm.** A finite-dimensional central division algebra `D` over `K` has
dimension `d ^ 2` for some `d > 0`, and in the coordinates of a `K`-basis of `D` there is a form
of degree `d` over `K`, the reduced norm, vanishing only at `0`.
(blueprint: `lem-sc-c1-brauer-trivial`) -/
theorem exists_isHomogeneous_eval_ne_zero (K D : Type*) [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] :
    ∃ d : ℕ, 0 < d ∧ Module.finrank K D = d ^ 2 ∧
      ∃ P : MvPolynomial (Fin (Module.finrank K D)) K, P.IsHomogeneous d ∧
        ∀ y : Fin (Module.finrank K D) → K, y ≠ 0 → MvPolynomial.eval y P ≠ 0 :=
  sorry

end Algebra.IsCentral
