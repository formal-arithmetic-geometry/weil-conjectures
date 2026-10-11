/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Finite graded kernels over the two-variable polynomial ring

Source: blueprint `sec-picard-framework/sk-thm-picard-duality/lem-sc-p1-graded-resolution.md`,
proof, Noetherianity of successive graded kernels (blueprint: lem-sc-p1-graded-kernel-finite).
-/

universe u v w

namespace MvPolynomial

/-- The kernel of a graded surjection between finite graded `k[x₀,x₁]`-modules is finite graded.
Source: blueprint `lem-sc-p1-graded-resolution.md`, proof, successive graded kernels
(blueprint: lem-sc-p1-graded-kernel-finite).

The internal integer gradings allow arbitrary shifts, with the polynomial ring carrying its
standard total-degree grading. Finite graded generation is expressed by finite homogeneous
spanning sets. The kernel grading is the grading inherited from `F`, expressed by closure under
homogeneous components; its finite homogeneous generators are elements of `F` spanning `q.ker`.

Proof:
1. Decompose an element of the kernel into its finitely many homogeneous components. Since `q`
   preserves degrees and `M` is an internal direct sum, each image component is zero. Thus every
   homogeneous component belongs to the kernel, making it a graded submodule of `F`.
2. Apply `lem-sc-p1-graded-submodule-finite` to this graded submodule of the finitely generated
   graded module `F`. It supplies the finite homogeneous generating set for the kernel. -/
theorem graded_kernel_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (_hM : DirectSum.IsInternal ℳ)
    (_hsmulF : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : F),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → f • x ∈ ℱ ((n : ℤ) + j))
    (_hsmulM : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : M),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → f • x ∈ ℳ ((n : ℤ) + j))
    (_hfiniteF : ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (_hfiniteM : ∃ s : Set M, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (q : F →ₗ[MvPolynomial (Fin 2) k] M) (_hq : Function.Surjective q)
    (_hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    @Submodule.IsHomogeneous ℤ (AddSubgroup F) (MvPolynomial (Fin 2) k) F
      _ _ _ q.ker ℱ _ _ _ hF.chooseDecomposition ∧
    ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = q.ker := by
  sorry

end MvPolynomial
