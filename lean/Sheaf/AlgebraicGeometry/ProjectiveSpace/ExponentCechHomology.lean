/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpace.ExponentCechComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Homology of a fixed-exponent monomial Cech complex

Source: Stacks Project, Cohomology of Schemes, Tag 01XS, proof of projective-space
cohomology (blueprint: lem-pc-monomial-cech-complex-homology).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The three cohomology cases for a fixed Laurent exponent vector.

If no exponent is negative, the basis is all nonempty subsets of the simplex.
On a basis element containing vertex `0`, remove `0` to define the homotopy;
on the other basis elements it is zero. This contracts positive degrees.
The degree-zero cocycle equations equate the coefficients at every pair of vertices,
so the kernel consists of the constant coefficient copy of `A` and there are no
incoming boundaries in degree zero.

If the negative set is nonempty and proper, choose `r` outside it. Define
`h[J] = (-1) ^ card {j ∈ J | j < r} • [J \ {r}]` when `r ∈ J`, and zero otherwise.
Removal preserves the negative set and leaves a nonempty subset. In `d h + h d`,
the terms indexed by vertices other than `r` cancel with opposite signs; the
remaining term is `[J]`. Thus every cocycle is a boundary, including in degree zero,
where the incoming term is zero.

If every exponent is negative, only the full subset occurs, in degree `n`.
Every other term and every differential is zero, so its basis vector is a cycle
whose class freely generates degree-`n` cohomology and all other cohomology vanishes.
Source: Stacks, Tag 01XS (blueprint: lem-pc-monomial-cech-complex-homology). -/
theorem exponentCechComplex_homology {A : Type*} [CommRing A] (n : ℕ) (hn : 1 ≤ n)
    (e : Fin (n + 1) → ℤ) :
    (exponentCechNegativeSet n e = ∅ →
      Nonempty ((exponentCechComplex (A := A) n e).homology 0 ≃ₗ[A] A) ∧
      (∀ q : ℕ, q ≠ 0 →
        Subsingleton ((exponentCechComplex (A := A) n e).homology q))) ∧
    (exponentCechNegativeSet n e ≠ ∅ →
      exponentCechNegativeSet n e ≠ Finset.univ →
      ∀ q : ℕ, Subsingleton ((exponentCechComplex (A := A) n e).homology q)) ∧
    (exponentCechNegativeSet n e = Finset.univ →
      (∃ (z : LinearMap.ker
          ((exponentCechComplex (A := A) n e).d n (n + 1)).hom),
        ((z.1 : (exponentCechComplex (A := A) n e).X n) :
          exponentCechBasis n e n →₀ A) =
          Finsupp.single
            (⟨Finset.univ,
              ⟨by simp, Finset.subset_univ _⟩⟩ :
              exponentCechBasis n e n) 1 ∧
        ∃ f : (exponentCechComplex (A := A) n e).homology n ≃ₗ[A] A,
          f ((exponentCechComplex (A := A) n e).homologyClass (n - 1) n (n + 1)
            (by
              cases n with
              | zero => omega
              | succ m => simp [CochainComplex.prev_nat_succ m])
            (by simp) z) = 1) ∧
      (∀ q : ℕ, q ≠ n →
        Subsingleton ((exponentCechComplex (A := A) n e).homology q))) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
