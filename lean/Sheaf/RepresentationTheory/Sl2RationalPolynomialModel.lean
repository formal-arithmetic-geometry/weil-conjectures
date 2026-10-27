module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Rational polynomial models for finite-dimensional sl₂ modules

Source: Milne, Algebraic Groups, Example 22.33, p.472, and Theorem 23.70 and its proof,
pp.507–508 (blueprint: lem-sfb-sl2-rational-polynomial-model).

The degree `n` binary forms are Mathlib's `MvPolynomial.homogeneousSubmodule (Fin 2) ℚ n`.
Variable `0` is `X` and variable `1` is `Y`. The intertwining identities are written after
each direct-sum projection and the inclusion into the ambient polynomial ring. Thus no
additional choice of restricted differential operators is needed.
-/

@[expose] public section

universe u

namespace RepresentationTheory

/-- A finite-dimensional rational sl₂ module with nilpotent raising and lowering operators
and an integral eigenbasis for its Cartan operator is a finite direct sum of binary forms.
The index `r = 0` permits the empty sum. The integral eigenbasis condition is precisely
diagonalizability over ℚ with integer eigenvalues, including the zero vector space.

Source: Milne, Algebraic Groups, Example 22.33, p.472, and Theorem 23.70, pp.507–508
(blueprint: lem-sfb-sl2-rational-polynomial-model).

Proof plan, following the six steps of the DAG node:
1. Induct strongly on the dimension. For the zero space use the empty sum. Otherwise
   choose a nonzero vector `v` of maximal integral weight `m`. The relation with `H`
   makes `E v` have weight `m + 2`, so `E v = 0`.
2. Set `u_j = F^j v`. Induction using the commutators gives
   `H u_j = (m - 2*j) u_j` and `E u_(j+1) = (j+1)*(m-j) u_j`.
   Nilpotence of `F` gives a last nonzero `u_r`; applying the second formula to
   `u_(r+1) = 0` shows `m = r`, hence `m` is a natural number `n`.
3. The weights `n - 2*j` are distinct. Polynomial spectral projectors show the `u_j`
   are independent. Their span `U` is nonzero and invariant under all three operators,
   including the endpoints `E u_0 = 0` and `F u_n = 0`.
4. The polynomial and partial-derivative definitions
   [def-weil-pbc-mv-polynomial-ring, def-weil-pbc-polynomial-partial-derivative]
   give `e b_j = j*b_(j-1)`, `f b_j = (n-j)*b_(j+1)` and `h b_j = (n-2*j)*b_j`
   for `b_j = X^(n-j)*Y^j`. Map `u_j` to `(n!/(n-j)!) * b_j`.
   These nonzero factors give an isomorphism and the two consecutive-factor identities
   show that it intertwines `E`, `F`, and `H`, including `n = 0` and both endpoints.
5. Use [lem-sfb-sl2-invariant-complement] to choose a common invariant complement `C`.
   Nilpotence and the commutator identities restrict to `C`. The polynomial projectors
   onto the integral eigenspaces of `H` preserve `C`, so the restriction of `H` still
   has an integral eigenbasis. Since `U` is nonzero, `C` has smaller dimension.
6. Apply induction to `C`, append the summand for `U`, and combine the two isomorphisms.
   Invariance gives the three intertwining identities on `u + c`; the inverse is the
   sum of the two inverses. This produces a finite sum and completes the induction.
-/
theorem exists_sl2_rational_polynomial_model
    (W : Type u) [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (E F H : Module.End ℚ W)
    (hHE : H * E - E * H = (2 : ℚ) • E)
    (hHF : H * F - F * H = (-2 : ℚ) • F)
    (hEF : E * F - F * E = H)
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hH : ∃ (d : ℕ) (b : Module.Basis (Fin d) ℚ W) (weight : Fin d → ℤ),
      ∀ j : Fin d, H (b j) = (weight j : ℚ) • b j) :
    ∃ (r : ℕ) (n : Fin r → ℕ)
      (T : W ≃ₗ[ℚ] DirectSum (Fin r)
        (fun i ↦ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ (n i))),
      ∀ (w : W) (i : Fin r),
        (T (E w) i : MvPolynomial (Fin 2) ℚ) =
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.pderiv (1 : Fin 2) (T w i) ∧
        (T (F w) i : MvPolynomial (Fin 2) ℚ) =
          MvPolynomial.X (1 : Fin 2) * MvPolynomial.pderiv (0 : Fin 2) (T w i) ∧
        (T (H w) i : MvPolynomial (Fin 2) ℚ) =
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.pderiv (0 : Fin 2) (T w i) -
          MvPolynomial.X (1 : Fin 2) * MvPolynomial.pderiv (1 : Fin 2) (T w i) := by
  sorry

end RepresentationTheory
