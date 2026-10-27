module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Orthogonal subspaces and cartesian restriction of scalars

Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Proposition 2.4.1/5,
printed p. 96, and Lemma 2.4.3/4, printed p. 100
(blueprint: lem-trf-cartesian-subspace-scalar-tower).

The norms are unbundled nonnegative real functions, exactly as in the node.
Orthogonality is written as a finite supremum equality; the empty supremum is zero.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped BigOperators NNReal

namespace Module

/-- Every subspace of a space with a finite orthogonal basis has a finite orthogonal basis.
Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Proposition 2.4.1/5, p. 96
(blueprint: lem-trf-cartesian-subspace-scalar-tower), clause (1).

Proof: scalar homogeneity and the absolute-value identity `|-1| = 1` give `N(-x) = N(x)`.
Apply lem-trf-cartesian-subspace with the given norm and orthogonal basis to the arbitrary
submodule `U`. Its conclusion is the displayed finite orthogonal basis, including the empty
basis when `U = 0`. No completeness is used. -/
theorem exists_orthogonal_basis_subspace
    {K : Type u} [Field K] (abv : AbsoluteValue K ℝ≥0)
    (h_nontrivial : abv.IsNontrivial) (h_nonarch : IsNonarchimedean abv)
    {V : Type v} [AddCommGroup V] [Module K V] (N : V → ℝ≥0)
    (h_definite : ∀ x : V, N x = 0 ↔ x = 0)
    (h_ultra : IsNonarchimedean N)
    (h_smul : ∀ (a : K) (x : V), N (a • x) = abv a * N x)
    (n : ℕ) (b : Module.Basis (Fin n) K V)
    (h_orthogonal : ∀ a : Fin n → K,
      N (∑ i, a i • b i) = Finset.univ.sup (fun i ↦ abv (a i) * N (b i)))
    (U : Submodule K V) :
    ∃ (m : ℕ) (c : Module.Basis (Fin m) K U), ∀ a : Fin m → K,
      N (↑(∑ i, a i • c i) : V) =
        Finset.univ.sup (fun i ↦ abv (a i) * N (↑(c i) : V)) := by
  sorry

/-- Cartesianity is preserved by restriction along a cartesian isometric field extension.
Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Lemma 2.4.3/4, p. 100
(blueprint: lem-trf-cartesian-subspace-scalar-tower), clause (2).

Proof: fix a finite-dimensional `K`-subspace `U` of `W`; use the empty basis if it is zero.
Choose a finite `K`-basis `u_j` and an orthogonal `F`-basis `e_i` of their finite-dimensional
`F`-span. Write `u_j = ∑ i, c_ij • e_i`. For each `i`, the `K`-span of the finitely many
`c_ij` in `F` has an orthogonal `K`-basis `a_il` by `h_extension`. The vectors `a_il • e_i`
span a finite `K`-space `V₀` containing `U`. Orthogonality first of the `e_i`, then of each
coefficient basis, and `h_isometric` give
`N(∑ i,l, d_il • (a_il • e_i)) = max i,l, abvK(d_il) * N(a_il • e_i)`.
Every basis vector has positive norm, so this identity also proves linear independence.
Thus these vectors form a finite orthogonal basis of `V₀`. Its restricted norm is definite,
ultrametric, symmetric, and `K`-homogeneous by `h_isometric` and the scalar tower.
Apply lem-trf-cartesian-subspace to `U` inside `V₀`. Empty coefficient blocks contribute zero,
so the argument includes all zero-dimensional cases. -/
theorem exists_orthogonal_basis_restrictScalars
    {K : Type u} [Field K] (abvK : AbsoluteValue K ℝ≥0)
    (hK_nontrivial : abvK.IsNontrivial) (hK_nonarch : IsNonarchimedean abvK)
    {F : Type w} [Field F] [Algebra K F] (abvF : AbsoluteValue F ℝ≥0)
    (hF_nontrivial : abvF.IsNontrivial) (hF_nonarch : IsNonarchimedean abvF)
    (h_isometric : ∀ a : K, abvF (algebraMap K F a) = abvK a)
    (h_extension : ∀ (A : Submodule K F) [FiniteDimensional K A],
      ∃ (n : ℕ) (b : Module.Basis (Fin n) K A), ∀ a : Fin n → K,
        abvF (↑(∑ i, a i • b i) : F) =
          Finset.univ.sup (fun i ↦ abvK (a i) * abvF (↑(b i) : F)))
    {W : Type t} [AddCommGroup W] [Module F W] [Module K W] [IsScalarTower K F W]
    (N : W → ℝ≥0) (h_definite : ∀ x : W, N x = 0 ↔ x = 0)
    (h_ultra : IsNonarchimedean N)
    (h_smul : ∀ (a : F) (x : W), N (a • x) = abvF a * N x)
    (h_space : ∀ (M : Submodule F W) [FiniteDimensional F M],
      ∃ (n : ℕ) (b : Module.Basis (Fin n) F M), ∀ a : Fin n → F,
        N (↑(∑ i, a i • b i) : W) =
          Finset.univ.sup (fun i ↦ abvF (a i) * N (↑(b i) : W)))
    (U : Submodule K W) [FiniteDimensional K U] :
    ∃ (m : ℕ) (c : Module.Basis (Fin m) K U), ∀ a : Fin m → K,
      N (↑(∑ i, a i • c i) : W) =
        Finset.univ.sup (fun i ↦ abvK (a i) * N (↑(c i) : W)) := by
  sorry

end Module
