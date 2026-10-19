/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Splitting group algebras over local cyclotomic coefficient rings

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, Proposition 1.2,
printed p.138, the integral representation input cited as Serre 1978, 12 §2.3 and
13 §14.4; coefficient localization in X 1.3, printed p.139.
(blueprint: lem-per-local-cyclotomic-group-algebra-split)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MonoidAlgebra

/-- The group algebra over a prime localization of `ℤ[1/N, ζ]` splits into full matrix
algebras over that same local ring. Here `MonoidAlgebra Λ G` is the free module on
`G`, with the bilinearly extended group multiplication. The equality `hA` specifies
exactly the complex coefficient subring, and `IsLocalization.AtPrime` specifies its
prime localization without choosing a particular carrier for the fractions.

Source: ILO, Travaux de Gabber, Exposé X Proposition 1.2, printed p.138,
Serre 1978, 12 §2.3 and 13 §14.4; X 1.3, printed p.139.
(blueprint: lem-per-local-cyclotomic-group-algebra-split)

Proof:
1. Put `m = |G|`. Realize `G` as the group permuting the variables of the rational
   function field `ℚ(x_g : g ∈ G)`. Cauchy's theorem (lem-exc-finite-group-cauchy,
   using def-pc-field-extension) shows every prime divisor of `m` divides `N`.
   Thus some `N^e = m*t`, and `t/N^e` inverts `m` in `A` and in `Λ`.
2. By lem-per-cyclotomic-local-ring-dvr, `Λ` is a field or a DVR. Its fraction field
   `K` embeds in `ℂ` and contains the same primitive root. Apply
   lem-per-cyclotomic-field-brauer-splitting to obtain the positive matrix blocks
   over `K`, whose squared sizes sum to `m`. This proves the field case.
3. In each block representation `ρ_i`, the lattice `L_i = Σ_g ρ_i(g) Λ^{d_i}`
   is finite, stable, torsion-free and contains the standard lattice. By
   lem-sc-dvr-fg-torsionfree-free it has a finite basis; clearing denominators
   shows this is also a `K`-basis, of size `d_i`.
4. The lattice actions give an algebra map `f : Λ[G] → Π_i End_Λ(L_i)`.
   Its scalar extension is the field splitting conjugated by the lattice bases.
   Both sides have bases of size `m`. Write `M` for the matrix of `f`.
5. Compare regular trace pairings. On the group basis the Gram matrix `H` is
   `m` times the inversion permutation matrix, so its determinant is a unit.
   On the matrix-unit basis the integral Gram matrix is `T`. Invariance of trace
   under conjugation over `K`, and injectivity of `Λ → K`, give `H = Mᵀ T M`.
6. Hence `det(M)^2 det(T) = ±m^m` is a unit, so `det(M)` is a unit.
   By lem-weil-pbc-matrix-adjugate-identity the adjugate gives an integral inverse
   to `M`. Thus `f` is bijective; its inverse respects multiplication and scalars
   by injectivity of `f`, giving the required algebra equivalence. -/
theorem exists_algEquiv_pi_matrix_local_cyclotomic
    (N : ℕ) (hN : 0 < N) (G : Type v) [Group G] [Finite G]
    (hG : ∀ g : G, g ^ N = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (A : Subalgebra ℤ ℂ) (hA : A = Algebra.adjoin ℤ {ζ, (N : ℂ)⁻¹})
    (p : Ideal A) [p.IsPrime] (Λ : Type u) [CommRing Λ]
    [Algebra A Λ] [IsLocalization.AtPrime Λ p] :
    ∃ (r : ℕ) (d : Fin r → ℕ), 0 < r ∧ (∀ i : Fin r, 0 < d i) ∧
      Nonempty (MonoidAlgebra Λ G ≃ₐ[Λ] Π i : Fin r, Matrix (Fin (d i)) (Fin (d i)) Λ) := by
  sorry

end MonoidAlgebra
