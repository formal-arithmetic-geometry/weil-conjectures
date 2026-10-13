/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Tor bound for adjoining a single variable
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7, pp. 101–102.
(blueprint: lem-pc-polynomial-successor-tor-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Adjoining one variable raises a Tor bound by at most one.
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7, pp. 101–102.
Proof: put R = A[t_0,...,t_{n-1}] and S = R[t_n], using the coefficient inclusion
`rename Fin.castSucc`. For L = M restricted to R, let E = S tensor_R L. The maps
on E given by delta(f tensor m) = t_n f tensor m - f tensor (t_n m) and
aug(f tensor m) = f m are S-linear and form 0 -> E -> E -> M -> 0.
To see delta is injective, expand an element as sum t_n^j tensor m_j: its top
coefficient in delta is the top m_j. To see ker aug = im delta, subtract delta
of the term one degree lower to eliminate the highest coefficient, then descend
until the remaining degree-zero coefficient is zero by aug. Aug is surjective
since aug(1 tensor m) = m. Freeness of S over R means extension of an R-projective
resolution of L is an S-projective resolution of E. Tensor associativity, and
exactness of restriction of scalars, identify restricted Tor_i^S(E,N) with
Tor_i^R(L,N restricted to R). Hence both copies of E have zero Tor above d.
For i > d+1, the exact segment Tor_i^S(E,N) -> Tor_i^S(M,N) ->
Tor_{i-1}^S(E,N) has zero ends, proving the conclusion. This argument also covers
n=0, d=0, the zero module, and the zero ring; no degree of a nonzero scalar
polynomial and no domain assumption is used.
(blueprint: lem-pc-polynomial-successor-tor-bound) -/
theorem polynomial_successor_tor_bound
    {A : Type u} [CommRing A]
    (n : ℕ) (M : ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A)) (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} (MvPolynomial (Fin n) A), ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin n) A)) i).obj
        ((restrictScalars (MvPolynomial.rename Fin.castSucc).toRingHom).obj M)).obj N)) :
    ∀ N : ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A), ∀ i : ℕ, d + 1 < i →
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A)) i).obj M).obj N) := by
  sorry

end ModuleCat
