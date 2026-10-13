/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Tor bounds for polynomial modules
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7, pp. 101–102.
(blueprint: lem-pc-polynomial-tor-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Polynomial extension increases flat dimension by at most the number of variables.
Source: Weibel, Theorem 4.3.7, pp. 101–102, its exact-sequence argument applied to Tor.
Proof: for one variable t, resolve a module L by the canonical exact sequence
0 → A[t] tensor_A L → A[t] tensor_A L → L → 0, where the first map sends
f tensor x to tf tensor x - f tensor tx, and the last map evaluates the action.
Injectivity follows by comparing the highest coefficient; the kernel of evaluation
is the image by recursively removing highest coefficients. The induced modules
have Tor_i over A[t] equal to Tor_i over A against the restricted test module:
extend an A-projective resolution, using freeness of A[t] over A, and tensor
associativity. The Tor long exact sequence therefore gives vanishing above d+1.
Iterate this construction over n variables, identifying the iterated polynomial
ring with MvPolynomial (Fin n) A. At n=0 use its canonical ring equivalence with A.
No finiteness or Noetherian hypothesis is needed. The argument includes the zero
module and d=0, because it only uses positive degrees above the indicated bounds.
(blueprint: lem-pc-polynomial-tor-bound). -/
theorem polynomial_tor_bound_of_base_tor_bound
    {A : Type u} [CommRing A]
    (n : ℕ) (M : ModuleCat.{u} (MvPolynomial (Fin n) A)) (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} A, ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj
        ((restrictScalars MvPolynomial.C).obj M)).obj N)) :
    ∀ N : ModuleCat.{u} (MvPolynomial (Fin n) A), ∀ i : ℕ, d + n < i →
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin n) A)) i).obj M).obj N) := by
  sorry

end ModuleCat
