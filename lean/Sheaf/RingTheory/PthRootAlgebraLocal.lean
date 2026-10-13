/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Locality of the actual algebra adjoining p-th roots

Source: Stacks Project, More on Algebra, Tag 07E5, construction of A'.
-/

@[expose] public section

universe u

namespace Algebra

/-- The actual polynomial quotient adjoining the specified p-th roots. -/
abbrev pthRootAlgebra (p n : ℕ) (A : Type u) [CommRing A] (a : Fin n → A) :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : MvPolynomial (Fin n) A) ^ p - MvPolynomial.C (a i)))

/-- Adjoining finitely many p-th roots to a local ring in characteristic p gives
another local ring, and the coefficient map is local.

Source: Stacks Project, More on Algebra, Tag 07E5, construction of A' in the proof;
Algebra, Tags 00GQ (lying over) and 0BR8 (uniqueness of primes from powers
in the coefficient image).
(blueprint: lem-weil-pbc-pth-root-algebra-local).

Proof: The monomials whose exponents are less than p form an A-basis of the quotient.
Reduction by the monic relations gives spanning, and successive division by each
monic polynomial gives independence. Thus the quotient is finite free and integral
over A. Every maximal ideal contracts to the unique maximal ideal of A. The closed
fibre is K[X_i]/(X_i^p-a_i). Each prime of this finite K-algebra is maximal, and each
residue field embeds in an algebraic closure of K. Frobenius injectivity in that
closure gives a unique value for every X_i, so every residue evaluation has the same
kernel. Thus the closed fibre has exactly one prime. Lying over gives existence;
contraction shows that this is the only maximal ideal of the quotient. The map
A → B sends the maximal ideal into this ideal, which is the local-hom condition.
For n = 0 the quotient is A itself, so the assertions hold as well. -/
theorem pthRootAlgebra_local (p n : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] [IsLocalRing A]
    (a : Fin n → A) :
    ∃ hlocal : IsLocalRing (pthRootAlgebra p n A a),
      letI := hlocal
      IsLocalHom (algebraMap A (pthRootAlgebra p n A a)) := by
  sorry

end Algebra
