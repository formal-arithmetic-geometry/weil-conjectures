/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.Irreducible

/-!
# Irreducibility of an affine linear incidence hypersurface

Source: Stacks Project, `more-morphisms.tex`, Tag 0G4F, lemma `lemma-bertini-irreducible`,
middle proof paragraph (blueprint: lem-zl-linear-incidence-irreducible).
-/

@[expose] public section

universe u v

open AlgebraicGeometry

/--
Let `A` be a finite type domain over a field `k`.  If the coefficients of a nonzero
linear form in at least one variable have a common vanishing locus of height at least
two, then the spectrum of its quotient polynomial ring is irreducible.  The statement
asserts irreducibility only; it makes no reducedness claim.

Source: Stacks Project, `more-morphisms.tex`, Tag 0G4F, lemma `lemma-bertini-irreducible`,
middle proof paragraph (blueprint: lem-zl-linear-incidence-irreducible).
Proof: Put `B = A[x_i]` and `L = ∑ f_i x_i`; `B` is a Noetherian domain and `L` is nonzero.
On each coefficient open, substitution identifies the kernel of evaluation at the solved
variable and clearing denominators shows that every minimal prime over `(L)` contains
that kernel.  The height bound for a principal quotient gives height at most one for
such a minimal prime.  If all coefficients lay in it, extending a length-two prime chain
under a minimal prime over their ideal would contradict that bound.  Hence a coefficient
is outside, forcing the minimal prime to be the substitution kernel; all minimal primes
therefore coincide.  The quotient spectrum is the corresponding irreducible closed set.
The argument uses the finite-type, polynomial-ring, localization, height, minimal-prime,
and irreducible-spectrum facts listed in the DAG proof dependencies.
-/
theorem linear_incidence_irreducible
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A]
    (r : ℕ) (hr : 0 < r) (f : Fin r → A) (hf : ∃ i, f i ≠ 0)
    (hJ : ∀ p : Ideal A, p ∈ (Ideal.span (Set.range f)).minimalPrimes →
      (2 : ℕ∞) ≤ p.height) :
    IrreducibleSpace
      (Spec (CommRingCat.of
        (MvPolynomial (Fin r) A ⧸ Ideal.span
          {∑ i : Fin r, MvPolynomial.C (f i) * MvPolynomial.X i}))) := by
  sorry

end
