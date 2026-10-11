/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Group.Idempotent

/-!
# Monic factorization from a lifted idempotent

Source: Stacks Project, Tag 09XI, proof of (3) implies (1)
(blueprint: lem-weil-pbc-idempotent-splitting-monic-factorization).
-/

@[expose] public section

universe u

namespace Polynomial

/-- Stacks Project, Tag 09XI, proof of (3) implies (1): an idempotent of `A[X]/(f)`
lifting the Chinese remainder element `(1, 0)` yields a monic factorization lifting `g₀ * h₀`.
The two `AdjoinRoot.map` conditions are precisely its residues in the Chinese remainder
factors, so they express that its reduction is the specified idempotent of `B/IB`.
(blueprint: lem-weil-pbc-idempotent-splitting-monic-factorization)

Proof:
1. By `lem-weil-pbc-monic-quotient-free`, `B = A[X]/(f)` is finite free, its coefficient
   reduction is `(A/I)[X]/(f.map (Ideal.Quotient.mk I))`, and the coprime factorization
   identifies this reduction with the product of the quotients by `g₀` and `h₀`.
2. Split `B` into `eB` and `(1-e)B`. Multiplication by the class of `X` preserves both.
   Modulo `I`, these summands become the quotients by `g₀` and `h₀`, respectively, with
   their multiplication-by-`X` endomorphisms. Their ranks are the natural degrees.
3. The summands are finite projective. By
   `lem-weil-pbc-finite-projective-rank-locally-constant`, their ranks are locally constant.
   Each rank equals its prescribed degree on `V(I)`. The closed locus where it differs
   would contain a maximal ideal, which contains `I` by the Jacobson hypothesis, a
   contradiction. By `lem-weil-pbc-finite-projective-standard-free-cover`, the summands
   are finite locally free of those constant ranks, including zero localizations.
4. Define `g` and `h` as the characteristic polynomials of these restricted endomorphisms
   using `def-weil-pbc-charpoly-locally-free`. They are monic by
   `lem-weil-pbc-charpoly-locally-free-existence`. Multiplicativity from
   `lem-weil-pbc-charpoly-locally-free-direct-sum` and
   `lem-weil-pbc-charpoly-mul-T-monic-quotient` gives `f = g * h`. For the zero ring
   this equality holds directly.
5. Base change of the characteristic polynomials to `A/I`, their invariance under the
   identifications in step 2, and `lem-weil-pbc-charpoly-mul-T-monic-quotient` identify
   their reductions with `g₀` and `h₀`. -/
theorem exists_monic_factorization_of_idempotent
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (e : AdjoinRoot f) (he : IsIdempotentElem e)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g₀
      (hfactor.symm ▸ dvd_mul_right g₀ h₀) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h₀
      (hfactor.symm ▸ dvd_mul_left h₀ g₀) e = 0) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  sorry

end Polynomial
