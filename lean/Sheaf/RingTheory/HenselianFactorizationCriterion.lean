/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.RingTheory.HenselianTerminology
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Factorization criterion for henselian pairs

Source: Stacks Project, More on Algebra, Lemma Tag 09XI (lemma-characterize-henselian-pair),
condition (3) iff condition (1), with Definition Tag 09XE
(blueprint: lem-weil-pbc-henselian-factorization-criterion).

The henselian pair `(A, I)` is the recorded notion of `def-weil-pbc-henselian-terminology`,
Mathlib's `HenselianRing A I`.
-/

universe u

open Polynomial

/-- `(A, I)` is henselian iff (i) `I` lies in the Jacobson radical and (ii) every coprime monic
factorization of the reduction of a monic `f ∈ A[T]` lifts to a monic factorization of `f`;
in particular, when `I` lies in the Jacobson radical, henselian iff (ii).
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (3) ⇔ (1), and Definition Tag 09XE
(blueprint: lem-weil-pbc-henselian-factorization-criterion).

Proof:
1. (3) ⇒ (i): if `I ⊄ 𝔪` for a maximal `𝔪`, then `B = A/(I ∩ 𝔪) ≅ A/I × A/𝔪` is finite with
   `B/IB ≅ A/I`; the distinct idempotents `(1,1)`, `(1,0)` both lift `1`, contradicting
   uniqueness of lifts.
2. (3) ⇒ (ii): `B = A[T]/(f)` is finite free (`lem-weil-pbc-monic-quotient-free`),
   `B/IB ≅ (A/I)[T]/(g₀) × (A/I)[T]/(h₀)` by CRT; lift the idempotent `(1,0)` to `e ∈ B` and
   apply `lem-weil-pbc-idempotent-splitting-monic-factorization`.
3. (1) ⇒ (5): factor `f = Tⁿ(T-1) + aₙTⁿ + ⋯ + a₀` (`aᵢ ∈ I`) lifting `Tⁿ · (T-1)`; the
   linear factor `T - α` gives a root `α ∈ 1 + I` (the case `A/I = 0` forces `A = 0`).
4. (5) ⇒ (2): `lem-weil-pbc-gabber-root-criterion-etale-section-lifting`.
5. (2) ⇒ (4) ⇒ (3): `lem-weil-pbc-etale-section-lifting-henselian-pair`.
6. The particular case: with (i) given, the equivalence reads henselian iff (ii). -/
theorem henselianRing_iff_factorization_criterion
    (A : Type u) [CommRing A] (I : Ideal A) :
    (HenselianRing A I ↔
      (I ≤ Ideal.jacobson (⊥ : Ideal A) ∧
        ∀ (f : A[X]), f.Monic → ∀ (g₀ h₀ : (A ⧸ I)[X]), g₀.Monic → h₀.Monic →
          IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀)) ∧
    (I ≤ Ideal.jacobson (⊥ : Ideal A) →
      (HenselianRing A I ↔
        ∀ (f : A[X]), f.Monic → ∀ (g₀ h₀ : (A ⧸ I)[X]), g₀.Monic → h₀.Monic →
          IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀)) := by
  sorry
