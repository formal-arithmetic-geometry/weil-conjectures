/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IdempotentsDeterminedModuloRadical
import Sheaf.RingTheory.LiftIdempotentUpstairs
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Henselian pairs from lifting sections of étale algebras

Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (2) ⇒ (4) ⇒ (3)
(blueprint: lem-weil-pbc-etale-section-lifting-henselian-pair).
-/

@[expose] public section

universe u v

/-! Proof plan is recorded on the blueprint node. -/

/-- The radical and root-lifting part of Stacks Tag 09XI.
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (2) ⇒ (4) ⇒ (3)
(blueprint: lem-weil-pbc-etale-section-lifting-radical-and-henselian).

Proof: apply the open-localization argument for the Jacobson radical, then the
finite-algebra idempotent descent through the étale neighbourhood and the section
supplied by the hypothesis; uniqueness follows from congruence modulo the radical. -/
theorem etale_section_lifting_radical_and_henselian (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    I ≤ Ideal.jacobson ⊥ ∧ HenselianRing A I := by
  sorry

/-- The finite-algebra idempotent-lifting part
(blueprint: lem-weil-pbc-etale-section-lifting-idempotents) of Stacks Tag 09XI.
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (4) ⇒ (3).

Proof: apply the étale idempotent lifting construction and descend along the
section supplied by the hypothesis; uniqueness follows from congruence modulo
the radical. -/
theorem etale_section_lifting_idempotents (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    ∀ (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
      (e₀ : B ⧸ I.map (algebraMap A B)), IsIdempotentElem e₀ → ∃! e : B,
        IsIdempotentElem e ∧ Ideal.Quotient.mk (I.map (algebraMap A B)) e = e₀ := by
  sorry

theorem henselianRing_of_etale_section_lifting (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    I ≤ Ideal.jacobson ⊥ ∧ HenselianRing A I ∧
      ∀ (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
        (e₀ : B ⧸ I.map (algebraMap A B)), IsIdempotentElem e₀ →
          ∃! e : B, IsIdempotentElem e ∧
    Ideal.Quotient.mk (I.map (algebraMap A B)) e = e₀ := by
  obtain ⟨hJ, hH⟩ := etale_section_lifting_radical_and_henselian A I h
  obtain hE := etale_section_lifting_idempotents A I h
  exact ⟨hJ, hH, hE⟩

