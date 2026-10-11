/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian

/-!
# Henselian pairs from lifting sections of étale algebras

Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (2) ⇒ (4) ⇒ (3)
(blueprint: lem-weil-pbc-etale-section-lifting-henselian-pair).
-/

universe u v

/-- If every section of an étale algebra modulo `I` lifts to a section over `A`, then
`I` lies in the Jacobson radical and `(A, I)` is henselian. The finite-algebra idempotent
criterion is stated explicitly alongside Mathlib's equivalent `HenselianRing` predicate.
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, (2) ⇒ (4) ⇒ (3)
(blueprint: lem-weil-pbc-etale-section-lifting-henselian-pair).

Proof:
1. If `I` is not contained in a maximal ideal, choose a nonunit `f` congruent to `1`
modulo `I`. Localization at `f` is étale by
`lem-weil-pbc-principal-localization-open-immersion` and
`lem-weil-pbc-etale-composition-cancellation`. Its map to `A/I` lifts by the hypothesis;
the lift sends the inverse of `f` to an inverse in `A`, a contradiction.
2. A finite `A`-algebra `B` is integral by `lem-weil-pbc-finite-algebra-is-integral`.
By `lem-weil-pbc-integral-algebra-ideal-in-radical`, `IB` lies in its Jacobson radical.
3. Two idempotents congruent modulo `IB` agree by
`lem-weil-pbc-idempotents-determined-modulo-radical`, giving uniqueness.
4. By `lem-weil-pbc-lift-idempotent-upstairs`, an idempotent modulo `IB` lifts after an
étale extension `A'` with `A/I ≅ A'/IA'`. Compose the quotient of `A'` with the inverse
of this isomorphism to obtain a section modulo `I`. The hypothesis supplies a lift
`τ : A' →ₐ[A] A`. Applying `id ⊗ τ` to the lifted idempotent gives an idempotent in `B`;
its reduction is the original one because `q ∘ τ = σ`.
5. This is the finite-algebra criterion for a henselian pair in
`def-weil-pbc-henselian-terminology`, equivalently `HenselianRing A I` by Stacks 09XI.
The radical assertion was established in step 1. -/
theorem henselianRing_of_etale_section_lifting (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
      (σ : A' →ₐ[A] A ⧸ I), ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    I ≤ Ideal.jacobson ⊥ ∧ HenselianRing A I ∧
      ∀ (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
        (e₀ : B ⧸ I.map (algebraMap A B)), IsIdempotentElem e₀ →
          ∃! e : B, IsIdempotentElem e ∧
            Ideal.Quotient.mk (I.map (algebraMap A B)) e = e₀ := by
  sorry
