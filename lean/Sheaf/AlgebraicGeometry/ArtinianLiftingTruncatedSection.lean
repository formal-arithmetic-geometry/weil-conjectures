/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.Paper.ArtinianIdealLengthOneFiltration

/-! # Truncated Artinian sections
Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1).
-/

@[expose] public section

universe u v

namespace Algebra

/-- The length-one Artinian lifting tests produce sections at every positive truncation.

Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1), paragraphs
beginning "Let N" and "Applying condition (4)" (https://stacks.math.columbia.edu/tag/02HT).
(blueprint: lem-weil-pbc-artinian-lifting-truncated-section).

Proof in words:
Write C = P.Ring, S = A_q, J = P.ker, m = maximalIdeal C, and n = maximalIdeal S.
The surjection C -> S pulls n back to m, so J is contained in m, and the image of
m is n. For N >= 1 put E = C/(J^2 + m^N) and F = C/(J + m^N). Both defining
ideals contain m^N and lie in m. Thus these quotients are nonzero Artinian local
rings by the Noetherian local quotient lemma, and E -> F is a local surjection.
Its kernel K is the image of J and has square zero. The natural map A -> F has
preimage maximal ideal q, since F is canonically S/n^N.

Apply exists_ideal_filtration_length_one to K in E. For its increasing filtration
0 = K_0 <= ... <= K_r = K, use the surjections E/K_i -> E/K_(i+1).
Their kernels are K_(i+1)/K_i and have length one over E/K_i: restriction of
scalars along E -> E/K_i identifies submodule lattices and preserves length.
All quotients are nonzero Artinian local, since the K_i lie in the maximal ideal.
Start with A -> E/K_r = F and lift successively down this finite chain using hlift.
At each stage a local surjection pulls the maximal ideal back to the source
maximal ideal, so the inverse image in A remains q. The structural R-map is
induced from C, and each application preserves its composite with A. This gives
an R-compatible lift a' : A -> E.

The preimage under a' of the maximal ideal of E is q, by composing with E -> F.
Hence every element outside q maps to a unit, and a' extends uniquely to S.
This extension is local: a fraction with numerator in q maps into the maximal
ideal, while its denominator is a unit. The maximal ideal of E is the image of
m and its N-th power is zero. Thus the extension annihilates n^N and factors
uniquely through S/n^N = F as an R-algebra map sigma : F -> E.
The composite E -> F after sigma agrees with the identity on A. Uniqueness of
localization maps first gives equality on S, and surjectivity of S -> F gives
equality on F. This is the displayed section equation.

For tests in Type (max u v), replace the intermediate quotient rings by ULift
and transport their maps by its ring equivalence. Equivalences preserve local
and Artinian structures, kernel length, and the two compatibility equations;
transport each lift back before continuing the induction. This is only a choice
inside an existential proof, not a definition of an object from an unproved theorem.
For N = 1 the two quotients are C/m and the section is the identity; if J = 0
all quotient maps are identities. No finite presentation or assumption on the
residue characteristic is used. -/
theorem artinian_lifting_truncated_section
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime]
    (P : Extension.{u} R (Localization.AtPrime q))
    [IsLocalRing P.Ring] [IsNoetherianRing P.Ring]
    (hlift : ∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp (algebraMap R A) = φ.comp ρ →
          Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ) :
    ∀ (N : ℕ), 1 ≤ N →
      ∃ σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
          (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)),
        (Ideal.Quotient.factorₐ R
          (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
            AlgHom.id R _ := by sorry

end Algebra
