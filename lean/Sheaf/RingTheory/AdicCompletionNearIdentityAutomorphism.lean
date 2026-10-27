/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Near-identity automorphisms of completed local rings

Source: Stacks Project, Tag 0CAV, `lemma-isomorphism-approximation`, associated-graded
and infinitesimal-quotient argument after identifying the given isomorphism with the identity
(blueprint: lem-trf-completion-near-identity-automorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- A ring endomorphism of the maximal-ideal completion of a Noetherian local ring that
preserves the extended maximal ideal and is the identity modulo its square is an automorphism.
The parameter `n`, with its defining equality `hn`, names the extended maximal ideal. Positive
quotient levels are indexed by `r + 1`. Identities on the residue field and graded pieces are
expressed on representatives; the quotient equivalences are characterized on representatives.
The equivalence `α` is the canonical identification with the second completion, and its conjugate
of the inverse automorphism acts coordinatewise by the finite-quotient inverses.

Source: Stacks Project, Tag 0CAV, `lemma-isomorphism-approximation`, proof
(blueprint: lem-trf-completion-near-identity-automorphism).

Proof: (1) Noetherianity makes the maximal ideal finitely generated. The local-completion
lemma identifies the maximal ideal of the completion with `n`; the completion-mod-ideal lemma
makes it `n`-adically complete, so its canonical map to the second completion is bijective.
(2) Preservation of `n` implies preservation of every power. The square-congruence implies
identity on the residue field. For a product `a x₁ ⋯ xᵣ` with each `xᵢ` in `n`, telescope its
image minus itself. The coefficient difference lies in `n²`, hence contributes to `n^(r+2)`;
each other summand contains one factor `h(xᵢ)-xᵢ` in `n²` and `r-1` factors in `n`, hence
lies in `n^(r+1)`. Additivity gives identity on the degree-`r` graded piece for every `r ≥ 1`.
(3) Induct on positive quotient levels. Level one is the identity. If `h(x)` lies in `n^(r+1)`,
injectivity at level `r` puts `x` in `n^r`, and the graded identity puts `x` in `n^(r+1)`.
For surjectivity, lift `y` modulo `n^r` as `h(x)`, set `e = y-h(x)` in `n^r`, and observe
`h(x+e) = y` modulo `n^(r+1)`. The resulting bijective ring maps are ring equivalences.
(4) The finite-level maps commute with reduction on representatives. Composing this equality
with their inverses gives compatibility of the inverses. Thus the coordinatewise maps on
compatible sequences are mutual inverses. The canonical completion identification intertwines
`h` with the forward coordinatewise map, so conjugating the inverse gives the asserted
ring automorphism and its coordinatewise inverse formula. -/
theorem nearIdentity_automorphism
    (C : Type u) [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (n : Ideal (AdicCompletion (IsLocalRing.maximalIdeal C) C))
    (hn : n = (IsLocalRing.maximalIdeal C).map
      (algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C)))
    (h : AdicCompletion (IsLocalRing.maximalIdeal C) C →+*
      AdicCompletion (IsLocalRing.maximalIdeal C) C)
    (hmem : ∀ d ∈ n, h d ∈ n)
    (hcongr : ∀ d, h d - d ∈ n ^ 2) :
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal C) C) ∧
    IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal C) C) = n ∧
    IsAdicComplete n (AdicCompletion (IsLocalRing.maximalIdeal C) C) ∧
    (∀ d, Ideal.Quotient.mk n (h d) = Ideal.Quotient.mk n d) ∧
    (∀ (r : ℕ) (d : AdicCompletion (IsLocalRing.maximalIdeal C) C),
      d ∈ n ^ (r + 1) → h d - d ∈ n ^ (r + 2)) ∧
    ∃ (e : AdicCompletion (IsLocalRing.maximalIdeal C) C ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal C) C)
      (eQ : ∀ r : ℕ,
        (AdicCompletion (IsLocalRing.maximalIdeal C) C ⧸ n ^ (r + 1)) ≃+*
        (AdicCompletion (IsLocalRing.maximalIdeal C) C ⧸ n ^ (r + 1)))
      (α : AdicCompletion (IsLocalRing.maximalIdeal C) C ≃+*
        AdicCompletion n (AdicCompletion (IsLocalRing.maximalIdeal C) C)),
      e.toRingHom = h ∧
      (∀ (r : ℕ) (d : AdicCompletion (IsLocalRing.maximalIdeal C) C),
        eQ r (Ideal.Quotient.mk (n ^ (r + 1)) d) =
          Ideal.Quotient.mk (n ^ (r + 1)) (h d)) ∧
      (∀ (r s : ℕ) (hrs : r ≤ s)
        (d : AdicCompletion (IsLocalRing.maximalIdeal C) C ⧸ n ^ (s + 1)),
        Ideal.Quotient.factorPow n (Nat.add_le_add_right hrs 1) ((eQ s).symm d) =
          (eQ r).symm (Ideal.Quotient.factorPow n (Nat.add_le_add_right hrs 1) d)) ∧
      α.toRingHom = algebraMap (AdicCompletion (IsLocalRing.maximalIdeal C) C)
        (AdicCompletion n (AdicCompletion (IsLocalRing.maximalIdeal C) C)) ∧
      (∀ (x : AdicCompletion n (AdicCompletion (IsLocalRing.maximalIdeal C) C)) (r : ℕ),
        AdicCompletion.evalₐ n (r + 1) (α (e.symm (α.symm x))) =
          (eQ r).symm (AdicCompletion.evalₐ n (r + 1) x)) := by
  sorry

end AdicCompletion
