module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Compatible Artinian lifts through an isomorphism of completions

Source: Stacks Project, Tag 0CAV, first proof paragraph, the algebraic lifting argument
implicit in the smoothness assertion; completion coordinates from Section 00M9
(blueprint: lem-trf-completion-isomorphism-artinian-lifts).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

namespace IsLocalRing

/-- Compatible Artinian lifts through the inverse of the coordinatewise completed map.
Source: Stacks Project, Tag 0CAV, first proof paragraph, and Section 00M9
(blueprint: lem-trf-completion-isomorphism-artinian-lifts).

The condition on `h` describes its coordinates using representatives: whenever `x` represents
coordinate `n` of `z`, `φ x` represents coordinate `n` of `h z`. This specifies exactly the map
induced by `φ`, without choosing quotient representatives or an auxiliary algebra structure.

Proof: (1) By `lem-weil-pbc-artinian-local-noetherian-nilpotent` (Tag 00J8), choose positive
nilpotence exponents for the two Artinian maximal ideals. Locality sends the source maximal
ideals into these ideals, so the maps kill the corresponding powers and factor through the
quotients. (2) For any such factorizations, compose with the completion projections. The
projection identities show that these maps restrict to `a` and `b`. Each projection kills the
corresponding power of the extended maximal ideal: it kills products of the original ideal's
generators, hence their multiples and finite sums. (3) For a completed element, choose a
representative of its coordinate at `max r s`. Compatibility of coordinates, the coordinate
condition on `h`, and `q.comp a = b.comp φ` prove equality after applying `q`. (4) The same
coordinate condition gives `h i_A = i_B φ`. Compose with `h.symm` to obtain both triangle
identities for the displayed lift. (5) Surjectivity of `q` makes the inverse image of the
maximal ideal of `C` maximal, hence the maximal ideal of `C'`. Taking inverse images in the
first triangle identity proves that the lift is local. -/
theorem completion_isomorphism_artinian_lifts
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (h : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B)
    (hcoord : ∀ (n : ℕ) (z : AdicCompletion (maximalIdeal A) A) (x : A),
      AdicCompletion.evalₐ (maximalIdeal A) n z = Ideal.Quotient.mk (maximalIdeal A ^ n) x →
      AdicCompletion.evalₐ (maximalIdeal B) n (h z) =
        Ideal.Quotient.mk (maximalIdeal B ^ n) (φ x))
    {C' : Type w'} {C : Type w} [CommRing C'] [CommRing C]
    [IsLocalRing C'] [IsLocalRing C] [IsArtinianRing C'] [IsArtinianRing C]
    (q : C' →+* C) (hq : Function.Surjective q)
    (a : A →+* C') (b : B →+* C) [IsLocalHom a] [IsLocalHom b]
    (hab : q.comp a = b.comp φ) :
    (∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ maximalIdeal C' ^ r = ⊥ ∧ maximalIdeal C ^ s = ⊥ ∧
      ∃ (aBar : A ⧸ maximalIdeal A ^ r →+* C') (bBar : B ⧸ maximalIdeal B ^ s →+* C),
        aBar.comp (Ideal.Quotient.mk (maximalIdeal A ^ r)) = a ∧
        bBar.comp (Ideal.Quotient.mk (maximalIdeal B ^ s)) = b) ∧
    (∀ (r s : ℕ), 1 ≤ r → 1 ≤ s →
      maximalIdeal C' ^ r = ⊥ → maximalIdeal C ^ s = ⊥ →
      ∀ (aBar : A ⧸ maximalIdeal A ^ r →+* C') (bBar : B ⧸ maximalIdeal B ^ s →+* C),
      aBar.comp (Ideal.Quotient.mk (maximalIdeal A ^ r)) = a →
      bBar.comp (Ideal.Quotient.mk (maximalIdeal B ^ s)) = b →
      (aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom).comp
          (algebraMap A (AdicCompletion (maximalIdeal A) A)) = a ∧
      (bBar.comp (AdicCompletion.evalₐ (maximalIdeal B) s).toRingHom).comp
          (algebraMap B (AdicCompletion (maximalIdeal B) B)) = b ∧
      (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ^ r ≤
        RingHom.ker (aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom) ∧
      (maximalIdeal B).map (algebraMap B (AdicCompletion (maximalIdeal B) B)) ^ s ≤
        RingHom.ker (bBar.comp (AdicCompletion.evalₐ (maximalIdeal B) s).toRingHom) ∧
      q.comp (aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom) =
        (bBar.comp (AdicCompletion.evalₐ (maximalIdeal B) s).toRingHom).comp h.toRingHom ∧
      IsLocalHom
        ((aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom).comp
          (h.symm.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B)))) ∧
      q.comp ((aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom).comp
          (h.symm.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B)))) = b ∧
      ((aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom).comp
          (h.symm.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B)))).comp φ =
        a) := by
  sorry

end IsLocalRing
