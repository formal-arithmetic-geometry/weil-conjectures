module

public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.FieldTheory.Perfect
import WeilConjectures.RingTheory.CohenRingModPowFormallySmooth

/-!
# Unique lifting of a perfect Cohen residue map

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Theorem 4.1.8(i)
and 4.1.9, printed pp. 57–58, with the ideal equal to the target's maximal ideal.
(blueprint: lem-per-perfect-cohen-residue-map)
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- A residue-field homomorphism from a perfect-residue Cohen ring lifts uniquely
to a local ring homomorphism into a complete Noetherian local ring.
Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Theorem 4.1.8(i)
and 4.1.9, printed pp. 57–58; uniqueness is used in 4.3.5.
(blueprint: lem-per-perfect-cohen-residue-map)

Proof:
1. Put K = A/pA and m = maximalIdeal R. The Cohen-ring definition
   (def-weil-pbc-cohen-ring) makes K a field and identifies the kernel of A → K
   with pA. The field homomorphism j is injective. Since p vanishes in K, it
   vanishes in the residue field of R, so p belongs to m. Start with h₁ = j ∘ q_A.
2. Given hₙ : A → R/mⁿ for n ≥ 1, put D = R/mⁿ⁺¹ and J = mⁿ/mⁿ⁺¹.
   Then D/J is canonically R/mⁿ, J² = 0 because 2n ≥ n+1, and pⁿ⁺¹ = 0 in D.
   The map hₙ factors through A/pⁿ⁺¹A. Apply the square-zero lifting clause of
   lem-weil-pbc-cohen-ring-mod-pn-formally-smooth to obtain hₙ₊₁ reducing to hₙ.
   Recursive choice gives compatible maps for all n ≥ 1.
3. Completeness (def-weil-pbc-adically-complete-ring) identifies R with the inverse
   limit of R/mⁿ. Assemble the compatible maps into f : A → R. The coordinate
   maps preserve the ring operations and separatedness proves that f does too.
   The first coordinate gives q_R ∘ f = j ∘ q_A. Injectivity of j then gives
   f(a) ∈ m iff q_A(a) = 0 iff a ∈ pA, which is precisely the stated locality.
4. For two lifts f and g, prove f(a) - g(a) ∈ mⁿ for every a and n ≥ 1 by induction.
   Their residue equality is the base case. Perfectness supplies a = bᵖ + pc.
   If d = f(b) - g(b) ∈ mⁿ, the term linear in d in the binomial expansion of
   (g(b) + d)ᵖ - g(b)ᵖ belongs to mⁿ⁺¹ because p ∈ m. All higher terms belong to
   m²ⁿ ⊆ mⁿ⁺¹. Likewise p(f(c) - g(c)) ∈ mⁿ⁺¹, proving the induction step.
5. Separatedness, included in def-weil-pbc-adically-complete-ring, gives
   ⋂ₙ mⁿ = 0, hence f(a) = g(a) for every a and therefore f = g. -/
theorem existsUnique_cohenRing_lift_of_perfect
    (p : ℕ) (A : Type u) [CommRing A] (hA : IsCohenRing p A)
    [PerfectRing (A ⧸ Ideal.span {(p : A)}) p]
    (R : Type v) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (j : (A ⧸ Ideal.span {(p : A)}) →+* ResidueField R) :
    ∃! f : A →+* R,
      (maximalIdeal R).comap f = Ideal.span {(p : A)} ∧
        (residue R).comp f = j.comp (Ideal.Quotient.mk (Ideal.span {(p : A)})) := by
  sorry

end IsLocalRing
