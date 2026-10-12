module

public import Sheaf.RingTheory.IsSMulRegularOfGoodSequence

@[expose] public section

universe u v

namespace Module

/-! Auxiliary setup for the Cohen--Macaulay good-element argument
(blueprint: lem-weil-pbc-cm-module-good-element-setup).
The construction of a maximal regular sequence and the prime-avoidance argument
are postponed to this theorem; its conclusion records precisely the data used by
`isSMulRegular_of_good_sequence`.

Proof: choose a maximal regular sequence from the depth equality, then use prime
avoidance over the finitely many minimal primes of the relevant supports; the
support-dimension equalities follow from the quotient-support and dimension-drop
lemmas.-/
/-- Existence of the regular sequence and goodness data.
(blueprint: lem-weil-pbc-cm-module-good-element-setup)

Proof: choose a maximal regular sequence from the depth equality, then use prime
avoidance over the finitely many minimal primes of the relevant supports; the
support-dimension equalities follow from the quotient-support and dimension-drop
lemmas. -/
theorem exists_good_sequence_for_cm_element
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdim : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) + 1 = supportDim R M) :
    ∃ d : ℕ, 1 ≤ d ∧ supportDim R M = (((d : ℕ∞) : WithBot ℕ∞)) ∧
      ∃ fs : List R, fs.length = d ∧
        (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular M fs ∧
        (∀ i : ℕ, i < d →
          Order.krullDim ((support R M ∩
            PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take i}) :
              Set (PrimeSpectrum R)) =
            (((d - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) := by
  sorry

end Module
