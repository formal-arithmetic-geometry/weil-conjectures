module

public import Mathlib.RingTheory.Regular.RegularSequence

/-! Auxiliary inclusion for regular-sequence ideal intersections. -/

@[expose] public section

universe u

namespace Ideal

/-- If a sequence is regular after quotienting by `I`, every element of the
intersection with its generated ideal has coefficients in `I`.
Source: Stacks Project, More on Algebra, Tag 0665, proof of Lemma H1-regular-in-quotient.
(blueprint: aux-regular-quotient-ideal-intersection-inclusion).

Proof: reduce a Koszul degree-one presentation of an element of the
intersection modulo `I`. The reduction is a one-cycle; regularity gives
H₁-vanishing, so it is a boundary. Lift the degree-two boundary and subtract
it from the presentation. The resulting coefficients lie in `I`, proving the
element lies in the product ideal. -/
theorem inf_ofList_le_mul_of_regular_quotient {R : Type u} [CommRing R]
    (I : Ideal R) (gs : List R)
    (hgs : RingTheory.Sequence.IsRegular (R ⧸ I) (gs.map (Ideal.Quotient.mk I))) :
    I ⊓ Ideal.ofList gs ≤ I * Ideal.ofList gs := by
  sorry

end Ideal
