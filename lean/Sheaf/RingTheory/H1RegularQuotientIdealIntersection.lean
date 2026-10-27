module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.KoszulRegularSequence

/-!
# Ideal intersection for an H₁-regular quotient ideal

Source: Stacks Project, More on Algebra, Tag 0666
(lemma-conormal-sequence-H1-regular).
(blueprint: lem-sfb-h1-regular-quotient-ideal-intersection)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- If `I ≤ J` and a finite tuple in `J` generates `J/I` and is H₁-regular in `A/I`,
then `I ∩ J² = IJ`. Here `J/I` is the image ideal `J.map (Ideal.Quotient.mk I)`.
There are no Noetherian, local, properness, or nonzero-ring assumptions, and `r = 0`
is permitted.

Source: Stacks Project, More on Algebra, Tag 0666
(lemma-conormal-sequence-H1-regular).
(blueprint: lem-sfb-h1-regular-quotient-ideal-intersection)

Proof:
1. Set `G = Ideal.span (Set.range g)`. The generators lie in `J`, and generation
   modulo `I` gives `J = I + G`: lift coefficients of an expression in `J/I`.
   Expanding the square gives `J² = I² + IG + G²`. Thus an element `x` of
   `I ∩ J²` is a sum `a + b + c`, with `a ∈ I²`, `b ∈ IG`, and `c ∈ G²`.
2. Since `a` and `b` lie in `I`, so does `c = x - a - b`; also `G² ≤ G`.
   By lem-sfb-h1-regular-generator-ideal-intersection (Stacks Tag 0665), applied
   to this tuple and its assumed H₁-regularity modulo `I`, `I ∩ G = IG`.
   Hence `c ∈ IG`. As `I ≤ J` and `G ≤ J`, all three summands belong to `IJ`.
3. Conversely, products from `IJ` belong to `I` and, since `I ≤ J`, to `J²`.
   This gives the reverse inclusion. For the empty tuple generation gives `J = I`,
   and both sides are `I²`; if `I = A`, then `J = A` and both sides are `A`.
-/
theorem inf_sq_eq_mul_of_h1Regular_quotient
    {A : Type u} [CommRing A] (I J : Ideal A) (hIJ : I ≤ J)
    {r : ℕ} (g : Fin r → A) (hg : ∀ i : Fin r, g i ∈ J)
    (hgen : J.map (Ideal.Quotient.mk I) =
      Ideal.span (Set.range (fun i : Fin r ↦ Ideal.Quotient.mk I (g i))))
    (hreg : RingTheory.Sequence.IsH1Regular
      (fun i : Fin r ↦ Ideal.Quotient.mk I (g i))) :
    I ⊓ J ^ 2 = I * J := by
  sorry

end Ideal
