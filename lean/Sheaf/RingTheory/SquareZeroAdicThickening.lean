module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Adic completeness across a square-zero thickening

Source: Stacks Project, Algebra, Tag 0DYC (lemma-complete-modulo-nilpotent),
specialized to a square-zero first ideal; Tag 0317 (definition-complete).
(blueprint: lem-sfb-finite-square-zero-adic-thickening)
-/

@[expose] public section

universe u

namespace IsAdicComplete

/-- Adic completeness lifts from a quotient by a square-zero ideal in a Noetherian ring.
The ideal `(H ⊔ Q).map (Ideal.Quotient.mk Q)` is the quotient ideal `(H + Q)/Q`.

Source: Stacks Project, Algebra, Tag 0DYC (lemma-complete-modulo-nilpotent),
with first ideal `Q` and second ideal `H`; Tag 0317 (definition-complete).
(blueprint: lem-sfb-finite-square-zero-adic-thickening)

Proof:
1. Since `Q ^ 2 = 0`, every power `Q ^ n` with `n ≥ 2` vanishes. The inverse system
   `C / Q ^ n` therefore has constant tail `C`, with identity transition maps.
   A compatible family is uniquely determined by its term at index two: all later terms
   equal it, and the earlier terms are its quotient images. Thus the canonical map from
   `C` to its `Q`-adic completion is bijective, giving `IsAdicComplete Q C` by
   `def-weil-pbc-adically-complete-ring`.
2. Apply `lem-sfb-two-ideal-adic-completeness` with `R = C`, `I = Q`, and `J = H`.
   The ring is Noetherian by hypothesis, is `Q`-complete by step 1, and its quotient
   is complete for `(Q + H)/Q = (H + Q)/Q` by hypothesis. The conclusion is
   `IsAdicComplete H C`. No section, coefficient-ring flatness, or locality is used. -/
theorem of_square_zero_quotient (C : Type u) [CommRing C] [IsNoetherianRing C]
    (Q H : Ideal C) (hQ : Q ^ 2 = ⊥)
    (hcomplete : IsAdicComplete ((H ⊔ Q).map (Ideal.Quotient.mk Q)) (C ⧸ Q)) :
    IsAdicComplete H C := by
  sorry

end IsAdicComplete
