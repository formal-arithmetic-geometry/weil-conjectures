module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Normality of fixed subrings and their prime localizations

Source: Stacks Project, Algebra, Tags 0309, 00GV and 00GY
(`literature/stacks-project/algebra.tex`, `lemma-localize-normal-domain`).
The arbitrary-group fixed-subring argument is agent-formulated for the existing quotients
in ILO X 2.3, Step 2, printed p.151, as recorded in the DAG.
(blueprint: lem-sfb-fixed-subring-normal-localizations)
-/

@[expose] public section

universe u v

namespace FixedPoints

/-- The fixed subring of an integrally closed domain under an arbitrary group of unital
ring automorphisms is an integrally closed domain, as is each of its prime localizations.
The last clause is also the definition of its being a normal ring. The action is encoded
by `MulSemiringAction`; since `G` is a group, each action map is a ring automorphism.
No finiteness, faithfulness, or invertibility of a group order is assumed.

Source: Stacks Project, Algebra, Tags 0309 (normal domain), 00GV (normal ring), and
00GY (`lemma-localize-normal-domain`); the fixed-subring argument is agent-formulated
for ILO X 2.3, Step 2, printed p.151.
(blueprint: lem-sfb-fixed-subring-normal-localizations)

Proof plan, following the five DAG steps:
1. The action preserves zero, one, sums, negatives and products, so its fixed points
   form the inherited unital subring C. Nontriviality and cancellation descend from D,
   making C a domain. Sending a/b in Frac(C) to a/b in Frac(D) embeds the fraction fields:
   equality on either side is the same cross-multiplication identity in D or in C.
2. A monic equation for x in Frac(C) maps to the same monic equation over D for its image y.
   Integral closedness of D, in def-weil-pbc-normal-ring, gives d in D representing y.
3. Write x = a/b with a,b in C and b nonzero. The equality bd = a holds in D.
   Applying any group element gives b(g • d) = a = bd, since a and b are fixed.
   Cancellation gives g • d = d. Thus d belongs to C, and the fraction-field embedding
   identifies x with this element of C. This proves integral closedness of C.
4. For a prime ideal p of C, its complement S is multiplicatively closed, contains one
   and excludes zero. The declaration Localization.AtPrime implements C_p = S⁻¹C
   (def-weil-pbc-localization-at-prime). Apply lem-weil-pbc-localization-normal-domain:
   isIntegrallyClosed_of_isLocalization gives integral closedness, and
   IsLocalization.isDomain_of_le_nonZeroDivisors gives the domain property.
   The source proof clears the denominators of a monic equation using one s in S:
   if y satisfies it, sy satisfies a monic polynomial over C, so sy belongs to C
   and y belongs to S⁻¹C.
5. That every prime localization is a normal domain is precisely the normal-ring
   clause of def-weil-pbc-normal-ring. Only nonzero-denominator cancellation was used;
   no step imposes finiteness, faithfulness, or division by a group order. -/
theorem isDomain_and_isIntegrallyClosed_subring_localizations
    (D : Type u) [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
    (G : Type v) [Group G] [MulSemiringAction G D] :
    IsDomain (FixedPoints.subring D G) ∧ IsIntegrallyClosed (FixedPoints.subring D G) ∧
      ∀ (p : Ideal (FixedPoints.subring D G)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end FixedPoints
