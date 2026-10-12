/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Reduction of polynomial completion fibres to complete local domains

Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraph 2;
Algebra 00E3, 00C9, 00MA, 0325 and 07BH.
(blueprint: lem-weil-pbc-polynomial-complete-local-fibre-reduction)
-/

@[expose] public section

universe u

namespace Polynomial

/-- Each fibre of the localized polynomial completion transports to a polynomial
formal fibre above zero over a complete local domain.
Source: Stacks Project, proof of Proposition 07PV, paragraph 2, with the quotient
completion identity in the proof of 07PN.
(blueprint: lem-weil-pbc-polynomial-complete-local-fibre-reduction)

Proof:
1. Contract the given prime s of T = S[X]_Q to r in S[X]. Prime correspondence
   for localization gives r ≤ Q and canonically identifies the residue fields.
   As all denominators of T act invertibly on both factors, tensoring over S[X]
   or T gives the same fibre over this identified residue field (00E3, 00C9, 07BH).
2. Put p = r intersect S and A = S/p. Primality makes A a domain; 0325 makes it
   a Noetherian complete local ring. The coefficient quotient map S[X] → A[X]
   is surjective with kernel pS[X]. Its images q and r' of Q and r are maximal
   and prime respectively; q lies over the maximal ideal of A, r' ≤ q and
   r' intersects A in zero. Take this actual quotient ring as the witness A.
3. Localizing the coefficient quotient identifies A[X]_q with T/pT, preserving
   maximal ideals. Completion of a quotient (00MA) identifies its completion
   with C/pC, where C is the completion of T. At r the quotient-localization
   identity identifies the residue field with that of r' as an S[X]-algebra.
4. Since p annihilates the residue field, tensoring C with it is unchanged by
   replacing C with C/pC and the base S[X] with A[X]. Tensor associativity and
   step 1 give an isomorphism of fibres compatible with the residue-field
   isomorphism. Noetherianity and regularity after every finite purely inseparable
   field extension transport across these isomorphisms. This is precisely the
   implication below; no arbitrary object is used in a definition. -/
theorem exists_completeLocalDomain_fibre_reduction
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (hQ : Q.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S)
    (s : Ideal (Localization.AtPrime Q)) [s.IsPrime] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A) (_ : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
      (q r : Ideal (Polynomial A)) (_ : q.IsMaximal) (_ : r.IsPrime),
      q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A ∧
      r ≤ q ∧ r.comap (Polynomial.C : A →+* Polynomial A) = ⊥ ∧
      (Algebra.IsGeometricallyRegular r.ResidueField
        (r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) →
        Algebra.IsGeometricallyRegular s.ResidueField
          (s.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
            (Localization.AtPrime Q)))) := by sorry

end Polynomial
