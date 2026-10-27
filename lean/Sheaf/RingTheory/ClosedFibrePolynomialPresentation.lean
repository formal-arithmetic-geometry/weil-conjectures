module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring

/-! # Polynomial presentation at a closed point of the special fibre

Source: Stacks Project, Tag 0AUG, lemma-localization-at-closed-point-special-fibre
(blueprint: lem-per-closed-fibre-polynomial-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra.EssFiniteType

/-- An essentially finite type algebra between local rings is a localization of a quotient
of a polynomial ring localized at a maximal ideal over the base maximal ideal.
The structure homomorphism is not assumed local.

Source: Stacks Project, Tag 0AUG, lemma-localization-at-closed-point-special-fibre
(blueprint: lem-per-closed-fibre-polynomial-presentation).

Proof:
1. Using def-weil-pbc-essentially-finite-type-algebra and def-weil-pbc-finite-type-algebra,
   write S as a localization of P/I for a finite polynomial ring P. Pull back the maximal
   ideal of S to a prime q of P. The fraction map P_q/IP_q to S is an isomorphism:
   denominators outside q map to units, every fraction in S lifts, and a zero fraction
   is killed by a denominator already inverted in P_q.
2. If q + m_R P is proper, lem-weil-pbc-proper-ideal-contained-in-maximal supplies a
   maximal ideal n containing it. Its contraction is m_R, and P_q is a localization
   of P_n by inverting P minus q (def-weil-pbc-localization-at-prime).
3. Otherwise let K be the residue field of q and B the image of R in K, a local domain.
   Apply lemma-nagata-local-domain-valuation-dominates to B inside its fraction field,
   then lemma-nagata-valuation-ring-extension to obtain a valuation ring A of K
   dominating B. Thus the inverse image of m_A in R is m_R.
4. If all coordinate residues lie in A, evaluation contradicts q + m_R P = P.
   Start with a coordinate outside A. The alternative in def-trf-valuation-ring and
   finite induction give a nonzero pivot lambda_i whose inverse and all ratios
   lambda_j/lambda_i belong to A. Replace the pivot whenever a new ratio lies outside A;
   multiplying previous ratios by the inverse ratio preserves their membership in A.
5. For the polynomial ring Q with variables y_0 and y_j for j different from i, use
   y_0 = 1/x_i and y_j = x_j/x_i. The inverse chart sends x_i to 1/y_0 and x_j to y_j/y_0.
   The universal property of def-weil-pbc-mv-polynomial-ring shows these are inverse
   after inverting the pivot, and then gives Q_q' isomorphic to P_q at corresponding
   primes (def-weil-pbc-localization-at-prime).
6. The map Q to K factors through A by the pivot memberships. Hence q' + m_R Q is
   contained in the proper inverse image of m_A. Step 2 gives a maximal n over m_R
   containing q'.
7. Transfer IP_q to an ideal J in Q_q' and contract it to J_0 in Q_n. Localizing J_0
   recovers J: multiply a fraction in J by its invertible denominator. Therefore
   S is isomorphic over R to T^{-1}(Q_n/J_0), where T is the image of the denominators.
   Surjectivity follows from fractions and injectivity from cross multiplication,
   as in def-weil-pbc-essentially-finite-type-algebra and
   def-weil-pbc-localization-at-prime. Rename the variables; the proper-ideal case
   already includes n = 0. -/
theorem exists_polynomial_maximal_localization_quotient
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Algebra.EssFiniteType R S] :
    ∃ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)),
      Ideal.comap (algebraMap R (MvPolynomial (Fin n) R)) m.asIdeal =
        IsLocalRing.maximalIdeal R ∧
      ∃ (I : Ideal (Localization.AtPrime m.asIdeal))
        (T : Submonoid (Localization.AtPrime m.asIdeal ⧸ I)),
        Nonempty (Localization T ≃ₐ[R] S) := by
  sorry

end Algebra.EssFiniteType
