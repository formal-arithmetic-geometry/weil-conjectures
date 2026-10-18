/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Polynomial presentation at a closed point of the special fibre

Source: Stacks Project, Tag 0AUG, lemma-localization-at-closed-point-special-fibre.
(blueprint: lem-per-closed-fibre-polynomial-presentation)
-/

@[expose] public section

universe u v

namespace Algebra.EssFiniteType

/-- An essentially finite type algebra between local rings is a localization of a quotient
of a polynomial local ring at a maximal ideal above the base maximal ideal. The structure
map is not assumed local. The localization is the usual ring of fractions at a submonoid.

Source: Stacks Project, Tag 0AUG, lemma-localization-at-closed-point-special-fibre.
(blueprint: lem-per-closed-fibre-polynomial-presentation)

Proof:
1. By def-weil-pbc-essentially-finite-type-algebra and def-weil-pbc-finite-type-algebra,
write S as a localization W⁻¹(P/I), with P a polynomial ring in finitely many variables.
Let q be the inverse image of the maximal ideal of S. Every element outside q maps to a
unit. The induced R-algebra map P_q/IP_q → S is bijective: fractions give surjectivity,
and the localization equality criterion gives injectivity, since a denominator from W
annihilates any element mapping to zero. Use def-weil-pbc-localization-at-prime.
2. If q + m_R P is proper, lem-weil-pbc-proper-ideal-contained-in-maximal gives a maximal
ideal m containing it. Its contraction is m_R, since this contraction is proper and
contains m_R. Since q ⊆ m, P_q is a localization of P_m by inverting the images of P ∖ q.
3. Otherwise, let K = κ(q), and let B be the image of R in K. This is a local domain
R/p, where p is the kernel and p ⊆ m_R. Apply lemma-nagata-local-domain-valuation-dominates
to B in its fraction field and lemma-nagata-valuation-ring-extension to that fraction
field inside K. Obtain a valuation subring A of K dominating B; m_A contracts to m_R.
Write λ_j for the images of the polynomial variables in K.
4. If every λ_j belongs to A, evaluation P → A shows q + m_R P is proper, a contradiction.
Otherwise choose a nonzero pivot λ_i outside A. By def-trf-valuation-ring its inverse
belongs to A. Process the finitely many other coordinates, keeping the pivot when
λ_j/λ_i belongs to A, and replacing it by λ_j otherwise. The valuation alternative
puts λ_i/λ_j in A in the latter case. Multiplication preserves all earlier ratios and
the inverse membership. Thus λ_i⁻¹ and all λ_j/λ_i belong to A. For zero variables this
remaining case cannot occur.
5. Let Q have variables y_0 and y_j for j ≠ i, again finitely many, and map it to P_q
by y_0 ↦ x_i⁻¹ and y_j ↦ x_j/x_i. Let q_Q be the inverse image of qP_q. Then y_0 is
outside q_Q. The maps between Q[1/y_0] and P[1/x_i] just displayed and the inverse
x_i ↦ y_0⁻¹, x_j ↦ y_j/y_0 fix coefficients and variables under composition. By
def-weil-pbc-mv-polynomial-ring and def-weil-pbc-localization-at-prime they induce
inverse R-algebra maps Q_(q_Q) ≃ P_q; the primes are the kernels of the maps into K.
6. The evaluation Q → K factors through A by Step 4, with kernel q_Q. Consequently
q_Q + m_R Q is contained in the proper inverse image of m_A and is proper. Apply Step 2
to this chart to get a maximal ideal m above m_R containing q_Q.
7. Transport IP_q to an ideal J of Q_(q_Q), and contract J to J₀ in Q_m. Localizing J₀
back gives J: for a/u ∈ J, multiplying by the inverted denominator gives a ∈ J₀.
Localization commutes with this quotient, by the fraction equality criterion. Thus
S ≃ Q_(q_Q)/J ≃ T⁻¹(Q_m/J₀), where T is the image of the multiplicative subset generated
by Q ∖ q_Q. Rename the variables of Q using Fin n. This also includes n = 0. -/
theorem exists_polynomial_maximal_localization_quotient
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Algebra.EssFiniteType R S] :
    ∃ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)),
      m.asIdeal.comap (algebraMap R (MvPolynomial (Fin n) R)) = IsLocalRing.maximalIdeal R ∧
      ∃ (I : Ideal (Localization.AtPrime m.asIdeal))
        (T : Submonoid (Localization.AtPrime m.asIdeal ⧸ I)),
        Nonempty (Localization T ≃ₐ[R] S) := by
  sorry

end Algebra.EssFiniteType
