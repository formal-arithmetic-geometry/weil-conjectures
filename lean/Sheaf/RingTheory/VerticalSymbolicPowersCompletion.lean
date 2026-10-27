/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Ideal.GoingDown
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.QuotientHenselianPair
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Vertical symbolic powers and henselian completion

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, V 2.2.4 and V 3.2.3--3.2.4,
printed pp. 65, 67; Stacks Project, Algebra, Tag 0BC0,
lemma-symbolic-power-flat-extension
(blueprint: lem-per-vertical-symbolic-powers-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- A prime minimal over a nonzero vertical principal ideal in the completion descends
uniquely, is the extension of its contraction, and its positive symbolic powers descend.
Both primes have height one, expressed as nonzero with no nonzero prime strictly below them.
Symbolic powers are written as the contraction of the ordinary power extended to the
localization at the prime, exactly the localization-membership definition in the node.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, V 2.2.4 and V 3.2.3--3.2.4,
printed pp. 65, 67; Stacks Project, Algebra, Tag 0BC0,
lemma-symbolic-power-flat-extension
(blueprint: lem-per-vertical-symbolic-powers-completion).

Proof:
1. Local completion is faithfully flat
   (`lem-weil-pbc-local-completion-faithfully-flat`), so every extended ideal contracts
   to itself and the completion map is injective
   (`lem-weil-pbc-faithfully-flat-ideal-contraction`). The completion is Noetherian
   (`lem-weil-pbc-adic-completion-noetherian`). Contract P to p; it is prime and contains a.
2. Flat going down (`lem-sc-flat-going-down`) lifts a smaller prime containing a to
   a prime below P containing the image of a. Minimality of P rules this out, so p
   is minimal over (a).
3. The quotient A/p is a Noetherian local domain. It is excellent by
   `lem-exc-finite-type-localization-excellent`, applied to the quotient algebra, and
   henselian by `lem-weil-pbc-quotient-henselian-pair`. Thus its completion is a domain
   (`lem-per-henselian-excellent-completion-domain`). The quotient-completion comparison
   (`lem-weil-pbc-local-completion-quotient`) makes p extended to the completion prime.
4. This extended prime lies between (a) and P, so minimality makes it P. Contracting
   any other such extended prime proves uniqueness and identifies p with P contracted.
5. Krull's principal ideal theorem (`lem-sfb-krull-principal-ideal-height-bound`) gives
   height at most one for both primes. The nonzero element a and its nonzero image
   belong to them, so both are nonzero. In a domain, zero is prime, so no prime can
   lie strictly between zero and either prime.
6. Apply `lem-sfb-symbolic-powers-flat-prime-extension` to the flat completion map
   and p, whose extension is P. It identifies their symbolic powers for every n ≥ 1.
-/
theorem vertical_symbolic_powers_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hExcellent : IsExcellent A)
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (a : A) (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) [P.IsPrime]
    (hP : (Ideal.span {algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) a}).IsMinimalPrime P) :
    P ≠ ⊥ ∧
      (∀ Q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        Q.IsPrime → ⊥ < Q → ¬ Q < P) ∧
      ∃ p : PrimeSpectrum A,
        (Ideal.span {a}).IsMinimalPrime p.asIdeal ∧
        p.asIdeal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) = P ∧
        (∀ q : PrimeSpectrum A, (Ideal.span {a}).IsMinimalPrime q.asIdeal →
          q.asIdeal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) = P →
            q = p) ∧
        p.asIdeal = P.comap (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
        p.asIdeal ≠ ⊥ ∧
        (∀ q : Ideal A, q.IsPrime → ⊥ < q → ¬ q < p.asIdeal) ∧
        ∀ n : ℕ, 1 ≤ n →
          (((p.asIdeal ^ n).map (algebraMap A (Localization.AtPrime p.asIdeal))).comap
            (algebraMap A (Localization.AtPrime p.asIdeal))).map
              (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
          ((P ^ n).map (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)
            (Localization.AtPrime P))).comap
              (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)
                (Localization.AtPrime P)) := by
  sorry

end AdicCompletion
