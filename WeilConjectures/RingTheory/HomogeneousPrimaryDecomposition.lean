/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Homogeneous primary decomposition with localization data

Source: Altman--Kleiman, A Term of Commutative Algebra, Theorem 20.27,
Exercises 20.25--20.26 and Chapter 18, especially Proposition 18.24 and Theorem 18.25.
(blueprint: lem-sfb-homogeneous-primary-decomposition)
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- A homogeneous polynomial ideal has an irredundant homogeneous primary decomposition,
including its minimal primes, radical-power bounds, and localization identities.
Source: Altman--Kleiman, Theorem 20.27, Exercises 20.25--20.26, and Chapter 18.
(blueprint: lem-sfb-homogeneous-primary-decomposition)

Proof: (1) The regularity of a polynomial ring over a field gives Noetherianity
[lem-weil-pbc-polynomial-ring-field-regular-ring]. For the unit ideal take the empty
family. Otherwise take a finite primary decomposition
[lem-per-noetherian-primary-decomposition]. (2) Replace each primary factor by its
homogeneous core [lem-sfb-primary-homogeneous-core]. Every component of an element of
I belongs to each original factor, so the cores still intersect to I. (3) Their radicals
are homogeneous [lem-sfb-homogeneous-ideal-radical]. If uv belongs to a radical but u
does not, primaryness applied to u^m v^m shows that a positive power of v belongs to
the factor, proving primality. (4) Group factors with equal radicals by intersection:
taking the maximum of the finitely many exponents proves that the intersection has
the same radical and remains primary. (5) Delete redundant factors until the finite
list is irredundant. (6) A prime containing I contains some factor: otherwise the product
of elements chosen outside the prime from each factor lies in I but outside the prime.
It therefore contains the factor's radical; minimality gives equality for a minimal
prime. (7) Each radical is finitely generated, so
[lem-weil-pbc-fg-ideal-radical-power] gives a positive power contained in its factor.
(8) A fraction r/s lies in the extension of J exactly when tr belongs to J for some t
outside the localization prime, by the fraction relation
[def-weil-pbc-localization-at-prime]. (9) Multiply these finitely many denominators to
show localization commutes with this intersection. If a radical is not contained in
the localization prime, a power of an element outside the prime lies in its factor;
this element becomes a unit, so that extended factor is the unit ideal. (10) At a minimal
prime, distinctness of the radicals leaves just its own primary factor.
-/
theorem homogeneous_primary_decomposition (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hI : @Ideal.IsHomogeneous _ _ _ _ _ _
      (homogeneousSubmodule (Fin (n + 1)) k) _ _ gradedAlgebra I) :
    IsNoetherianRing (MvPolynomial (Fin (n + 1)) k) ∧
      ∃ (s : ℕ) (Q : Fin s → Ideal (MvPolynomial (Fin (n + 1)) k)),
        I = ⨅ a, Q a ∧
        (∀ a, Q a ≠ ⊤ ∧
          @Ideal.IsHomogeneous _ _ _ _ _ _
            (homogeneousSubmodule (Fin (n + 1)) k) _ _ gradedAlgebra (Q a) ∧
          (Q a).IsPrimary ∧ (Q a).radical.IsPrime ∧
          @Ideal.IsHomogeneous _ _ _ _ _ _
            (homogeneousSubmodule (Fin (n + 1)) k) _ _ gradedAlgebra (Q a).radical) ∧
        Function.Injective (fun a => (Q a).radical) ∧
        (∀ a, (⨅ (b : Fin s) (_ : b ≠ a), Q b) ≠ I) ∧
        (∀ p ∈ I.minimalPrimes, ∃ a, (Q a).radical = p) ∧
        (∀ a, ∃ h : ℕ, 1 ≤ h ∧ (Q a).radical ^ h ≤ Q a) ∧
        (∀ (p : Ideal (MvPolynomial (Fin (n + 1)) k)) [p.IsPrime], I ≤ p →
          I.map (algebraMap _ (Localization.AtPrime p)) =
            ⨅ (a : Fin s) (_ : (Q a).radical ≤ p),
              (Q a).map (algebraMap _ (Localization.AtPrime p)) ∧
          (∀ a, ¬ (Q a).radical ≤ p →
            (Q a).map (algebraMap _ (Localization.AtPrime p)) = ⊤) ∧
          (∀ b, p = (Q b).radical → I.IsMinimalPrime p →
            I.map (algebraMap _ (Localization.AtPrime p)) =
              (Q b).map (algebraMap _ (Localization.AtPrime p)))) := by
  sorry

end MvPolynomial
