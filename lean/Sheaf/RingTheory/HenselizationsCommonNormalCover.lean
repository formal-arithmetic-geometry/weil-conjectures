/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.HenselizationAtPrime
import Mathlib.Algebra.MvPolynomial.Counit
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Maps
/-!
# A common normal-domain cover of two ordinary henselizations
Source: Stacks Project, Algebra, Tag 05WQ, together with Tag 00CT and the
polynomial normal-domain presentation in Huebner--Schmidt, Theorem 6.3, p. 13
(blueprint: lem-trf-henselizations-common-normal-cover).
-/
@[expose] public section
universe u
namespace RingHom
/-- Every commutative ring admits a common normal-domain cover whose localized maps at
 two chosen primes extend to local surjections of ordinary henselizations.
Source: Stacks Project, Algebra, Tags 030A, 00CT and 05WQ; the quotient reduction of
Huebner--Schmidt, Theorem 6.3, p. 13 (blueprint: lem-trf-henselizations-common-normal-cover).
Proof: choose the normal polynomial domain `ℤ[X a : a ∈ A]` and its surjective evaluation
map (`lem-trf-normal-polynomial-surjection`). For each chosen prime `p`, take its inverse
image `q` in `P`. The canonical localization map is local and surjective by localization
of a quotient (`lem-weil-pbc-localization-at-prime-of-quotient`). Its kernel lies in the
maximal ideal. Apply quotient compatibility of ordinary henselization (Tag 05WQ,
`lem-trf-henselization-quotient-at-prime`) to obtain the local surjection of henselizations.
The quotient construction gives the two compatibility equations with the localization
and the original ring map. Do this independently for the two primes. No finite-generation
hypothesis on `A` is used. -/
theorem exists_common_normal_henselization_cover
    (A : Type u) [CommRing A] (p₁ p₂ : Ideal A) [p₁.IsPrime] [p₂.IsPrime] :
    ∃ (P : Type u) (_ : CommRing P) (_ : IsDomain P) (_ : IsIntegrallyClosed P)
      (π : P →+* A),
      Function.Surjective π ∧
        ∀ (p : Ideal A) [hp : p.IsPrime] (_ : p = p₁ ∨ p = p₂)
          (q : Ideal P) [hq : q.IsPrime] (hqp : q = Ideal.comap π p),
          ∃ (HP HA : Type u) (_ : CommRing HP) (_ : CommRing HA)
            (_ : Algebra (Localization.AtPrime q) HP)
            (_ : Algebra (Localization.AtPrime p) HA)
            (_ : HenselianLocalRing HP) (_ : HenselianLocalRing HA)
            (_ : Algebra.IsHenselizationAtPrime P q HP)
            (_ : Algebra.IsHenselizationAtPrime A p HA)
            (φ : HP →+* HA),
            IsLocalHom φ ∧ Function.Surjective φ ∧
              IsLocalHom (Localization.localRingHom q p π hqp) ∧
              φ.comp (algebraMap (Localization.AtPrime q) HP) =
                (algebraMap (Localization.AtPrime p) HA).comp
                  (Localization.localRingHom q p π hqp) ∧
              φ.comp
                  ((algebraMap (Localization.AtPrime q) HP).comp
                    (algebraMap P (Localization.AtPrime q))) =
                (algebraMap (Localization.AtPrime p) HA).comp
                  ((algebraMap A (Localization.AtPrime p)).comp π) := by
  sorry
end RingHom
