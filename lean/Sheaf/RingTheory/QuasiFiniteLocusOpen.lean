module

public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.RingTheory.QuasiFiniteAtPrime
import Sheaf.RingTheory.FiniteRingMapQuasiFinite
import Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
import Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization

/-!
# Openness of the quasi-finite locus for a finite-type ring map

Source: Stacks Project, Algebra, Lemma Tag 00QA, label `lemma-quasi-finite-open`
(blueprint: lem-weil-pbc-ring-quasi-finite-locus-open).
-/

@[expose] public section

universe u v

namespace Algebra

/-- The quasi-finite locus of a finite-type ring map is open, and is locally
represented by localizations on which the map is quasi-finite at every prime.
Source: Stacks Project, Algebra, Lemma Tag 00QA
(blueprint: lem-weil-pbc-ring-quasi-finite-locus-open).

Proof (following Stacks Project, Algebra, Lemma Tag 00QA):
1. For a quasi-finite prime `q`,
   `lem-weil-pbc-quasi-finite-at-finite-subalgebra-away` gives a finite `A`-subalgebra
   `B'` and `g ∉ q` such that the canonical map `B'_g → B_g` is an isomorphism;
   finite generation is expressed by `def-weil-finitely-generated-module` and the
   localization by `def-weil-ring-localization-away`.
2. By `lem-weil-pbc-finite-ring-map-quasi-finite`, the finite map `A → B'` is of
   finite type and quasi-finite at every prime.
3. The localization `A → B_g` remains of finite type, since generators of `B`
   together with `g⁻¹` generate it.
4. For a prime of `B_g`, use the open immersion and prime correspondence from
   `lem-weil-pbc-principal-localization-open-immersion` to contract it to `B` and
   transport it through `B'_g ≅ B_g`; then
   `lem-weil-pbc-quasi-finite-at-prime-principal-localization` gives quasi-finiteness.
5. The isomorphism preserves the fibre rings and their distinguished primes, using
   `def-weil-pbc-localization-at-prime` and
   `lem-weil-pbc-fibre-ring-primes-bijection`, so quasi-finiteness holds at every
   prime of `B_g`.
6. Every basic open `D(g)` obtained this way lies in the quasi-finite locus, again by
   `lem-weil-pbc-quasi-finite-at-prime-principal-localization`; hence the locus is open.
   The same argument proves the converse local characterization.
-/
theorem isOpen_isQuasiFiniteAtPrime (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    IsOpen {q : PrimeSpectrum B | IsQuasiFiniteAtPrime A B q} ∧
      (IsOpen {q : PrimeSpectrum B | IsQuasiFiniteAtPrime A B q} ↔
        ∀ q : PrimeSpectrum B, IsQuasiFiniteAtPrime A B q →
          ∃ g : B, g ∉ q.asIdeal ∧
            ∀ p : PrimeSpectrum (Localization.Away g),
              IsQuasiFiniteAtPrime A (Localization.Away g) p) := by
  sorry

end Algebra
