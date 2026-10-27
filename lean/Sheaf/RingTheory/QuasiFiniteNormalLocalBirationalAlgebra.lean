module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away

/-!
# Quasi-finite birational algebras over a normal local ring

Source: Stacks Project, Varieties, Tag 0BFP,
`lemma-modification-normal-iso-over-codimension-1`, proof of (4), local algebra paragraph.
(blueprint: lem-sfb-quasifinite-normal-local-birational-algebra)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Localization

/-- A finite-type inclusion of domains with the same fraction field induces an isomorphism
on local rings at a quasi-finite prime whose contracted local ring is normal.

Source: Stacks Project, Varieties, Tag 0BFP,
`lemma-modification-normal-iso-over-codimension-1`, proof of (4), local algebra paragraph.
(blueprint: lem-sfb-quasifinite-normal-local-birational-algebra)

Proof:
1. Put p = q ∩ A and R = A_p. The common fraction field embeds R and C_q in K.
   Since a ∉ p implies a ∉ q, the canonical local map is the inclusion R ⊆ C_q
   (`def-weil-pbc-localization-at-prime`).
2. By `lem-weil-pbc-quasi-finite-at-finite-subalgebra-away`, choose a finite
   A-subalgebra B of C and g ∈ B outside q for which B_g → C_g is an isomorphism.
3. Each b ∈ B is integral over A by `lem-weil-pbc-finite-algebra-is-integral`,
   hence integral over R. Since K is also the fraction field of R, normality
   (`def-weil-pbc-normal-ring`) puts b in R. Thus B ⊆ R inside K.
4. Write g = a/s in R with s ∉ p. The equality sg = a holds in C because it
   holds in K. If a ∈ p, primeness of q and s ∉ q would give g ∈ q. Thus a ∉ p,
   so g⁻¹ = s/a ∈ R. Consequently C ⊆ C_g = B_g ⊆ R, using the fraction
   descriptions in `def-weil-pbc-localization-at-prime` and
   `def-weil-ring-localization-away`.
5. For c ∈ C outside q, write c = a/s in R with s ∉ p. Again sc = a in C,
   and a ∈ p would force c ∈ q. Therefore c⁻¹ = s/a belongs to R. Every fraction
   d/c in C_q lies in R, so R = C_q inside K. The inverse sends a fraction to
   the same quotient in R, proving bijectivity of the specified local map.
-/
theorem bijective_localRingHom_of_isQuasiFiniteAtPrime_of_isIntegrallyClosed
    (A : Type u) (C : Type v) (K : Type w)
    [CommRing A] [IsDomain A] [CommRing C] [IsDomain C] [Field K]
    [Algebra A C] [Algebra A K] [Algebra C K] [IsScalarTower A C K]
    [IsFractionRing A K] [IsFractionRing C K] [Algebra.FiniteType A C]
    (q : PrimeSpectrum C) (hq : Algebra.IsQuasiFiniteAtPrime A C q)
    [IsIntegrallyClosed (Localization.AtPrime (q.comap (algebraMap A C)).asIdeal)] :
    Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap A C)).asIdeal q.asIdeal
        (algebraMap A C) rfl) := by
  sorry

end Localization
