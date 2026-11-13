/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SurjectiveOnStalks
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-! # Strict henselianity of prime localizations of a quotient

## References

* [Stacks Project, Tag 09ZC](https://stacks.math.columbia.edu/tag/09ZC)
-/

@[expose] public section

universe u

/-- Every prime localization of a quotient of a normal domain with separably closed
fraction field is strictly henselian (Stacks, Tags 09ZC, 05WS). -/
theorem gabber_quotient_localizations
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hsep : IsSepClosed (FractionRing R)) (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime p) := by
  let := hsep
  let P := p.comap (Ideal.Quotient.mk I)
  let A := Localization.AtPrime P
  have hP : P.primeCompl ≤ nonZeroDivisors R := P.primeCompl_le_nonZeroDivisors
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A P.primeCompl hP
  let g : A →+* FractionRing R :=
    IsLocalization.map _ (T := nonZeroDivisors R) (RingHom.id R) hP
  let := g.toAlgebra
  have : IsScalarTower R A (FractionRing R) := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp,
      RingHomCompTriple.comp_eq])
  have : IsFractionRing A (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization P.primeCompl A (FractionRing R) hP
  have : HenselianLocalRing A :=
    HenselianLocalRing.of_isSepClosed_fractionRing (FractionRing R)
  have : IsStrictlyHenselianLocalRing A :=
    ⟨IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing (FractionRing R)⟩
  let φ : A →+* Localization.AtPrime p :=
    Localization.localRingHom P p (Ideal.Quotient.mk I) rfl
  have hφ : Function.Surjective φ :=
    RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective p inferInstance
  have hker : RingHom.ker φ ≤ IsLocalRing.maximalIdeal A := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have hz : φ a = 0 := ha
    exact (hu.map φ).ne_zero hz
  obtain ⟨_, _, _, hstrict, _, _⟩ :=
    isStrictlyHenselianLocalRing_quotient.{u, u} A inferInstance (RingHom.ker φ) hker
  let := hstrict
  exact IsStrictlyHenselianLocalRing.of_ringEquiv (φ.quotientKerEquivOfSurjective hφ)
