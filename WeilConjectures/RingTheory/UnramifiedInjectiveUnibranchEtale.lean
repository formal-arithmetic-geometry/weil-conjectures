/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import WeilConjectures.DeligneLaumon.EtaleUnibranchDomainNeighbourhood
import WeilConjectures.SecDeligneLaumonA1.EtaleLocalDomainIdealContraction

/-! # An injective unramified local map over a unibranch domain is etale nearby

Source: Stacks Project, More on Algebra, Tag 0GSC.
(blueprint: lem-dl-a1-unramified-injective-unibranch-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

open AlgebraicGeometry

private theorem injective_of_etale_domain
    (A C L : Type u) [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [CommRing L] [IsLocalRing L] [Algebra A C] [Algebra A L]
    (het : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (φ : C →ₐ[A] L) (hinj : Function.Injective (algebraMap A L)) :
    Function.Injective φ := by
  classical
  let Q := (IsLocalRing.maximalIdeal L).comap φ.toRingHom
  let ψ : Localization.AtPrime Q →ₐ[A] L := IsLocalization.liftAlgHom
    (M := Q.primeCompl) (f := φ)
    (fun s ↦ IsLocalRing.notMem_maximalIdeal.mp s.property)
  apply (injective_iff_map_eq_zero φ).mpr
  intro c hc
  by_contra hcn
  have hcl : algebraMap C (Localization.AtPrime Q) c ≠ 0 :=
    fun h ↦ hcn ((IsLocalization.injective (Localization.AtPrime Q)
      Q.primeCompl_le_nonZeroDivisors) (by simpa using h))
  have hmem : algebraMap C (Localization.AtPrime Q) c ∈ RingHom.ker ψ.toRingHom := by
    change ψ (algebraMap C (Localization.AtPrime Q) c) = 0
    simpa [ψ] using hc
  have hker : RingHom.ker ψ.toRingHom ≠ ⊥ := by
    intro heq
    rw [heq, Ideal.mem_bot] at hmem
    exact hcl hmem
  obtain ⟨a, ha, hamem⟩ :=
    Ideal.comap_ne_bot_of_etale_localization A C het Q (RingHom.ker ψ.toRingHom) hker
  have haz : algebraMap A L a = 0 := by
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ψ.commutes] using hamem
  exact ha (hinj (by simpa using haz))

/-- The local algebra criterion used by Stacks Tag 0GS8. The input injection is from
A itself; it also makes the induced map from the localization at the contracted
prime injective, because all its denominators map to units.

Source: Stacks Project, More on Algebra, Tag 0GSC.
(blueprint: lem-dl-a1-unramified-injective-unibranch-etale).

Proof: The local structure theorem for unramified algebras gives b outside q and a
surjection from a standard etale A-algebra C onto B[1/b]. Pull back the prime induced
by q to Q in C. Its contraction is q ∩ A. Apply the etale unibranch domain-neighbourhood
lemma to obtain h outside Q with D = C[1/h] a domain. Localizing the surjection yields
a surjection D onto T = (B[1/b])[1/image(h)]. The localization of T at the marked prime
is canonically B_q, compatibly with the A-action. If the surjection D → T had nonzero
kernel, injectivity of localization in the domain D would give a nonzero kernel ideal
in D_Q. The nonzero-ideal contraction lemma for local etale domains produces a nonzero
a in A killed in B_q, contradicting the given injection. The surjection D → T is
therefore an A-algebra isomorphism, and T is etale over A. Write image(h) as c/b^n.
Its marked prime avoids it, hence c is outside q; localizing B at b*c gives precisely
T. Transport etaleness across this localization equivalence to obtain g = b*c.
No finite-presentation assumption on B is used: the isomorphism with the etale
algebra supplies finite presentation on the resulting principal neighbourhood. -/
theorem exists_etale_away_of_unramified_injective_unibranch
    (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [FiniteType A B] (q : Ideal B) [q.IsPrime] [IsUnramifiedAt A q]
    (hinj : Function.Injective (algebraMap A (Localization.AtPrime q)))
    (hgeom : ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime (q.under A))) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime (q.under A))) K]
      [Algebra (Localization.AtPrime (q.under A)) K]
      [IsScalarTower (Localization.AtPrime (q.under A))
        (IsLocalRing.ResidueField (Localization.AtPrime (q.under A))) K]
      [CommRing H] [Algebra (Localization.AtPrime (q.under A)) H],
      StrictHenselizationPresentationIn.{u, v} (Localization.AtPrime (q.under A)) K H →
        IrreducibleSpace (PrimeSpectrum H)) :
    ∃ g : B, g ∉ q ∧ Etale A (Localization.Away g) := by
  classical
  obtain ⟨b, hb, P, φ, hφ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) q
  let B' := Localization.Away b
  let L := Localization.AtPrime q
  let ρ : B' →ₐ[A] L := IsLocalization.liftAlgHom
    (M := Submonoid.powers b) (f := IsScalarTower.toAlgHom A B L)
    (fun s ↦ by
      obtain ⟨n, hn⟩ := s.property
      change IsUnit (algebraMap B L s.val)
      rw [← hn, map_pow]
      exact (IsLocalization.map_units L (⟨b, hb⟩ : q.primeCompl)).pow n)
  let χ := ρ.comp φ
  let Q := (IsLocalRing.maximalIdeal L).comap χ.toRingHom
  have hp : Q.comap (algebraMap A P.Ring) = q.under A := by
    ext a
    change χ (algebraMap A P.Ring a) ∈ IsLocalRing.maximalIdeal L ↔ _
    rw [χ.commutes, IsScalarTower.algebraMap_apply A B L]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff L q _
  have hCet : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    change (algebraMap A P.Ring).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨h, hh, hD⟩ := etale_unibranch_domain_neighbourhood
    A P.Ring hCet Q (q.under A) hp hgeom
  let D := Localization.Away h
  let T := Localization.Away (φ h)
  have : IsDomain D := hD
  let ψ : D →ₐ[A] T := IsLocalization.Away.mapₐ D T φ h
  have hψsurj : Function.Surjective ψ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective h hφ
  have huh : IsUnit (χ h) := IsLocalRing.notMem_maximalIdeal.mp hh
  let δ : D →ₐ[A] L := IsLocalization.liftAlgHom
    (M := Submonoid.powers h) (f := χ) (fun s ↦ by
      obtain ⟨n, hn⟩ := s.property
      rw [← hn, map_pow]
      exact huh.pow n)
  let ε : T →ₐ[A] L := IsLocalization.liftAlgHom
    (M := Submonoid.powers (φ h)) (f := ρ) (fun s ↦ by
      obtain ⟨n, hn⟩ := s.property
      rw [← hn, map_pow]
      exact huh.pow n)
  have : Algebra.Etale A D := Algebra.Etale.comp A P.Ring D
  have hDet : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    change (algebraMap A D).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hδinj := injective_of_etale_domain A D L hDet δ hinj
  have hcomp : ε.comp ψ = δ := by
    apply IsLocalization.algHom_ext (Submonoid.powers h)
    apply AlgHom.ext
    intro c
    change ε (ψ (algebraMap P.Ring D c)) = δ (algebraMap P.Ring D c)
    simp [δ, ε, ψ, χ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]
    rfl
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hδinj
    rw [← hcomp]
    exact congrArg ε hxy
  have : Algebra.Etale A T :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
  let c := (IsLocalization.Away.sec b (φ h)).1
  have hassoc : Associated (algebraMap B B' c) (φ h) :=
    IsLocalization.Away.associated_sec_fst b (φ h)
  have huc : IsUnit (algebraMap B L c) := by
    have hh' : IsUnit (ρ (φ h)) := huh
    have hh'' := ((hassoc.map ρ.toRingHom).isUnit_iff).mpr hh'
    simpa [ρ] using hh''
  have hc : c ∉ q := (IsLocalization.AtPrime.isUnit_to_map_iff L q c).mp huc
  have : IsLocalization.Away (b * c) T :=
    IsLocalization.Away.mul_of_associated b c (φ h) hassoc
  refine ⟨b * c, fun hbc ↦ ((inferInstance : q.IsPrime).mem_or_mem hbc).elim hb hc, ?_⟩
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (b * c)) T
      (Localization.Away (b * c))).restrictScalars A)

end Algebra
