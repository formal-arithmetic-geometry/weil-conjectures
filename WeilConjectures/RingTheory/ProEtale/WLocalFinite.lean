/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.ProEtale.IntegralLocal
public import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStrictHenselianAlgebraEtaleSection
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Finite algebras over w-strictly-local rings

## Main results

- `IsWLocalRing.of_isIntegral`: an integral algebra over a w-strictly-local ring is w-local.
- `IsWStrictlyLocalRing.of_finite`: a module-finite algebra over a w-strictly-local ring is
  w-strictly-local.
-/

@[expose] public section

universe u

open PrimeSpectrum AlgebraicGeometry CategoryTheory

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

namespace IsWLocalRing

/-- Let `B` be integral over `A` and `m` a maximal ideal of `A` with `A_m` henselian. Two maximal
ideals of `B` over `m` containing a common prime ideal `x` coincide.

The localization `S` of the domain `B ⧸ x` at `A ∖ m` is integral over the henselian local ring
`A_m`, hence local; both maximal ideals are the preimage of the maximal ideal of `S`. -/
lemma eq_of_le_of_comap_eq [Algebra.IsIntegral A B] (m : Ideal A) [m.IsMaximal]
    [HenselianLocalRing (Localization.AtPrime m)] (x c c' : Ideal B) [x.IsPrime]
    [c.IsMaximal] [c'.IsMaximal] (hxc : x ≤ c) (hxc' : x ≤ c')
    (hc : c.comap (algebraMap A B) = m) (hc' : c'.comap (algebraMap A B) = m) : c = c' := by
  have : Algebra.IsIntegral A (B ⧸ x) :=
    ⟨fun d ↦ by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
      exact (Algebra.IsIntegral.isIntegral (R := A) b).map (Ideal.Quotient.mkₐ A x)⟩
  let M := Algebra.algebraMapSubmonoid (B ⧸ x) m.primeCompl
  let S := Localization M
  have hM : M ≤ nonZeroDivisors (B ⧸ x) := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [IsScalarTower.algebraMap_apply A B (B ⧸ x), Ideal.Quotient.algebraMap_eq, Ne,
      Ideal.Quotient.eq_zero_iff_mem]
    intro h
    exact ha (hc ▸ hxc h)
  have : IsDomain S := IsLocalization.isDomain_localization hM
  have : Algebra.IsIntegral (Localization.AtPrime m) S := ⟨isIntegral_localization⟩
  have : IsLocalRing S :=
    IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain (R := Localization.AtPrime m)
  let φ : B →+* S := (algebraMap (B ⧸ x) S).comp (Ideal.Quotient.mk x)
  have key (d : Ideal B) [d.IsMaximal] (hxd : x ≤ d) (hd : d.comap (algebraMap A B) = m) :
      d = (IsLocalRing.maximalIdeal S).comap φ := by
    have hdp : (d.map (Ideal.Quotient.mk x)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have hdisj : Disjoint (M : Set (B ⧸ x)) (d.map (Ideal.Quotient.mk x)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ h
      rw [SetLike.mem_coe, IsScalarTower.algebraMap_apply A B (B ⧸ x),
        Ideal.Quotient.algebraMap_eq, Ideal.mem_quotient_iff_mem hxd] at h
      exact ha (hd ▸ h)
    have hP := IsLocalization.isPrime_of_isPrime_disjoint M S _ hdp hdisj
    refine Ideal.IsMaximal.eq_of_le ‹_›
      (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top) fun b hb ↦ ?_
    exact IsLocalRing.le_maximalIdeal hP.ne_top
      (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hb))
  rw [key c hxc hc, key c' hxc' hc']

/-- An integral algebra over a w-strictly-local ring is w-local: its closed points are the
preimage of the closed points of `Spec A`, and two closed specializations of a point lie over the
same closed point of `Spec A`, hence coincide by `IsWLocalRing.eq_of_le_of_comap_eq`. -/
theorem of_isIntegral [IsWStrictlyLocalRing A] [Algebra.IsIntegral A B] : IsWLocalRing B := by
  have hcl : closedPoints (PrimeSpectrum B) =
      comap (algebraMap A B) ⁻¹' closedPoints (PrimeSpectrum A) := by
    ext y
    simp only [Set.mem_preimage, mem_closedPoints_iff, isClosed_singleton_iff_isMaximal,
      comap_asIdeal]
    exact ⟨fun _ ↦ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _,
      fun h ↦ Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h⟩
  refine ⟨@WLocalSpace.mk _ _ inferInstance ?_ ?_⟩
  · intro x c c' hc hc' hxc hxc'
    have hcmem : c ∈ closedPoints (PrimeSpectrum B) := hc
    have hc'mem : c' ∈ closedPoints (PrimeSpectrum B) := hc'
    rw [hcl] at hcmem hc'mem
    have hm := WLocalSpace.eq_of_specializes hcmem hc'mem (hxc.map (continuous_comap _))
      (hxc'.map (continuous_comap _))
    rw [isClosed_singleton_iff_isMaximal] at hc hc'
    have hmax : (comap (algebraMap A B) c).asIdeal.IsMaximal :=
      (isClosed_singleton_iff_isMaximal _).1 hcmem
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (comap (algebraMap A B) c).asIdeal
    ext1
    exact eq_of_le_of_comap_eq (comap (algebraMap A B) c).asIdeal x.asIdeal c.asIdeal c'.asIdeal
      ((le_iff_specializes _ _).2 hxc) ((le_iff_specializes _ _).2 hxc') rfl
      (by rw [hm]; rfl)
  · rw [hcl]
    exact WLocalSpace.isClosed_closedPoints.preimage (continuous_comap _)

end IsWLocalRing

/-- Let `B'` be a module-finite algebra over a strictly henselian local ring `H`. Every étale
`B'`-algebra which is surjective on spectra has a retraction
(`AlgebraicGeometry.Scheme.finite_strict_henselian_algebra_etale_section`). -/
lemma exists_retraction_of_etale_of_finite_of_isStrictlyHenselianLocalRing (H B' : Type u)
    [CommRing H] [IsStrictlyHenselianLocalRing H] [CommRing B'] [Algebra H B']
    [Module.Finite H B'] (C : Type u) [CommRing C] [Algebra B' C] (hC : Algebra.Etale B' C)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B' C))) :
    ∃ f : C →+* B', f.comp (algebraMap B' C) = RingHom.id B' := by
  have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap B' C))) := by
    rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.2 hC
  obtain ⟨σ, hσ⟩ := AlgebraicGeometry.Scheme.finite_strict_henselian_algebra_etale_section H B'
    (Spec.map (CommRingCat.ofHom (algebraMap B' C))) hsurj
  refine ⟨(Spec.preimage σ).hom, ?_⟩
  have : Spec.map (CommRingCat.ofHom (algebraMap B' C) ≫ Spec.preimage σ) =
      Spec.map (𝟙 _) := by
    rw [Spec.map_comp, Spec.map_preimage, hσ, Spec.map_id]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

/-- A module-finite algebra `B` over a w-strictly-local ring `A` is w-strictly-local.

For a maximal ideal `n` of `B` over `m`, the localization `B'` of `B` at `A ∖ m` is finite over
the strictly henselian local ring `A_m`, so every surjective étale `B'`-algebra has a retraction
and the localizations of `B'` at maximal ideals are strictly henselian
(`IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction`); `B_n` is one of
them. -/
theorem IsWStrictlyLocalRing.of_finite [IsWStrictlyLocalRing A] [Module.Finite A B] :
    IsWStrictlyLocalRing B where
  toIsWLocalRing := IsWLocalRing.of_isIntegral (A := A)
  isStrictlyHenselianLocalRing_localization n _ := by
    set m := n.comap (algebraMap A B)
    have : m.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m
    let B' := Localization (Algebra.algebraMapSubmonoid B m.primeCompl)
    obtain ⟨P, hPmax, hPn⟩ : ∃ P : Ideal B', P.IsMaximal ∧ P.comap (algebraMap B B') = n := by
      have hdisj : Disjoint ((Algebra.algebraMapSubmonoid B m.primeCompl : Submonoid B) : Set B)
          n := by
        rw [Set.disjoint_left]
        rintro _ ⟨a, ha, rfl⟩ h
        exact ha h
      have hp := IsLocalization.isPrime_of_isPrime_disjoint _ B' n inferInstance hdisj
      have hc := IsLocalization.under_map_of_isPrime_disjoint _ B' (I := n) inferInstance hdisj
      obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hp.ne_top
      refine ⟨Q, hQ, ?_⟩
      have : n ≤ Q.comap (algebraMap B B') := hc.symm.le.trans (Ideal.comap_mono hle)
      exact ((‹n.IsMaximal›.eq_of_le (Ideal.comap_ne_top _ hQ.ne_top) this)).symm
    have : IsStrictlyHenselianLocalRing (Localization.AtPrime P) :=
      IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
        (exists_retraction_of_etale_of_finite_of_isStrictlyHenselianLocalRing
          (Localization.AtPrime m) B') P
    have key (q : Ideal B) [q.IsPrime] (hq : q = P.comap (algebraMap B B')) :
        IsStrictlyHenselianLocalRing (Localization.AtPrime q) := by
      subst hq
      exact IsStrictlyHenselianLocalRing.of_ringEquiv
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization _ P).symm.toRingEquiv
    exact key n hPn.symm
