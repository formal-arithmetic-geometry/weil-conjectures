/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
import Mathlib.Algebra.CharP.Invertible
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.RingTheory.QuasiFinite.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.FormalFibreQuasiFiniteAscent
import WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiber
import WeilConjectures.RingTheory.RegularLocalLocalization

/-!
# Generic polynomial formal fibres of complete local domains

For a complete local domain `A` and a maximal ideal `q` of `A[X]` over the maximal ideal of `A`,
the formal fibre of `A[X]_q` over the zero prime is geometrically regular.

## Implementation details

Choose a regular complete local subring `A₀` with `A` finite over `A₀` (Tag 032D); Tag 07PP(1)
reduces to `A₀`. In characteristic zero the generic fibre is a localization of the regular
completion of `A₀[X]`. In positive characteristic `A₀` is a power series ring over a field and
Tag 07PR applies.

## References

* [Stacks, Tag 07PV] (paragraphs 3–5 of the proof)
* [Stacks, Tag 032D]
* [Stacks, Tag 07PP]
* [Stacks, Tag 07NF]
* [Stacks, Tag 07NY]
* [Stacks, Tag 07PR]
-/

@[expose] public section

universe u

namespace Polynomial

private theorem polynomial_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    let _ := Polynomial.algebra (R := R) (A := S)
    Module.Finite (Polynomial R) (Polynomial S) := by
  let _ := Polynomial.algebra (R := R) (A := S)
  exact Module.Finite.equiv
    (Algebra.IsPushout.equiv R (Polynomial R) S (Polynomial S)).toLinearEquiv

private theorem finite_generic_ascent
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (q : Ideal S) [q.IsPrime]
    (hbase :
      Algebra.IsGeometricallyRegular (⊥ : Ideal R).ResidueField
        ((⊥ : Ideal R).Fiber
          (AdicCompletion
            (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap (algebraMap R S))))
            (Localization.AtPrime (q.comap (algebraMap R S)))))) :
    Algebra.IsGeometricallyRegular (⊥ : Ideal S).ResidueField
      ((⊥ : Ideal S).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) := by
  have hqf : Algebra.IsQuasiFiniteAtPrime R S ⟨q, inferInstance⟩ := by
    dsimp [Algebra.IsQuasiFiniteAtPrime]
    exact isOpen_discrete _
  have h := RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime
    (R := R) (R' := S) (⊥ : Ideal S) q bot_le hqf
  apply h
  have hb (r : Ideal R) [r.IsPrime] (hr : r = ⊥) :
      Algebra.IsGeometricallyRegular r.ResidueField
        (r.Fiber
          (AdicCompletion
            (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap (algebraMap R S))))
            (Localization.AtPrime (q.comap (algebraMap R S))))) := by
    subst r
    exact hbase
  exact hb _ (Ideal.comap_bot_of_injective _ hinj)

private theorem cohen_charZero
    (Λ : Type u) [CommRing Λ] (p : ℕ) (hΛ : IsCohenRing p Λ) : CharZero Λ := by
  obtain ⟨hp, hdomain, hdvr, hm, _⟩ := hΛ
  have := hdomain
  have := hdvr
  have hirr : Irreducible (p : Λ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : Λ)).mpr hm
  rcases CharP.exists' Λ with hzero | ⟨l, hl, hchar⟩
  · exact hzero
  · have := hchar
    by_cases hpl : l = p
    · subst l
      exact False.elim (hirr.ne_zero (CharP.cast_eq_zero Λ p))
    · have hu : IsUnit (p : Λ) :=
        (CharP.isUnit_natCast_iff hl.out).mpr ((hp.dvd_iff_eq hl.out.ne_one).not.mpr (Ne.symm hpl))
      exact False.elim (hirr.not_isUnit hu)

private theorem regular_generic_charZero
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [CharZero A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A) :
    Algebra.IsGeometricallyRegular (⊥ : Ideal (Polynomial A)).ResidueField
      ((⊥ : Ideal (Polynomial A)).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  let K := (⊥ : Ideal (Polynomial A)).ResidueField
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal A q hq
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  have : IsRegularLocalRing C :=
    (AdicCompletion.isRegularLocalRing_iff (Localization.AtPrime q)).mp inferInstance
  have : IsRegularRing C :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal C)).2
  let T := TensorProduct (Polynomial A) C K
  let M := Algebra.algebraMapSubmonoid C (nonZeroDivisors (Polynomial A))
  have : IsLocalization M T :=
    IsLocalization.tensor (S := C) (A := K) (nonZeroDivisors (Polynomial A))
  have : IsRegularRing T := by
    apply RingTheory.isRegularRing_of_localization C T M (algebraMap C T)
    · exact IsLocalization.map_units T
    · intro y
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj M y
      obtain ⟨z, hz⟩ := IsLocalization.map_units T s
      refine ⟨r, s, ↑z⁻¹, z⁻¹.isUnit, ?_, ?_⟩
      · rw [← hz]
        exact z.mul_inv
      · calc
          y = (y * algebraMap C T s) * ↑z⁻¹ := by rw [← hz]; simp
          _ = algebraMap C T r * ↑z⁻¹ := by rw [hy]
    · intro r hr
      exact (IsLocalization.map_eq_zero_iff M T r).mp hr
  have hregular : IsRegularRing ((⊥ : Ideal (Polynomial A)).Fiber C) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm (Polynomial A) C K).toRingEquiv
  have : CharZero (⊥ : Ideal (Polynomial A)).ResidueField :=
    IsFractionRing.charZero_of_isFractionRing (Polynomial A)
  refine ⟨hregular.toIsNoetherian, ?_⟩
  intro L _ _ _ _
  have hb := IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    (⊥ : Ideal (Polynomial A)).ResidueField L
  let F := (⊥ : Ideal (Polynomial A)).Fiber
    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q))
  let e : F ≃ₐ[K] TensorProduct K L F :=
    AlgEquiv.ofBijective Algebra.TensorProduct.includeRight
      (Algebra.TensorProduct.includeRight_bijective hb)
  exact IsRegularRing.of_ringEquiv e.toRingEquiv

/-- The generic formal fibre of `A[X]` at a maximal ideal, over a complete local domain `A`, is
geometrically regular. -/
theorem completeLocalGenericFibre
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A) :
    Algebra.IsGeometricallyRegular (⊥ : Ideal (Polynomial A)).ResidueField
      ((⊥ : Ideal (Polynomial A)).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) := by
  obtain ⟨A₀, hreg, _hcomplete, hfinite, hm, _, _, hmodel⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular A
  have := hreg
  have := hfinite
  let _ := Polynomial.algebra (R := A₀) (A := A)
  have : Module.Finite (Polynomial A₀) (Polynomial A) := polynomial_finite A₀ A
  let q₀ := q.comap (algebraMap (Polynomial A₀) (Polynomial A))
  have : q₀.IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal q
  have hq₀ : q₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) =
      IsLocalRing.maximalIdeal A₀ := by
    change (q.comap (mapRingHom (algebraMap A₀ A))).comap C = _
    rw [Ideal.comap_comap, mapRingHom_comp_C, ← Ideal.comap_comap, hq]
    exact hm.symm
  apply finite_generic_ascent (Polynomial A₀) (Polynomial A)
    (map_injective _ Subtype.val_injective) q
  rcases hmodel with ⟨k, hk, n, ⟨e⟩⟩ | ⟨Λ, hΛ, n, p, hC, ⟨e⟩⟩
  · let _ := hk
    rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
    · have := hzero
      have : CharZero (MvPowerSeries (Fin n) k) :=
        charZero_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective
      have : CharZero A₀ := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
      exact regular_generic_charZero A₀ q₀ hq₀
    · have := hp
      have := hchar
      let E : MvPolynomial (Fin 1) (MvPowerSeries (Fin n) k) ≃+* Polynomial A₀ :=
        (MvPolynomial.uniqueAlgEquiv (MvPowerSeries (Fin n) k) (Fin 1)).toRingEquiv.trans
          (Polynomial.mapEquiv e.symm)
      let B := MvPolynomial (Fin 1) (MvPowerSeries (Fin n) k)
      have : IsDomain B := E.toMulEquiv.isDomain
      have : IsNoetherianRing B :=
        isNoetherianRing_of_ringEquiv (Polynomial A₀) E.symm
      let _ : Algebra B (Polynomial A₀) := E.toRingHom.toAlgebra
      have : Module.Finite B (Polynomial A₀) := E.finite
      apply finite_generic_ascent B (Polynomial A₀) E.injective q₀
      exact (MvPowerSeries.formalFiber_polynomial_isGeometricallyRegular
        k p n 1 (q₀.comap E.toRingHom)).2
  · let _ := hΛ
    have : CharZero Λ := cohen_charZero Λ p hC
    have : CharZero (MvPowerSeries (Fin n) Λ) :=
      charZero_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective
    have : CharZero A₀ := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
    exact regular_generic_charZero A₀ q₀ hq₀

end Polynomial
