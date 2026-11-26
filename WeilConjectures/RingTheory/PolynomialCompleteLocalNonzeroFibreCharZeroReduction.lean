/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Polynomial.IsIntegral
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import WeilConjectures.RingTheory.FormalFibreQuasiFiniteAscent

/-! # Reduction to a regular complete local coefficient subring

The characteristic-zero formal-fibre statement for a complete local domain reduces to a regular
complete local subring over which the domain is finite.

## Implementation details

The polynomial extension `A₀[X] → A[X]` is finite, hence quasi-finite at `q`, and the contracted
prime is nonzero by `Ideal.under_ne_bot`. In characteristic zero purely inseparable extensions
are trivial, so regularity of the contracted fibre is geometric regularity; Tag 07PP(1)
transfers it to the original fibre.

## References

* [Stacks, Tag 07PV] (paragraphs 3–4 of the proof)
* [Stacks, Tag 032D]
* [Stacks, Tag 07PP]
-/

@[expose] public section

universe u

private theorem geometricallyRegular_charZero
    (k B : Type u) [Field k] [CharZero k] [CommRing B] [Algebra k B]
    [IsRegularRing B] : Algebra.IsGeometricallyRegular k B := by
  refine ⟨inferInstance, ?_⟩
  intro L hL aL hfin hpure
  let e : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L)
    (IsPurelyInseparable.bijective_algebraMap_of_isSeparable k L)
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : B ≃ₐ[k] B)).trans
      (Algebra.TensorProduct.lid k B)).symm.toRingEquiv

namespace Polynomial

/-- Reduction of the characteristic-zero formal-fibre statement to a regular complete local
subring `A₀` over which `A` is finite: if the contracted formal fibre over `A₀` is regular, the
original formal fibre is geometrically regular. -/
theorem completeLocalNonzeroFibreCharZero_reduction
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    [CharZero (Localization.AtPrime (⊥ : Ideal A))]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsNoetherianRing A₀)
      (_ : IsRegularLocalRing A₀) (_ : CharZero A₀)
      (_ : IsLocalRing A₀) (_ : IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀)
      (q₀ r₀ : Ideal (Polynomial A₀)) (_ : q₀.IsMaximal) (_ : r₀.IsPrime),
      q₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) = IsLocalRing.maximalIdeal A₀ ∧
      r₀ ≤ q₀ ∧ r₀ ≠ ⊥ ∧
      r₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) = ⊥ ∧
      (IsRegularRing (r₀.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q₀))
          (Localization.AtPrime q₀))) →
       Algebra.IsGeometricallyRegular r.ResidueField
        (r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)))) := by
  have : CharZero A := (algebraMap A (Localization.AtPrime (⊥ : Ideal A))).charZero
  obtain ⟨A₀, hreg, hcomplete, hfinite, hmax, _⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular A
  let : IsRegularLocalRing A₀ := hreg
  let : IsLocalRing A₀ := hreg.toIsLocalRing
  let : IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀ := hcomplete
  let : Module.Finite A₀ A := hfinite
  let : Algebra (Polynomial A₀) (Polynomial A) := Polynomial.algebra A₀ A
  have : Algebra.IsIntegral (Polynomial A₀) (Polynomial A) := ⟨fun p ↦
    Polynomial.isIntegral_iff_isIntegral_coeff.mpr
      (fun n ↦ Algebra.IsIntegral.isIntegral (p.coeff n))⟩
  have : Algebra.FiniteType (Polynomial A₀) (Polynomial A) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A₀ (Polynomial A₀) (Polynomial A)
  have : Module.Finite (Polynomial A₀) (Polynomial A) := Algebra.IsIntegral.finite
  let q₀ := q.comap (algebraMap (Polynomial A₀) (Polynomial A))
  let r₀ := r.comap (algebraMap (Polynomial A₀) (Polynomial A))
  have : q₀.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal q
  have : r₀.IsPrime := Ideal.comap_isPrime _ r
  have hc : (algebraMap (Polynomial A₀) (Polynomial A)).comp
      (Polynomial.C : A₀ →+* Polynomial A₀) =
      (Polynomial.C : A →+* Polynomial A).comp A₀.subtype := by
    ext x
    simp only [RingHom.comp_apply, Polynomial.algebraMap_def, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
    rfl
  have hq₀ : q₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) =
      IsLocalRing.maximalIdeal A₀ := by
    change (q.comap _).comap _ = _
    rw [hmax, ← hq, Ideal.comap_comap, Ideal.comap_comap, hc]
  have hr₀A : r₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) = ⊥ := by
    change (r.comap _).comap _ = _
    rw [Ideal.comap_comap, hc, ← Ideal.comap_comap, hrA]
    exact (RingHom.injective_iff_ker_eq_bot A₀.subtype).mp A₀.subtype_injective
  refine ⟨A₀, inferInstance, inferInstance, inferInstance, hreg, inferInstance,
    inferInstance, hcomplete, q₀, r₀, inferInstance, inferInstance,
    hq₀, Ideal.comap_mono hrq, Ideal.under_ne_bot (Polynomial A₀) hr, hr₀A, ?_⟩
  intro hregular
  have : CharZero r₀.ResidueField := by
    apply charZero_of_inj_zero
    intro n hn
    have hz : (n : A₀) = 0 := by
      have hm : (n : A₀) ∈ r₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) := by
        change Polynomial.C (n : A₀) ∈ r₀
        apply Ideal.algebraMap_residueField_eq_zero.mp
        simpa using hn
      simpa [hr₀A] using hm
    exact Nat.cast_eq_zero.mp hz
  have : IsRegularRing
      (r₀.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q₀))
        (Localization.AtPrime q₀))) := hregular
  obtain ⟨hft, hquasi⟩ :=
    Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite (Polynomial A₀) (Polynomial A)
  let : Algebra.FiniteType (Polynomial A₀) (Polynomial A) := hft
  apply RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime r q hrq
    (hquasi ⟨q, inferInstance⟩)
  exact geometricallyRegular_charZero r₀.ResidueField _

end Polynomial
