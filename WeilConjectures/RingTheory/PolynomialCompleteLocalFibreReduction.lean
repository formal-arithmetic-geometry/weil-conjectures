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
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.PolynomialQuotientCompletionFibreIso
import WeilConjectures.RingTheory.GeometricRegularityFieldIso

/-!
# Reduction of polynomial completion fibres to complete local domains

Each fibre of the completion of `S[X]_Q`, for a complete local Noetherian ring `S`, is
identified with a fibre over a prime lying over zero for a complete local domain quotient of `S`.

## Implementation details

For a prime `r` with `p = r ∩ S`, the quotient `A = S / p` is a complete local domain; localizing
the coefficient quotient identifies `A[X]_q` with `T / p T`, and completion of a quotient
identifies its completion with `C / p C`. Since `p` annihilates the residue field, the fibres
agree. The witness `A` is this actual quotient ring.

## References

* [Stacks, Tag 07PV] (paragraph 2 of the proof)
* [Stacks, Tag 07PN]
* [Stacks, Tag 00E3]
* [Stacks, Tag 00C9]
* [Stacks, Tag 00MA]
* [Stacks, Tag 0325]
* [Stacks, Tag 07BH]
-/

@[expose] public section

universe u

namespace Polynomial

/-- Each fibre of the localized polynomial completion transports to a polynomial
formal fibre above zero over a complete local domain. -/
theorem exists_completeLocalDomain_fibre_reduction
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (hQ : Q.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S)
    (s : Ideal (Localization.AtPrime Q)) [s.IsPrime] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A) (_ : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
      (q r : Ideal (Polynomial A)) (_ : q.IsMaximal) (_ : r.IsPrime),
      q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A ∧
      r ≤ q ∧ r.comap (Polynomial.C : A →+* Polynomial A) = ⊥ ∧
      (Algebra.IsGeometricallyRegular r.ResidueField
        (r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) →
        Algebra.IsGeometricallyRegular s.ResidueField
          (s.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
            (Localization.AtPrime Q)))) := by
  let T := Localization.AtPrime Q
  let r₀ : Ideal (Polynomial S) := s.comap (algebraMap (Polynomial S) T)
  have : r₀.IsPrime := inferInstance
  have hr₀Q : r₀ ≤ Q := by
    have h := Ideal.comap_mono
      (f := algebraMap (Polynomial S) T) (IsLocalRing.le_maximalIdeal_of_isPrime s)
    exact h.trans_eq (IsLocalization.AtPrime.under_maximalIdeal T Q)
  let p : Ideal S := r₀.comap (Polynomial.C : S →+* Polynomial S)
  have : p.IsPrime := inferInstance
  let A := S ⧸ p
  have : IsDomain A := inferInstance
  have : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  obtain ⟨hnoeth, _, hmax, hcomplete⟩ := quotient_complete_local S p
    (Ideal.IsPrime.ne_top inferInstance)
  have : IsNoetherianRing A := hnoeth
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hcomplete
  let f : Polynomial S →+* Polynomial A := Polynomial.mapRingHom (Ideal.Quotient.mk p)
  have hf : Function.Surjective f :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ r₀ := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
    exact Ideal.map_comap_le
  let q : Ideal (Polynomial A) := Q.map f
  let r : Ideal (Polynomial A) := r₀.map f
  have : q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hf
    (hker.trans hr₀Q)
  have : r.IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hqQ : q.comap f = Q := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (hker.trans hr₀Q)]
  have hrr₀ : r.comap f = r₀ := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have hq : q.comap (Polynomial.C : A →+* Polynomial A) =
      IsLocalRing.maximalIdeal A := by
    have hmk : Function.Surjective (Ideal.Quotient.mk p) :=
      Ideal.Quotient.mk_surjective
    have hinj := Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p) hmk
    apply hinj
    rw [hmax, Ideal.comap_map_of_surjective (Ideal.Quotient.mk p) hmk,
      ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    have hpmax : p ≤ IsLocalRing.maximalIdeal S :=
      IsLocalRing.le_maximalIdeal_of_isPrime p
    rw [sup_eq_left.mpr hpmax]
    change (q.comap Polynomial.C).comap (Ideal.Quotient.mk p) = _
    rw [Ideal.comap_comap]
    have hcomm : (Polynomial.C : A →+* Polynomial A).comp (Ideal.Quotient.mk p) =
        f.comp (Polynomial.C : S →+* Polynomial S) := by
      ext x
      simp [f]
    rw [hcomm, ← Ideal.comap_comap, hqQ, hQ]
  have hr : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥ := by
    have hmk : Function.Surjective (Ideal.Quotient.mk p) :=
      Ideal.Quotient.mk_surjective
    have hinj := Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p) hmk
    apply hinj
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [Ideal.comap_comap]
    have hcomm : (Polynomial.C : A →+* Polynomial A).comp (Ideal.Quotient.mk p) =
        f.comp (Polynomial.C : S →+* Polynomial S) := by
      ext x
      simp [f]
    rw [hcomm, ← Ideal.comap_comap, hrr₀]
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q, r, inferInstance, inferInstance, hq,
    Ideal.map_mono hr₀Q, hr, ?_⟩
  intro hregular
  obtain ⟨σ, e, hcompat⟩ := exists_quotient_completion_fibre_iso S Q s p rfl q r rfl rfl
  exact Algebra.isGeometricallyRegular_of_fieldIso σ e hcompat hregular

end Polynomial
