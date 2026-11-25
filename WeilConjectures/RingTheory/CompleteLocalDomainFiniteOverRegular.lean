/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.CompleteLocalDomainResidueParameterMap
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Complete local domains finite over regular subrings

A Noetherian complete local domain `R` is finite over a regular complete local subring `R₀`
with the same residue field, where `R₀` is a power series ring over a field or over a Cohen ring.

## Implementation details

The subring is the image of the power series ring `A = Λ[[X₁, …, X_n]]` over a coefficient ring
`Λ` under the map of `complete_local_domain_residue_parameter_map`. Finiteness follows from
completeness of `A`, and injectivity of `A → R` from a Krull dimension count.

## References

* [Stacks, Tag 032D]
* [Stacks, Tag 0327] (Cohen rings)
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace IsLocalRing

/-- A Noetherian complete local domain `R` is finite over a regular complete local subring `R₀`
whose maximal ideal is the contraction of that of `R` and whose residue field maps isomorphically
onto that of `R`; moreover `R₀` is a power series ring over a field or over a Cohen ring. -/
theorem complete_local_domain_finite_over_regular
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    ∃ (R₀ : Subring R), ∃ hreg : IsRegularLocalRing R₀,
      let _ := hreg.toIsLocalRing
      IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀ ∧
      Module.Finite R₀ R ∧
      IsLocalRing.maximalIdeal R₀ =
        Ideal.comap R₀.subtype (IsLocalRing.maximalIdeal R) ∧
    ∃ e : (R₀ ⧸ IsLocalRing.maximalIdeal R₀) ≃+*
          (R ⧸ IsLocalRing.maximalIdeal R),
        (∀ x : R₀,
          e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R₀) x) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (R₀.subtype x)) ∧
      ((∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
          let _ := h
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
          let _ := h
          ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) Λ))) := by
  obtain ⟨n, Λ, hΛring, hlocal, halg, hΛ, hdim, hsep, hquot, hres⟩ :=
    complete_local_domain_residue_parameter_map R
  let := hΛring
  let A := MvPowerSeries (Fin n) Λ
  let : IsLocalRing A := hlocal
  let : Algebra A R := halg
  let : IsHausdorff (maximalIdeal A) R := hsep
  let : Module.Finite (A ⧸ maximalIdeal A)
      (R ⧸ (maximalIdeal A • ⊤ : Submodule A R)) := hquot
  have hproperties := MvPowerSeries.power_series_field_cohen_regular_complete n hΛ
  have hregular : IsRegularLocalRing A := by
    rcases hproperties with ⟨_, _, _, _, _, e, _, _, hreg, _⟩ |
      ⟨_, _, _, _, _, _, e, _, _, hreg, _⟩
    · exact hreg
    · exact hreg
  have hcomplete : IsAdicComplete (maximalIdeal A) A := by
    rcases hproperties with ⟨_, _, _, _, _, e, _, hcomp, _, _⟩ |
      ⟨_, _, _, _, _, _, e, _, hcomp, _, _⟩
    · exact hcomp
    · exact hcomp
  let : IsRegularLocalRing A := hregular
  let : IsAdicComplete (maximalIdeal A) A := hcomplete
  let : Module.Finite A R :=
    (Module.finite_and_span_eq_top_of_adicComplete (maximalIdeal A) R).1
  let f := algebraMap A R
  have hfinite : f.Finite := by
    exact (RingHom.finite_algebraMap).mpr inferInstance
  have hrange : f.range.subtype.Finite :=
    RingHom.Finite.of_comp_finite (f := f.rangeRestrict) (by
      convert hfinite using 1
      ext x
      rfl)
  have hbound : ringKrullDim R ≤ ringKrullDim f.range := by
    let : Module.Finite f.range R := hrange
    let : Algebra.IsIntegral f.range R := inferInstance
    exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f.range.subtype)
      (fun p q hpq ↦ Ideal.IsIntegral.under_lt_under hpq)
  have hdomain : IsDomain A := by
    rcases hproperties with ⟨_, _, hdom, _, _⟩ | ⟨_, _, _, hdom, _, _⟩
    · exact hdom
    · exact hdom
  let : IsDomain A := hdomain
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    by_contra hne
    have hsucc := ringKrullDim_succ_le_of_surjective f.rangeRestrict
      f.rangeRestrict_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
      (show f.rangeRestrict x = 0 from Subtype.ext hx)
    have hbad : ringKrullDim R + 1 ≤ ringKrullDim R := by
      calc
        ringKrullDim R + 1 ≤ ringKrullDim f.range + 1 := add_le_add hbound le_rfl
        _ ≤ ringKrullDim A := hsucc
        _ = ringKrullDim R := hdim
    have hnatdim : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
      rcases hproperties with ⟨_, _, _, _, _, _, _, _, _, hd⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hd⟩
      · exact ⟨n, hdim.symm.trans hd⟩
      · exact ⟨n + 1, hdim.symm.trans hd⟩
    obtain ⟨d, hd⟩ := hnatdim
    rw [hd] at hbad
    exact (lt_irrefl (d : WithBot ℕ∞))
      (ENat.WithBot.add_one_le_natCast_iff.mp hbad)
  let e : A ≃+* f.range :=
    RingEquiv.ofBijective f.rangeRestrict
      ⟨fun x y h ↦ hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let : IsRegularLocalRing f.range := IsRegularLocalRing.of_ringEquiv e
  have hcompRange : IsAdicComplete (maximalIdeal f.range) f.range := by
    have hmap : (maximalIdeal A).map e = maximalIdeal f.range :=
      map_ringEquiv_maximalIdeal e
    rw [← hmap]
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal A) e).mpr hcomplete
  have hmax : maximalIdeal f.range = (maximalIdeal R).comap f.range.subtype := by
    let : Module.Finite f.range R := hrange
    let : Algebra.IsIntegral f.range R := inferInstance
    exact (eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := f.range)
        (maximalIdeal R))).symm
  let q := Ideal.quotientMap (maximalIdeal R) f.range.subtype hmax.le
  have hq : Function.Bijective q := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply Ideal.Quotient.eq.mpr
      rw [hmax]
      change (a - b : f.range).val ∈ maximalIdeal R
      exact Ideal.Quotient.eq.mp hxy
    · intro y
      obtain ⟨a, ha⟩ := hres y
      exact ⟨Ideal.Quotient.mk _ (f.rangeRestrict a), ha⟩
  let eres := RingEquiv.ofBijective q hq
  refine ⟨f.range, inferInstance, hcompRange, hrange, hmax, eres, ?_, ?_⟩
  · intro x
    rfl
  · rcases hΛ with hfield | ⟨p, hp⟩
    · exact Or.inl ⟨Λ, hfield.toField, n, ⟨e.symm⟩⟩
    · exact Or.inr ⟨Λ, hΛring, n, p, hp, ⟨e.symm⟩⟩


end IsLocalRing
