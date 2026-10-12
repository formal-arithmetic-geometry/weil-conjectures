module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.CompleteLocalDomainParameterMap
import Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.FiniteOverCompleteRing
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.AdicCompletion.Topology

@[expose] public section

universe u
set_option autoImplicit false

namespace IsLocalRing

/--
The coefficient and parameter construction in Stacks Tag 032D produces a regular local
complete subring finite over the given complete local domain. This is the core intermediate
assertion used by the target theorem.
(blueprint: split-complete-local-domain-finite-over-regular-core)
-/
theorem complete_local_domain_finite_over_regular_core
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    ∃ (R₀ : Subring R), ∃ hreg : IsRegularLocalRing R₀,
      let _ := hreg.toIsLocalRing
      IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀ ∧ Module.Finite R₀ R := by
  obtain ⟨n, Λ, hΛring, hlocal, halg, hΛ, hdim, hsep, hquot⟩ :=
    complete_local_domain_parameter_map R
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
      (fun p q hpq ↦ Ideal.IsIntegral.comap_lt_comap hpq)
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
  refine ⟨f.range, inferInstance, ?_, hrange⟩
  have hmap : (maximalIdeal A).map e = maximalIdeal f.range :=
    map_ringEquiv_maximalIdeal e
  rw [← hmap]
  exact (IsAdicComplete.congr_ringEquiv (maximalIdeal A) e).mpr hcomplete

end IsLocalRing
