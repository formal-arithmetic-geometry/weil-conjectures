/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.FormallySmoothAdicPowerSeriesMap

/-!
# Adically formally smooth local algebras over fields are regular

A Noetherian local algebra over a field, formally smooth for the maximal-ideal-adic topology,
is a regular local ring.

## Implementation details

Reduce to the prime field and pass to the completion, from which regularity descends. Choose a
coefficient field `K` and a basis `x_i` of `m/m²`, and let `T = K[[X_1, …, X_n]]`, so that
`A/m² ≅ T/n²`. Formal smoothness lifts `A → T/n²` successively through `T/n^(r+2) → T/n^(r+1)`,
and completeness of `T` gives a local map `f : A → T` (not necessarily `K`-linear). The
`f(x_i)` generate `n`, and completeness of `A` makes `f` surjective, so `dim A ≥ n`; Nakayama
gives `dim A ≤ n`.

## References

* [Stacks, Tag 07EI]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A Noetherian local algebra over a field, formally smooth for the maximal-ideal-adic
 topology, is a regular local ring. -/
theorem isRegularLocalRing_of_formallySmoothAdic (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsLocalRing A]
    (h : FormallySmoothAdic k A (IsLocalRing.maximalIdeal A)) : IsRegularLocalRing A := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing _
  have hB : FormallySmoothAdic k B (IsLocalRing.maximalIdeal B) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact h.adicCompletion k A _ (Ideal.fg_of_isNoetherianRing _)
  apply (AdicCompletion.isRegularLocalRing_iff A).mpr
  obtain ⟨f, hmax, hres⟩ :=
    exists_powerSeries_comparison_of_formallySmoothAdic k B hB
  let K := IsLocalRing.ResidueField B
  let d := (IsLocalRing.maximalIdeal B).spanFinrank
  let T := MvPowerSeries (Fin d) K
  have hK : IsField K := Field.toIsField K
  rcases MvPowerSeries.power_series_field_cohen_regular_complete d (Or.inl hK) with
    ⟨_, hnoeth, hdomain, hlocal, hvars, e, he, hcomplete, _, hdim⟩ | ⟨p, hp, _⟩
  · let : IsNoetherianRing T := hnoeth
    let : IsLocalRing T := hlocal
    let : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
    have hmap : Ideal.map f (IsLocalRing.maximalIdeal B) =
        IsLocalRing.maximalIdeal T := hmax.trans hvars.symm
    have : IsHausdorff (Ideal.map f (IsLocalRing.maximalIdeal B)) T := by
      rw [hmap]
      infer_instance
    have hf : Function.Surjective f :=
      surjective_of_mk_map_comp_surjective (I := IsLocalRing.maximalIdeal B) f hres
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    calc
      ((IsLocalRing.maximalIdeal B).spanFinrank : WithBot ℕ∞) = ringKrullDim T :=
        hdim.symm
      _ ≤ ringKrullDim B := ringKrullDim_le_of_surjective f hf
  · obtain ⟨_, hdomain, hdvr, _⟩ := hp
    let := hdomain
    let := hdvr
    exact False.elim (IsDiscreteValuationRing.not_isField K hK)

end Algebra
