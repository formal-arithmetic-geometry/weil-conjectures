/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.RegularityRkGoesUp
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Regularity ascends along smooth ring maps

A smooth algebra over a regular ring is regular.

## Implementation details

`S` is Noetherian and flat over `R`, and the fibres are smooth over fields, hence regular
(Tag 00TT), so they satisfy every `(R_k)`. Since `R` satisfies every `(R_k)`, so does `S`
(Tag 033A), and a Noetherian local ring satisfying `(R_k)` for `k` at least its dimension is
regular.

## References

* [Stacks, Tag 07NF]
* [Stacks, Tags 00FN, 00TA, 00T4, 00TT, 033A, 00OD]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A smooth algebra over a regular ring is regular. -/
theorem isRegularRing_of_smooth
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Smooth R S] [IsRegularRing R] : IsRegularRing S := by
  have : IsNoetherianRing S := FiniteType.isNoetherianRing R S
  have hS (k : ℕ) : Ring.IsSerreR S k := by
    apply RingHom.regularity_rk_goes_up k
      (RingHom.flat_algebraMap_iff.mpr (Smooth.flat R S))
    · intro p hp
      obtain ⟨hsmooth, hregular⟩ :=
        smooth_fibre_regular_local (R := R) (S := S) ⟨p, hp⟩
      have : Smooth p.ResidueField (p.Fiber S) := hsmooth
      have : IsNoetherianRing (p.Fiber S) :=
        FiniteType.isNoetherianRing p.ResidueField (p.Fiber S)
      refine ⟨inferInstance, ?_⟩
      intro Q hQ _
      exact hregular ⟨Q, hQ⟩
    · intro p hp _
      infer_instance
  apply isRegularRing_iff.mpr
  intro q hq
  exact hS q.height.toNat q (le_of_eq
    (ENat.natCast_toNat q.height_ne_top_of_isPrime).symm)

end Algebra
