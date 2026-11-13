/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
import WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import Mathlib.Data.Finset.Max

/-! # Global Tor bounds on a quasi-compact scheme

## References

* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 09U9](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact scheme, local finite Tor dimension has a global finite bound.
-/
theorem hasFiniteTorDimension_of_locallyFinite (X : Scheme.{u}) [CompactSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : HasLocallyFiniteTorDimension X E) :
    HasFiniteTorDimension X E := by
  classical
  choose U hx a b hab htor using hE
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let lower := insert 0 (s.image a)
  let upper := insert 0 (s.image b)
  have hlow : lower.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hupp : upper.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let lo := lower.min' hlow
  let hi := upper.max' hupp
  have hlo : lo ≤ 0 := lower.min'_le 0 (Finset.mem_insert_self _ _)
  have hhi : 0 ≤ hi := upper.le_max' 0 (Finset.mem_insert_self _ _)
  refine ⟨lo, hi, hlo.trans hhi,
    torAmplitude_of_open_neighbourhoods X E lo hi (hlo.trans hhi) ?_⟩
  intro x
  have hxcover : ∃ y ∈ s, x ∈ U y := by
    have h := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at h
    exact h
  obtain ⟨y, hy, hxy⟩ := hxcover
  refine ⟨U y, hxy, fun G i h ↦ htor y G i ?_⟩
  have hla : lo ≤ a y := lower.min'_le _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hy))
  have hbu : b y ≤ hi := upper.le_max' _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem b hy))
  rcases h with h | h
  · exact Or.inl (h.trans_le hla)
  · exact Or.inr (hbu.trans_lt h)

end AlgebraicGeometry.Scheme
