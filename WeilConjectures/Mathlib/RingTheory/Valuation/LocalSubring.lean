/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation subrings and the domination order

Two consequences of the maximality of valuation subrings in the domination order of
local subrings (`ValuationSubring.isMax_toLocalSubring`, Stacks Project Tag 052K) and
of the Chevalley extension theorem (`LocalSubring.exists_le_valuationSubring`, Stacks
Project Tag 00IA):

- `ValuationSubring.comap_eq_of_le_comap`: if a valuation subring `B` of a field
  extension `L` of `K` dominates the image of a valuation subring `A ⊆ K`, then
  `K ∩ B = A`, i.e. `B.comap f = A`;
- `ValuationSubring.exists_comap_eq`: every valuation subring `A ⊆ K` extends to a
  valuation subring `B` of any field extension `L` with `K ∩ B = A`.
-/

@[expose] public section

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

/-- **Intersection with a dominating valuation ring** (consequence of Stacks Project
Tag 052K): if a valuation subring `B` of a field extension `L` of `K` dominates a
valuation subring `A ⊆ K` — that is, `A ≤ B.comap f` in the domination order of local
subrings of `K` — then `K ∩ B = A`, i.e. `B.comap f = A`. -/
theorem comap_eq_of_le_comap (f : K →+* L) (A : ValuationSubring K)
    (B : ValuationSubring L) (h : A.toLocalSubring ≤ (B.comap f).toLocalSubring) :
    B.comap f = A :=
  ValuationSubring.toLocalSubring_injective
    (le_antisymm (A.isMax_toLocalSubring h) h)

/-- **Extension of a valuation ring to a field extension** (Stacks Project Tag 00IA):
for every field extension `f : K ⟶ L` and every valuation subring `A ⊆ K` there is a
valuation subring `B ⊆ L` with `K ∩ B = A`; its fraction field is `L`, as for every
valuation subring of `L`. The witness produced by Mathlib's Chevalley extension
theorem (`IsLocalRing.exists_factor_valuationRing`) dominates the image of `A`, and
`comap_eq_of_le_comap` upgrades the domination to the equality `B.comap f = A`. -/
theorem exists_comap_eq (f : K →+* L) (A : ValuationSubring K) :
    ∃ B : ValuationSubring L, B.comap f = A := by
  obtain ⟨B, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp A.subtype)
  have hsub : A.toLocalSubring.toSubring ≤ (B.comap f).toLocalSubring.toSubring :=
    fun x hx ↦ hmem ⟨x, hx⟩
  refine ⟨B, comap_eq_of_le_comap f A B ⟨hsub, ⟨fun a ha ↦ ?_⟩⟩⟩
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp ha
  -- the image of `a` in `B` is a unit with inverse the image of `v`
  have hval : (a : K) * (v : K) = 1 := by
    have := congrArg (Subtype.val : (B.comap f).toLocalSubring.toSubring → K) hv
    simpa using this
  have hBunit : IsUnit ((f.comp A.subtype).codRestrict B.toSubring hmem a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨f (v : K), v.2⟩, ?_⟩
    apply Subtype.ext
    change f (a : K) * f (v : K) = 1
    rw [← map_mul, hval, map_one]
  exact hloc.map_nonunit a hBunit

end ValuationSubring
