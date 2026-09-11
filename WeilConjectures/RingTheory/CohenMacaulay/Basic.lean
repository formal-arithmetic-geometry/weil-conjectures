/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.Depth.Basic

/-!
# Cohen–Macaulay local rings

A Noetherian local ring `R` is *Cohen–Macaulay* if its depth along the maximal ideal, as a module
over itself, is its Krull dimension.

## Design

`Module.depth (maximalIdeal R) R` is a natural number (`Module.depth_ne_top`) and `ringKrullDim R`
lives in `WithBot ℕ∞`, so the equation defining the condition is stated after coercing the depth,
exactly as `IsRegularLocalRing` states `(maximalIdeal R).spanFinrank = ringKrullDim R`. The
inequality `≤` always holds (`Module.depth_le_ringKrullDim`), so the condition has content only in
the direction `ringKrullDim R ≤ depth`; `IsCohenMacaulayLocalRing.of_ringKrullDim_le_depth` and
`IsCohenMacaulayLocalRing.of_isRegular` are the two constructors that exploit this, and they are
how the condition should be checked in practice.

Following `IsRegularLocalRing`, this is a class extending `IsLocalRing` and `IsNoetherianRing`
rather than a predicate on a ring already known to be Noetherian local.

## Main definitions and results

* `IsCohenMacaulayLocalRing`: the Cohen–Macaulay condition on a Noetherian local ring.
* `IsCohenMacaulayLocalRing.of_isRegular`: a regular sequence in the maximal ideal whose length is
  the Krull dimension exhibits the ring as Cohen–Macaulay.
* `IsCohenMacaulayLocalRing.exists_isRegular_length_eq_ringKrullDim`: conversely, a Cohen–Macaulay
  local ring carries a regular sequence in its maximal ideal of length its Krull dimension.
* `IsRegularLocalRing.isCohenMacaulayLocalRing`: a regular local ring is Cohen–Macaulay. **This is
  stated with a deliberate `sorry`**; see the `TODO` below.

## TODO

Prove `IsRegularLocalRing.isCohenMacaulayLocalRing` and make it an instance. The mathematical
route is standard but it needs two results about regular local rings that mathlib does not have at
`v4.33.1`, and which have to be proved by a simultaneous induction on the dimension: a regular
local ring is a domain, and the quotient of a regular local ring by an element of
`maximalIdeal R \ (maximalIdeal R) ^ 2` is again regular local. Given those two, the
induction here is short: in dimension zero the maximal ideal is `⊥`, so `R` is a field and both
sides vanish; in positive dimension pick `x ∈ maximalIdeal R` outside the square, note that it is
a nonzerodivisor because `R` is a domain, and combine
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` with
`Module.depth_quotSMulTop_add_one`.
-/

@[expose] public section

universe u

open IsLocalRing Module RingTheory.Sequence

variable (R : Type u) [CommRing R]

/-- A Noetherian local ring is *Cohen–Macaulay* if its depth along the maximal ideal, as a module
over itself, is its Krull dimension. The inequality `≤` is automatic
(`Module.depth_le_ringKrullDim`), so the content of the condition is the inequality `≥`. -/
class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R, IsNoetherianRing R where
  depth_maximalIdeal_eq_ringKrullDim :
    (Module.depth (maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R

lemma isCohenMacaulayLocalRing_iff [IsLocalRing R] [IsNoetherianRing R] :
    IsCohenMacaulayLocalRing R ↔
      (Module.depth (maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

namespace IsCohenMacaulayLocalRing

variable {R}

/-- To check that a Noetherian local ring is Cohen–Macaulay it suffices to bound its Krull
dimension by its depth: the reverse inequality is `Module.depth_le_ringKrullDim`. -/
lemma of_ringKrullDim_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (h : ringKrullDim R ≤ (Module.depth (maximalIdeal R) R : WithBot ℕ∞)) :
    IsCohenMacaulayLocalRing R :=
  ⟨le_antisymm depth_le_ringKrullDim h⟩

/-- A regular sequence in the maximal ideal whose length is at least the Krull dimension exhibits
a Noetherian local ring as Cohen–Macaulay. -/
lemma of_isRegular [IsLocalRing R] [IsNoetherianRing R] {rs : List R}
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (reg : IsRegular R rs)
    (h : ringKrullDim R ≤ (rs.length : ℕ∞)) : IsCohenMacaulayLocalRing R :=
  of_ringKrullDim_le_depth <| h.trans <| by
    exact_mod_cast WithBot.coe_le_coe.mpr (le_depth_of_isRegular mem reg)

/-- A Noetherian local ring of Krull dimension zero is Cohen–Macaulay. -/
lemma of_ringKrullDim_eq_zero [IsLocalRing R] [IsNoetherianRing R] (h : ringKrullDim R = 0) :
    IsCohenMacaulayLocalRing R :=
  of_ringKrullDim_le_depth <| h.trans_le <| by exact_mod_cast zero_le

variable (R) [IsCohenMacaulayLocalRing R]

lemma depth_eq_ringKrullDim :
    (Module.depth (maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R :=
  IsCohenMacaulayLocalRing.depth_maximalIdeal_eq_ringKrullDim

/-- A Cohen–Macaulay local ring carries a regular sequence in its maximal ideal whose length is
its Krull dimension. This is the concrete content of the condition, and the converse of
`IsCohenMacaulayLocalRing.of_isRegular`. -/
theorem exists_isRegular_length_eq_ringKrullDim :
    ∃ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular R rs ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨rs, mem, reg, hrs⟩ := Module.exists_isRegular_length_eq_depth (I := maximalIdeal R)
    (M := R)
  exact ⟨rs, mem, reg, by rw [← depth_eq_ringKrullDim R, ← hrs]; rfl⟩

end IsCohenMacaulayLocalRing

instance (priority := 100) (K : Type u) [Field K] : IsCohenMacaulayLocalRing K :=
  .of_ringKrullDim_eq_zero (ringKrullDim_eq_zero_of_field K)

/-- A regular local ring is Cohen–Macaulay.

This is stated with a deliberate `sorry`: the proof needs a regular system of parameters to be a
regular sequence, and mathlib `v4.33.1` has no theory of regular local rings beyond the definition
`IsRegularLocalRing` itself. See the `TODO` in the module docstring for the missing ingredients.
Once proved this should become an instance. -/
theorem IsRegularLocalRing.isCohenMacaulayLocalRing [IsRegularLocalRing R] :
    IsCohenMacaulayLocalRing R :=
  sorry
