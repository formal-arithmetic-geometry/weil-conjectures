/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
import all WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # Transition functions between section trivializations

## References

* [Stacks, Tag 01CY], [Stacks, Tag 01PV], [Stacks, Tag 01PY]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Two nonvanishing section opens of the same invertible module intersect in a basic
open; their transition coefficients multiply to one on the intersection. -/
theorem exists_nonvanishing_transition_functions {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (s t : M.val.presheaf.obj (Opposite.op ⊤))
    (U V : X.Opens) (hU : (U : Set X) = nonvanishingLocus M s)
    (hV : (V : Set X) = nonvanishingLocus M t) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), U ⊓ V = X.basicOpen f ∧
      (X.presheaf.map (homOfLE inf_le_left).op) f *
        (X.presheaf.map (homOfLE inf_le_right).op) g = 1 := by
  obtain ⟨U', hU', -, hs⟩ := nonvanishing_section_trivializes X M s
  obtain ⟨V', hV', -, ht⟩ := nonvanishing_section_trivializes X M t
  have hUU : U' = U := SetLike.coe_injective (hU'.trans hU.symm)
  have hVV : V' = V := SetLike.coe_injective (hV'.trans hV.symm)
  subst U' V'
  have hsgen : IsFreeGenerator (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
    intro W hWU
    constructor
    · intro a b hab
      simp only [presheaf_map_homOfLE_map_homOfLE] at hab
      exact (hs W hWU (a • M.presheaf.map (homOfLE le_top).op s)).unique rfl hab
    · intro m
      obtain ⟨a, ha, -⟩ := hs W hWU m
      exact ⟨a, by simpa only [presheaf_map_homOfLE_map_homOfLE] using ha.symm⟩
  obtain ⟨f, hf, -⟩ := hs U le_rfl
    (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
  obtain ⟨g, hg, -⟩ := ht V le_rfl
    (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s)
  refine ⟨f, g, ?_, ?_⟩
  · ext x
    by_cases hxU : x ∈ U
    · have hb := stalk_generator_bijective hsgen x hxU
      let ex := M.presheaf.germ U x hxU
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
      have hspan : Submodule.span (X.presheaf.stalk x) {ex} = ⊤ :=
        (Submodule.span_singleton_eq_top_iff (X.presheaf.stalk x) ex).2 hb.2
      have hmem (a : X.presheaf.stalk x) :
          a • ex ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) ↔
          a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
        rw [← hspan, Submodule.mem_smul_span_singleton]
        exact ⟨fun ⟨b, hbI, hba⟩ ↦ hb.1 hba ▸ hbI, fun ha ↦ ⟨a, ha, rfl⟩⟩
      have hgt : M.presheaf.germ ⊤ x trivial t =
          X.presheaf.germ U x hxU f • ex := by
        rw [← M.presheaf.germ_res_apply (homOfLE le_top) x hxU t, hf, germ_smul M]
      have hxV : x ∈ V ↔ x ∈ nonvanishingLocus M t := by rw [← hV]; rfl
      change (x ∈ U ∧ x ∈ V) ↔ _
      rw [and_iff_right hxU, hxV]
      change M.presheaf.germ ⊤ x trivial t ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) ↔ _
      rw [hgt, hmem, IsLocalRing.mem_maximalIdeal]
      change _ ↔ x ∈ X.basicOpen f
      rw [X.mem_basicOpen f x hxU]
      simp
    · exact ⟨fun hx ↦ False.elim (hxU hx.1),
        fun hx ↦ False.elim (hxU (X.basicOpen_le f hx))⟩
  · let W := U ⊓ V
    have hfW := congrArg (M.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op) hf
    have hgW := congrArg (M.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op) hg
    simp only [map_smul, presheaf_map_homOfLE_map_homOfLE] at hfW hgW
    obtain ⟨a, -, hua⟩ := hs W inf_le_left
      (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s)
    have hprod : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
        (X.presheaf.map (homOfLE inf_le_left).op f *
          X.presheaf.map (homOfLE inf_le_right).op g) •
          M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := by
      calc
        _ = X.presheaf.map (homOfLE inf_le_right).op g •
            M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t := hgW
        _ = _ := by rw [hfW, smul_smul, mul_comm]
    exact (hua _ hprod).trans (hua 1 (by simp)).symm

end AlgebraicGeometry.Scheme.Modules
