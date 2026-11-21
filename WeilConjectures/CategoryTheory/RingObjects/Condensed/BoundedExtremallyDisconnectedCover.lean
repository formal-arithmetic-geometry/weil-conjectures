/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.SetTheory.Cardinal.Basic

import Mathlib.Topology.Category.Stonean.Basic

/-!
# Bounded extremally disconnected covers of profinite spaces

Source: Stacks Project, Topology, Tags 090D and 090E.
-/

@[expose] public section

universe u

namespace Profinite

/-- Every profinite space admits an extremally disconnected profinite cover with the stated
cardinal bound. Source: Stacks Project, Topology, Tags 090D and 090E. -/
theorem exists_bounded_extremallyDisconnected_cover (X : Profinite.{u}) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X ≤ κ) :
    ∃ (T : Profinite.{u}) (u : ContinuousMap T X),
      Function.Surjective u ∧ ExtremallyDisconnected T ∧
        Cardinal.mk T ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
  classical
  -- The construction also works for finite bounds; retain the stated hypothesis.
  have _ := hκ
  let P := X.presentation
  let f : ContinuousMap (Stonean.toProfinite.obj P) X :=
    CategoryTheory.ConcreteCategory.hom (Profinite.presentation.π X)
  refine ⟨Stonean.toProfinite.obj P, f, ?_, ?_, ?_⟩
  · have h : CategoryTheory.Epi (Profinite.presentation.π X) := inferInstance
    rw [Profinite.epi_iff_surjective] at h
    exact h
  · exact P.prop
  · change Cardinal.mk (Ultrafilter X) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)
    let g : Ultrafilter X → Set (Set X) := fun F ↦ (F : Filter (X : Type u)).sets
    have hg : Function.Injective g := by
      intro F G hFG
      apply Ultrafilter.ext
      intro A
      simpa [g] using Set.ext_iff.mp hFG A
    calc
      Cardinal.mk (Ultrafilter X) ≤ Cardinal.mk (Set (Set X)) :=
        Cardinal.mk_le_of_injective hg
      _ = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.mk X) := by
        rw [Cardinal.mk_set, Cardinal.mk_set]
      _ ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
        apply Cardinal.power_le_power_left two_ne_zero
        apply Cardinal.power_le_power_left two_ne_zero
        exact hX

end Profinite
