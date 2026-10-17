/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recognising filtered colimits of modules

A cocone over a filtered diagram of modules is a colimit as soon as it is jointly surjective
and every element of a term of the diagram which is sent to zero in the cocone point is
already killed by a transition map (`ModuleCat.isColimitOfSurjectiveOfEqZero`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace ModuleCat

variable {Λ : Type u} [Ring Λ] {J : Type v} [Category.{v} J] [IsFiltered J]
  [PreservesColimitsOfShape J (forget (ModuleCat.{u} Λ))]
  {K : J ⥤ ModuleCat.{u} Λ} (t : Cocone K)

/-- A cocone over a filtered diagram of modules is a colimit if it is jointly surjective and
every element of `K j` sent to zero in the cocone point is killed by a transition map. -/
noncomputable def isColimitOfSurjectiveOfEqZero
    (hsurj : ∀ y : t.pt, ∃ (j : J) (z : K.obj j), t.ι.app j z = y)
    (hzero : ∀ (j : J) (z : K.obj j), t.ι.app j z = 0 → ∃ (k : J) (f : j ⟶ k), K.map f z = 0) :
    IsColimit t := by
  refine isColimitOfReflects (forget (ModuleCat.{u} Λ))
    (Types.FilteredColimit.isColimitOf' _ _ (fun y ↦ ?_) (fun j y₁ y₂ h ↦ ?_))
  · obtain ⟨j, z, rfl⟩ := hsurj y
    exact ⟨j, z, rfl⟩
  · obtain ⟨k, f, hf⟩ := hzero j (y₁ - y₂) (by
      rw [map_sub]
      exact sub_eq_zero.2 h)
    exact ⟨k, f, sub_eq_zero.1 (by simpa using hf)⟩

end ModuleCat
