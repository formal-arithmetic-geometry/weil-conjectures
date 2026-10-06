/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Points of fppf coverings

A covering sieve of the fppf topology is jointly surjective, through flat morphisms locally of
finite presentation: every point of the base lies in the image of such a morphism of the sieve.
We record this for the fppf topology on `Scheme` and for its localization to `Over S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A covering sieve of the fppf topology on a scheme `X` is jointly surjective through flat
morphisms locally of finite presentation: every point of `X` is in the image of some flat
morphism locally of finite presentation `g : Y ⟶ X` of the sieve. -/
lemma exists_flat_mem_of_mem_fppfTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ fppfTopology X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g.base := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)), inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : fppfPrecoverage.{u}.HasIsos := by unfold fppfPrecoverage; infer_instance
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨hR₁, hR₂⟩, hle⟩ := hS
  obtain ⟨_, _, h, hx⟩ := hR₁ x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, (hR₂ hg).1, (hR₂ hg).2, hx⟩

/-- A covering sieve of the fppf topology on `Over S` is jointly surjective through morphisms
whose underlying morphism of schemes is flat and locally of finite presentation. -/
lemma exists_flat_mem_of_mem_fppfTopology_over {S : Scheme.{u}} {T : Over S} {R : Sieve T}
    (hR : R ∈ fppfTopology.over S T) (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T), R g ∧ Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      t ∈ Set.range g.left.base := by
  obtain ⟨Y, g, ⟨Z, h, k, hh, rfl⟩, hg₁, hg₂, hx⟩ :=
    exists_flat_mem_of_mem_fppfTopology ((GrothendieckTopology.mem_over_iff _ _).1 hR) t
  refine ⟨Over.mk (k ≫ Z.hom), Over.homMk k ≫ h, R.downward_closed hh _, ?_, ?_, ?_⟩
  all_goals simpa using ‹_›

end AlgebraicGeometry.Scheme
