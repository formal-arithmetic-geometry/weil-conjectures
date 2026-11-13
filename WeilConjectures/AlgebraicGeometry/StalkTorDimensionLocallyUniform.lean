/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.AffineSectionsFiniteTorOfStalkwise
import WeilConjectures.AlgebraicGeometry.AffineSectionsTorBoundStalk

/-! # Uniform stalk Tor bounds near a point

## References

* [Stacks Project, Tag 069C](https://stacks.math.columbia.edu/tag/069C)
* [Stacks Project, Tag 09U9](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Stalkwise finite Tor dimension becomes uniformly bounded on a neighbourhood. -/
theorem stalkTorDimension_locally_uniform
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ d : ℕ,
      ∀ y : X, y ∈ U → ∀ M : ModuleCat.{u} (Y.presheaf.stalk (f y)),
        ∀ j : ℕ, d < j →
          IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f y))) j).obj
            ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
              (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj M) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) (by trivial)
  obtain ⟨V, hV, hxV, e⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ U) hxU
  obtain ⟨d, hd⟩ := affineSections_finiteTorDimension_of_stalkwise f hperfect U hU V hV e
  refine ⟨V, hxV, d, ?_⟩
  exact affineSections_torBound_stalk f U hU V hV e d hd

end AlgebraicGeometry
