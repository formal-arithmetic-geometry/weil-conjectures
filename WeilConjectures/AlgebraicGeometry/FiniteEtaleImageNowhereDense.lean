/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.NoetherianSpace

/-! # Images of nowhere dense closed sets under finite morphisms

Let `f : X ⟶ Y` be a finite morphism of schemes with `X` a noetherian topological space.
We show that the image under `f` of a closed subset `B ⊆ X` with empty interior is again a
closed subset with empty interior. In particular this applies to finite étale morphisms.

The argument: a locally quasi-finite morphism has discrete fibres, so a point of `X` lying over
the generic point of an irreducible component of `Y` is itself the generic point of an
irreducible component of `X`. In a noetherian space every irreducible component has nonempty
interior, so such a point cannot lie in a closed set with empty interior.

## Main results

* `AlgebraicGeometry.closure_singleton_mem_irreducibleComponents_of_locallyQuasiFinite`:
  for `f` locally quasi-finite, if `f x` is a maximal point of `Y` then `x` is a maximal point
  of `X`.
* `AlgebraicGeometry.interior_image_eq_empty_of_locallyQuasiFinite`
* `AlgebraicGeometry.isClosed_image_and_interior_image_eq_empty_of_isFinite`
* `AlgebraicGeometry.dense_compl_image_of_isFinite`
-/

@[expose] public section

universe u

open Topology

/-- In a `T₀` space, a point whose closure is an irreducible component admits no proper
generization. -/
theorem eq_of_specializes_of_closure_mem_irreducibleComponents {α : Type*}
    [TopologicalSpace α] [T0Space α] {x y : α}
    (hy : closure {y} ∈ irreducibleComponents α) (hxy : x ⤳ y) : x = y := by
  have h := hy.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp hxy)
  exact (hxy.antisymm (specializes_iff_closure_subset.mpr h)).eq

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a locally quasi-finite morphism `f`, a point lying over the generic point of an
irreducible component of `Y` is the generic point of an irreducible component of `X`. -/
theorem closure_singleton_mem_irreducibleComponents_of_locallyQuasiFinite
    [LocallyQuasiFinite f] {x : X} (hx : closure {f x} ∈ irreducibleComponents Y) :
    closure {x} ∈ irreducibleComponents X := by
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
    isClosed_irreducibleComponent
  have hξx : ξ ⤳ x := hξ.specializes mem_irreducibleComponent
  have hfξ : f ξ = f x :=
    eq_of_specializes_of_closure_mem_irreducibleComponents hx (hξx.map f.continuous)
  rw [← (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hξx hfξ rfl, hξ.def]
  exact irreducibleComponent_mem_irreducibleComponents x

/-- For a locally quasi-finite morphism `f` with noetherian source, the image of a closed set
with empty interior has empty interior. -/
theorem interior_image_eq_empty_of_locallyQuasiFinite [LocallyQuasiFinite f]
    [TopologicalSpace.NoetherianSpace X] {B : Set X} (hB : IsClosed B)
    (hB' : interior B = ∅) : interior (f '' B) = ∅ := by
  by_contra h
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    isClosed_irreducibleComponent
  obtain ⟨b, hb, hbη⟩ := interior_subset
    ((hη.specializes mem_irreducibleComponent).mem_open isOpen_interior hy)
  have hfb : closure {f b} ∈ irreducibleComponents Y := by
    rw [hbη, hη.def]
    exact irreducibleComponent_mem_irreducibleComponents y
  obtain ⟨o, ho, hne, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
      (closure_singleton_mem_irreducibleComponents_of_locallyQuasiFinite f hfb)
  have hoB : o ⊆ interior B := ho.subset_interior_iff.mpr
    (hoZ.trans (hB.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hb)))
  rw [hB'] at hoB
  exact hne.ne_empty (Set.subset_empty_iff.mp hoB)

/-- For a finite morphism `f` with noetherian source, the image of a closed set with empty
interior is closed with empty interior. -/
theorem isClosed_image_and_interior_image_eq_empty_of_isFinite [IsFinite f]
    [TopologicalSpace.NoetherianSpace X] {B : Set X} (hB : IsClosed B)
    (hB' : interior B = ∅) : IsClosed (f '' B) ∧ interior (f '' B) = ∅ :=
  ⟨f.isClosedMap B hB, interior_image_eq_empty_of_locallyQuasiFinite f hB hB'⟩

/-- For a finite morphism `f` with noetherian source and a closed set `B ⊆ X` with empty
interior, the complement of `f '' B` is a dense open subset of `Y`. -/
theorem dense_compl_image_of_isFinite [IsFinite f]
    [TopologicalSpace.NoetherianSpace X] {B : Set X} (hB : IsClosed B)
    (hB' : interior B = ∅) : IsOpen (f '' B)ᶜ ∧ Dense (f '' B)ᶜ :=
  ⟨(f.isClosedMap B hB).isOpen_compl, interior_eq_empty_iff_dense_compl.mp
    (interior_image_eq_empty_of_locallyQuasiFinite f hB hB')⟩

/-- The preimage of the complement of `f '' B` does not meet `B`. -/
theorem preimage_compl_image_inter_eq_empty {B : Set X} :
    f ⁻¹' (f '' B)ᶜ ∩ B = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦ hx.1 (Set.mem_image_of_mem f hx.2)

end AlgebraicGeometry
