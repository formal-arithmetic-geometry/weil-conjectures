/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Finite closed subsets of Jacobson spaces

In a Jacobson space every point of a finite closed subset is closed: the closure of such a
point is a finite closed set, and the closed points are dense in it.

In a noetherian Jacobson space whose closed points are permuted transitively by homeomorphisms
(such as an algebraic group over an algebraically closed field, acting on itself by translations),
distinct irreducible components are disjoint
(`disjoint_of_mem_irreducibleComponents_of_forall_closedPoints`).
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

open TopologicalSpace in
/-- In a noetherian Jacobson space whose closed points are permuted transitively by
homeomorphisms, distinct irreducible components are disjoint: some closed point lies in a single
irreducible component, hence so does every closed point, and two components meeting would meet in
a closed point. -/
theorem disjoint_of_mem_irreducibleComponents_of_forall_closedPoints [NoetherianSpace X]
    [JacobsonSpace X] (h : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ φ : X ≃ₜ X, φ x = y)
    {Z₁ Z₂ : Set X} (hZ₁ : Z₁ ∈ irreducibleComponents X) (hZ₂ : Z₂ ∈ irreducibleComponents X)
    (hne : Z₁ ≠ Z₂) : Disjoint Z₁ Z₂ := by
  refine Set.disjoint_left.2 fun z hz₁ hz₂ ↦ ?_
  obtain ⟨q, ⟨hq₁, hq₂⟩, hq⟩ := nonempty_inter_closedPoints (Z := Z₁ ∩ Z₂) ⟨z, hz₁, hz₂⟩
    ((isClosed_of_mem_irreducibleComponents _ hZ₁).inter
      (isClosed_of_mem_irreducibleComponents _ hZ₂)).isLocallyClosed
  have : Nonempty X := ⟨z⟩
  obtain ⟨U, hU, hUne, hUuniq⟩ := NoetherianSpace.exists_isOpen_nonempty_forall_eq (α := X)
  obtain ⟨p, hpU, hp⟩ := nonempty_inter_closedPoints hUne hU.isLocallyClosed
  obtain ⟨φ, hφ⟩ := h q hq p hp
  exact hne (φ.injective.image_injective (hUuniq p hpU _ (φ.image_mem_irreducibleComponents hZ₁)
    _ (φ.image_mem_irreducibleComponents hZ₂) ⟨q, hq₁, hφ⟩ ⟨q, hq₂, hφ⟩))

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.Topology.JacobsonSpace`) -/

variable {X : Type*} [TopologicalSpace X]

-- before `closedPoints_eq_univ`
theorem closedPoints.isClosed_singleton (x : closedPoints X) :
    IsClosed ({x} : Set (closedPoints X)) := by
  simpa [Set.preimage, Subtype.val_inj] using
      x.2.preimage (f := fun (x : closedPoints X) ↦ (x : X)) continuous_subtype_val
