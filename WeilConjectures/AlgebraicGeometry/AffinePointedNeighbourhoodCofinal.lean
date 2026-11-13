/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofinality of affine pointed étale neighbourhoods

## References

* Stacks Project, Tags 04HX and 0BUC
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The full subcategory of affine pointed étale neighbourhoods of a geometric point is
initial; its opposite inclusion is final, so computes the same opposite-indexed stalk colimit.
(Stacks, Tags 04HX, 0BUC and 04E7). -/
theorem affinePointedNeighbourhoods_initial_and_final_op
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Functor.Initial
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)) ∧
    Functor.Final
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).op := by
  have h : Functor.Initial
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)) := by
    apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    intro n
    induction n with | @mk X x
    cases X with | _ Y f
    obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
    dsimp at y hy
    obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
        (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
      obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
        (x := y.base default) (U := ⊤) (by simp)
      refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    refine ⟨⟨Functor.elementsMk _ (Etale.mk (j ≫ f))
      (Over.homMk y'), by change IsAffine (Spec (.of R)); infer_instance⟩, ?_⟩
    exact ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩
  exact ⟨h, inferInstance⟩

end AlgebraicGeometry.Scheme
