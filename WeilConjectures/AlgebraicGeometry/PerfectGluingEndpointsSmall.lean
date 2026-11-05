/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointProperties
import WeilConjectures.AlgebraicGeometry.PerfectRestrictionClassesSmall

/-! # Small endpoint families for perfect gluing

Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tags 08BV and 08DR
(blueprint: lem-perfect-gluing-endpoints-small).
-/

@[expose] public section

universe u w v z r

open CategoryTheory CategoryTheory.Limits

private theorem small_skeleton_of_family {C : Type v} [Category.{z} C]
    (P : ObjectProperty C) {I : Type r} [Small.{u} I] (F : I → C)
    (h : ∀ X : P.FullSubcategory, ∃ i : I, Nonempty (F i ≅ X.obj)) :
    Small.{u} (Skeleton P.FullSubcategory) := by
  classical
  let f : I → Skeleton C := fun i ↦ toSkeleton (F i)
  let g : Skeleton P.FullSubcategory → Set.range f := fun s ↦
    ⟨P.ι.mapSkeleton.obj s, by
      rw [← toSkeleton_fromSkeleton_obj s, Functor.mapSkeleton_obj_toSkeleton]
      obtain ⟨i, ⟨e⟩⟩ := h ((fromSkeleton P.FullSubcategory).obj s)
      exact ⟨i, congr_toSkeleton_of_iso e⟩⟩
  apply small_of_injective (f := g)
  intro s t hst
  exact P.ι.mapSkeleton_injective (congrArg Subtype.val hst)

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
