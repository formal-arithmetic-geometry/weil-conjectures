/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Antisymmetrization

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The initial upper-tail chart projection is an isomorphism (Stacks, Tag 01ZR). -/
theorem affine_chart_section_ring_presentations_iso
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (j : I) {A : Scheme.{u}}
    (g : A ⟶ Spec (R.obj j)) :
    IsIso (pullback.snd (Spec.map (R.map (homOfLE
      ((OrderEmbedding.ofAntisymmetrization (α := {k : I // j ≤ k})).monotone.functor.obj
        (toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k}))).property))) g) := by
  let k := (OrderEmbedding.ofAntisymmetrization (α := {k : I // j ≤ k})).monotone.functor.obj
    (toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k}))
  have hk : AntisymmRel (· ≤ ·) k (⟨j, le_rfl⟩ : {k : I // j ≤ k}) :=
    Quotient.exact (toAntisymmetrization_ofAntisymmetrization (· ≤ ·)
      (toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})))
  have : IsIso (homOfLE k.property) :=
    ⟨⟨homOfLE (show k.val ≤ j from hk.1), by
      constructor <;> apply Subsingleton.elim⟩⟩
  have : IsIso (R.map (homOfLE k.property)) := inferInstance
  have : IsIso (Spec.map (R.map (homOfLE k.property))) := inferInstance
  infer_instance
end AlgebraicGeometry
