/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# A criterion for local injectivity of morphisms of presheaves of abelian groups

For a morphism of presheaves of abelian groups, local injectivity may be checked on sections
which are killed by the morphism.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- A morphism of presheaves of abelian groups is locally injective as soon as every section
which is killed by it vanishes locally. -/
lemma isLocallyInjective_of_forall_equalizerSieve_zero
    (h : ∀ (X : Cᵒᵖ) (x : F.obj X), φ.app X x = 0 →
      equalizerSieve x (0 : F.obj X) ∈ J X.unop) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y hxy := by
    refine J.superset_covering (fun V g hg ↦ ?_)
      (h X (x - y) (by rw [map_sub (φ.app X).hom, hxy, sub_self]))
    simpa [map_sub (F.map g.op).hom, sub_eq_zero] using hg

end CategoryTheory.Presheaf
