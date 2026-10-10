/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms out of K-projective complexes in the derived category

A morphism `Q(K) ⟶ Q(L)` in the derived category out of a K-projective complex `K` is the
image of a morphism of complexes (`CochainComplex.IsKProjective.exists_Q_map_eq`).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A morphism `Q(K) ⟶ Q(L)` in the derived category out of a K-projective complex `K` is
the image of a morphism of complexes. -/
lemma IsKProjective.exists_Q_map_eq (K L : CochainComplex C ℤ) [K.IsKProjective]
    (g : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : K ⟶ L, DerivedCategory.Q.map φ = g := by
  obtain ⟨g', hg'⟩ := (IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).2
      ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ g ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g'
  refine ⟨φ, ?_⟩
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality φ
  dsimp at h hg'
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K), ← h, hg']
  simp

end CochainComplex
