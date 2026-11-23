/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Evaluations detect isomorphisms in derived categories of diagrams

A morphism in the derived category of `J`-shaped diagrams in an abelian category is an
isomorphism as soon as all its evaluations are
(`DerivedCategory.isIso_of_isIso_evaluation`): the homology of a complex of diagrams is computed
pointwise.
-/

@[expose] public section

open CategoryTheory

namespace DerivedCategory

variable {J C : Type*} [Category J] [Category C] [Abelian C] [HasDerivedCategory C]
  [HasDerivedCategory (J ⥤ C)]

/-- A morphism of derived categories of diagrams is an isomorphism if all its evaluations are. -/
theorem isIso_of_isIso_evaluation {M N : DerivedCategory (J ⥤ C)} (f : M ⟶ N)
    (hf : ∀ j : J, IsIso (((evaluation J C).obj j).mapDerivedCategory.map f)) : IsIso f := by
  rw [isIso_iff]
  intro q
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  have := hf j
  exact (NatIso.isIso_map_iff
    (((evaluation J C).obj j).mapDerivedCategoryHomologyFunctorIso q) f).2 (by
      change IsIso ((homologyFunctor C q).map (((evaluation J C).obj j).mapDerivedCategory.map f))
      infer_instance)

end DerivedCategory
