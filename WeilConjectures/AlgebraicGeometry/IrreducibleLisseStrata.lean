/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IrreducibleLisseRefinement

/-!
# Irreducible lisse strata
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constructible abelian etale sheaf on a Noetherian scheme admits a finite partition
into nonempty irreducible locally closed subschemes with finite locally constant restrictions.
Constructibility and finite local constancy refer to the finite geometric stalks of the
underlying sheaf of sets. -/
theorem exists_irreducible_lisse_stratification
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ S : Stratification X, ∀ i : Fin S.n,
      IrreducibleSpace (S.domain i) ∧
        IsFiniteLocallyConstantSheafOfTypes
          ((etaleSetPullback (S.immersion i)).obj
            ((sheafCompose X.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) := by
  rcases hF with ⟨S, hS⟩
  exact exists_irreducible_refinement X
    ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) S hS

end AlgebraicGeometry.Scheme
