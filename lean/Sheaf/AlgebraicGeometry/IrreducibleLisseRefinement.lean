/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-! Refinement of a finite lisse stratification by irreducible strata. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite lisse stratification can be refined so that every stratum is irreducible.
This is the topological and scheme theoretic refinement step in the proof of
`exists_irreducible_lisse_stratification`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1602
(blueprint: lem-weil-pbc-irreducible-refinement).

Proof: refine each Noetherian lisse stratum by its finitely many irreducible
components, removing earlier components and pulling back the sheaf; the resulting
open pieces are nonempty irreducible locally closed subschemes and preserve finite
local constancy under pullback. -/
theorem exists_irreducible_refinement
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (S : Stratification X)
    (hS : ∀ i : Fin S.n,
      IsFiniteLocallyConstantEtaleSheafOfSets
        ((etaleSetPullback (S.immersion i)).obj F)) :
    ∃ T : Stratification X, ∀ i : Fin T.n,
      IrreducibleSpace (T.domain i) ∧
        IsFiniteLocallyConstantEtaleSheafOfSets
          ((etaleSetPullback (T.immersion i)).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
