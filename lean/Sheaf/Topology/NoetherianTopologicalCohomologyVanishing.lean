/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.KrullDimension
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Category.Grp.AB

/-!
# Noetherian topological cohomology vanishing

Source: literature/stacks-project/cohomology.tex, Proposition 02UZ
(cohomology-proposition-vanishing-Noetherian), statement (blueprint:
lem-sc-noetherian-topological-cohomology-vanishing)
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- For a Noetherian topological space, abelian-sheaf cohomology vanishes above a
nonnegative upper bound for the topological Krull dimension.
Source: literature/stacks-project/cohomology.tex, Proposition 02UZ
(cohomology-proposition-vanishing-Noetherian), statement
(blueprint: lem-sc-noetherian-topological-cohomology-vanishing)

Proof: induct on the dimension bound. Handle the empty space using the sheaf axiom,
then induct on the finite number of irreducible components using the open-closed
cohomology sequence. In the irreducible case, dimension zero reduces to constant
sheaves and their acyclicity. For positive dimension, verify the four hypotheses of
`lem-sc-noetherian-extension-by-zero-reduction`; for a quasi-compact open, use the
open-closed sequence for the constant sheaf and the closed complement's lower
 dimension. Apply that reduction and complete both inductions, using
`lem-sc-noetherian-finite-irreducible-components`.
-/
theorem isZero_noetherian_topological_cohomology_of_dimension_bound
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) : IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  sorry

end TopCat
