/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Category.Grp.AB

/-!
# The Zariski dimension bound

Source: the Weil conjectures blueprint, `sec-smooth-purity`, unit `sk-prop-sf-cbc`,
lemma `lem-sc-zariski-dimension-bound` (blueprint: lem-sc-zariski-dimension-bound);
Stacks Project, Cohomology, Proposition 02UZ.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The Zariski cohomology of every abelian sheaf on a Noetherian scheme vanishes above
any nonnegative upper bound for its topological Krull dimension.
Source: Stacks Project, Cohomology, Proposition 02UZ and the blueprint lemma of the same name
(blueprint: lem-sc-zariski-dimension-bound).

Proof: forget the scheme structure. The underlying space is Noetherian by
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, and its dimension is at most `d`
by hypothesis (`def-kun-topological-krull-dimension`). The small Zariski site is the site
of open subsets with jointly surjective open coverings (`def-sc-zariski-site`). Thus `F`
is an abelian sheaf on that space, and its topological cohomology
(`def-sc-topological-abelian-cohomology`) is precisely its Zariski cohomology
(`def-sc-zariski-cohomology`). Apply
`lem-sc-noetherian-topological-cohomology-vanishing` to obtain vanishing for every `q > d`.
-/
theorem isZero_zariskiCohomology_of_dimension_bound
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) : IsZero (Sheaf.H' F q (⊤ : X.Opens)) := by
  sorry

end AlgebraicGeometry
