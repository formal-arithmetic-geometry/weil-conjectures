/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Topology.NoetherianVanishingByIrreducibleComponents

/-!
# Noetherian topological cohomology vanishing

On a Noetherian topological space, abelian-sheaf cohomology vanishes above the topological Krull
dimension (Grothendieck vanishing).

## Implementation details

The proof inducts on the dimension bound and on the number of irreducible components, using the
open-closed cohomology sequence; the irreducible case reduces to extensions by zero of constant
sheaves via `noetherian_extensionByZero_reduction`.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- For a Noetherian topological space, abelian-sheaf cohomology vanishes above a
nonnegative upper bound for the topological Krull dimension. -/
theorem isZero_noetherian_topological_cohomology_of_dimension_bound
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) : IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  exact noetherian_vanishing_of_irreducible_components
    (fun Y _ _ _ d hdim F q hq =>
      noetherian_vanishing_irreducible Y d hdim F q hq)
    X d hdim F q hq

end TopCat
