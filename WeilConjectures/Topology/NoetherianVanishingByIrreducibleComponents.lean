/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import WeilConjectures.Topology.FiniteClosedCoverCohomologyVanishing
import WeilConjectures.Topology.IrreducibleIntegerExtensionVanishing
import WeilConjectures.Topology.NoetherianExtensionByZeroReduction

/-!
# Grothendieck vanishing on Noetherian spaces via irreducible components

Grothendieck vanishing for Noetherian spaces in the irreducible case, and the induction step on
the number of irreducible components.

## Implementation details

The irreducible case inducts on the dimension bound and applies
`noetherian_extensionByZero_reduction`, whose last hypothesis is supplied by
`irreducible_integer_extension_vanishing`. The general case inducts on the number of irreducible
components, using the open-closed cohomology sequence for the complement `U` of a component and
the closure of `U`, which has fewer components. The irreducible statement repeats this
component argument at a fixed bound, since `noetherian_vanishing_of_irreducible_components`
quantifies its irreducible hypothesis over all dimension bounds.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Fixed-bound version of the finite irreducible closed-cover reduction. -/
private theorem vanishing_at_bound_of_irreducible
    (d q : ℕ)
    (hIrred : ∀ (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y]
      [IrreducibleSpace Y], topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
      ∀ G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u},
        IsZero (Sheaf.H' G q (⊤ : Opens Y)))
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  obtain ⟨S, hS, hcover⟩ := NoetherianSpace.exists_finset_irreducible (⊤ : Closeds X)
  apply cohomology_vanishing_of_finite_closed_cover X S hcover.symm q _ F
  intro Z hZ G
  have : IrreducibleSpace (Z : Set X) := Subtype.irreducibleSpace (hS ⟨Z, hZ⟩)
  exact hIrred (Z : Set X) ((topologicalKrullDim_subspace_le X _).trans hdim) G

/-- The irreducible case of Grothendieck vanishing for Noetherian spaces: on an irreducible
Noetherian space of dimension at most `d`, abelian-sheaf cohomology vanishes in degrees `q > d`. -/
theorem noetherian_vanishing_irreducible
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    [IrreducibleSpace X] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  have hall : ∀ (e : ℕ) (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y],
      topologicalKrullDim Y ≤ (e : WithBot ℕ∞) →
      ∀ (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (r : ℕ), e < r → IsZero (Sheaf.H' G r (⊤ : Opens Y)) := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro Y _ _ hdimY G r hr
      apply vanishing_at_bound_of_irreducible e r ?_ Y hdimY G
      intro Z _ _ _ hdimZ H
      apply noetherian_extensionByZero_reduction (TopCat.of Z) e ?_ ?_ ?_ H r hr
      · intro U hU z hz
        exact ⟨U, hU, NoetherianSpace.isCompact U, hz, Set.Subset.rfl⟩
      · intro U V _ _ _ _
        exact NoetherianSpace.isCompact (U ∩ V)
      · exact irreducible_integer_extension_vanishing (TopCat.of Z) e hdimZ ih
  exact hall d X hdim F q hq

-- Preserve the existing names of the unused binders inside `hIrred`.
set_option linter.unusedVariables false in
/-- The component induction step in Grothendieck vanishing for Noetherian spaces. -/
theorem noetherian_vanishing_of_irreducible_components
    (hIrred : ∀ (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y]
      [IrreducibleSpace Y] (d : ℕ)
      (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
      (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (q : ℕ) (hq : d < q),
      IsZero (Sheaf.H' F q (⊤ : Opens Y)))
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  apply vanishing_at_bound_of_irreducible d q ?_ X hdim F
  intro Y _ _ _ hdimY G
  exact hIrred Y d hdimY G q hq

end TopCat
