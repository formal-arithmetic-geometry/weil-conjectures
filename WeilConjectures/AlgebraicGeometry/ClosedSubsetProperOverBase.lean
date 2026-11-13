/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Closed subsets and module supports proper over a base

## Main definitions

* `Scheme.IsClosedSubsetProperOver`: properness of the reduced induced closed subscheme.
* `Scheme.Modules.HasSupportProperOver`: closedness and properness of the nonzero-stalk locus.

## References

* Stacks Project, Tags 0CYM, 0CYL, 0CYS and 01AT
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A closed subset is proper over the base if its reduced induced closed subscheme is proper.
The ideal `IdealSheafData.vanishingIdeal Z` consists of sections vanishing at every point of
`Z`; its subscheme is the reduced induced structure of Stacks Tags 01J3 and 01J4, as stated
in `IdealSheafData.reduced_induced_closed_subscheme`, including uniqueness over `X`
(Stacks, Tags 0CYM and 0CYL). -/
def IsClosedSubsetProperOver {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) : Prop :=
  IsProper ((IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)

namespace Modules

/-- The support of `F` is the set of points where its stalk is nonzero, written below as
failure of `Subsingleton` for the stalk (the project's inline support convention).
It has support proper over the base exactly
when this set is closed and is proper over the base with its reduced induced structure.
The existential closed subset expresses closedness without assuming it for arbitrary `F`
(Stacks, Tags 01AT and 0CYS). -/
def HasSupportProperOver {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) : Prop :=
  ∃ Z : TopologicalSpace.Closeds X,
    (Z : Set X) =
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
    IsClosedSubsetProperOver f Z

end Modules

end AlgebraicGeometry.Scheme
