/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Colimits and geometric stalks

Source: Stacks Project, Tags 03PN and 04K1; blueprint node
`lem-kun-stalks-commute-colimits` (blueprint: lem-kun-stalks-commute-colimits).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-kun-stalks-commute-colimits) Let `T` be a scheme and `s` a geometric
point of `T`. The geometric stalk of sheaves of abelian groups on the small etale
site of `T` commutes with arbitrary colimits. In each degree the same holds for
complexes of abelian sheaves, whose colimits are computed termwise.

For a diagram of sheaves, first form the objectwise colimit of the underlying
presheaves and then sheafify. Sheafification leaves geometric stalks unchanged.
The resulting colimit over pointed etale neighborhoods commutes with the colimit
over the diagram, by their cocone universal properties. Apply this in each degree
to obtain the claim for complexes. -/
theorem geometricStalk_preservesColimits
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ T) :
    PreservesColimits
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} ℤ)) ∧
    PreservesColimits
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)) := by
  sorry

end AlgebraicGeometry.Scheme
