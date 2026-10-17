/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# The structural morphism of the strict henselization

The strict henselization `S_(s)` of a scheme `S` at a geometric point `s` maps to `S` through
every affine pointed étale neighbourhood; this module names that canonical morphism.

Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The representative limit legs factor through upstream's structure morphism. -/
theorem strictHenselizationStructuralMap_eq
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
        Spec.map (ΓSpecIso
          (((equivSmallModel.{u}
            (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
        ((AffineEtale.Spec S).obj
          (((equivSmallModel.{u}
            (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
      strictHenselizationStructuralMap s := by
  exact (exists_strictHenselizationStructuralMap s).choose_spec j

end AlgebraicGeometry.Scheme
