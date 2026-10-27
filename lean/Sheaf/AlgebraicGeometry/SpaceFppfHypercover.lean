/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.CategoryTheory.SiteHypercoverDisjointUnion

/-! # Fppf hypercovers of algebraic spaces

Source: Stacks Project, Simplicial Spaces, section Fppf hypercoverings
(blueprint: def-sfb-space-fppf-hypercover).

The matching predicate is the published proper-face boundary predicate in the slice.
Degree zero has empty boundary and matching object the augmentation target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fppf for a space map means flat and locally finitely presented on étale charts,
and surjective on point classes. It does not require representability by schemes.
Source: Stacks, Topologies on Spaces, fppf topology
(blueprint: def-sfb-space-fppf-hypercover). -/
def SpaceMapIsFppf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  MapIsFlat f ∧ MapIsLocallyOfFinitePresentation f ∧
    IsJointlySurjective (fun _ : Unit ↦ f.hom.hom)

/-- All proper-face matching arrows are flat, locally finitely presented and surjective.
The limits are taken in the slice, so the degree-zero matching object is the base.
Source: Stacks, Simplicial Spaces, section Fppf hypercoverings
(blueprint: def-sfb-space-fppf-hypercover). -/
def IsSpaceFppfHypercover {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : SimplicialObject (Over X)) : Prop :=
  ∀ n : ℕ, ∃ (M : Over X)
      (μ : U.obj (op (SimplexCategory.mk n)) ⟶ M),
    SimplicialObject.IsProperFaceMatchingArrow U n M μ ∧ SpaceMapIsFppf μ.left

end AlgebraicGeometry.AlgebraicSpace
