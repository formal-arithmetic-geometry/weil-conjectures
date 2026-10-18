/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper hypercovers of schemes

Source: Orgogozo, Modifications et cycles proches sur une base générale, Proposition 3.3.1;
Stacks Project, proper hypercovering spaces, Tag 0DHL, and simplicial matching objects,
Tag 0186 (blueprint: def-trf-proper-hypercover).

An augmented simplicial scheme over `Z` is a simplicial object of `Over Z`. Matching
limits are characterized in that slice category, including the empty boundary in degree zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical cone of the proper-face operators out of degree `n`.
This uses the existing proper-face diagram and the canonical slice cocone.
Source: Stacks Project, Tag 0186 (blueprint: def-trf-proper-hypercover). -/
def properHypercoverBoundaryCone {Z : Scheme.{u}}
    (Y : SimplicialObject (Over Z)) (n : ℕ) : Cone (Y.properFaceDiagram n) :=
  Y.mapCone (((Over.forgetCocone (SimplexCategory.mk n)).whisker
    (SimplicialObject.properFaceProperty n).ι).op)

/-- An augmented simplicial scheme is a proper hypercover when every canonical matching
arrow is proper and surjective. Matching objects are specified by their universal property,
so the predicate is independent of any choice of limits. In degree zero the boundary is
empty and its limit in `Over Z` is the identity of `Z`; the matching condition is exactly
proper surjectivity of the augmentation. In positive degree this is the usual simplicial
matching object (the proper-face and all-lower-simplex diagrams give the same limit).
Source: Orgogozo, Proposition 3.3.1; Stacks Project, Tag 0DHL, matching convention, and
Tag 0186 (blueprint: def-trf-proper-hypercover). -/
def IsProperHypercover {Z : Scheme.{u}} (Y : SimplicialObject (Over Z)) : Prop :=
  ∀ n : ℕ, ∃ (c : Cone (Y.properFaceDiagram n)) (hc : IsLimit c),
    IsProper (hc.lift (properHypercoverBoundaryCone Y n)).left ∧
      Surjective (hc.lift (properHypercoverBoundaryCone Y n)).left

end AlgebraicGeometry
