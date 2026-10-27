/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Relative local finite presentation for morphisms of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 05WT
(blueprint: lem-sfb-space-relative-lfp-permanence).

Local finite presentation of a composite and local finite type of its second factor imply
local finite presentation of its first factor, with both properties tested on étale charts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Cancellation of local finite presentation for algebraic-space morphisms over a scheme.
Source: Stacks Project, Morphisms of Spaces, Tag 05WT
(blueprint: lem-sfb-space-relative-lfp-permanence).

Proof:
1. Choose a surjective étale scheme atlas W → Z, then V → Y ×_Z W, then
   U → X ×_Y V. Fibre products are algebraic spaces by
   [lem-trf-space-fibre-products-etale-covers], and atlases exist by
   [def-trf-algebraic-space]. Base change and composition preserve representable
   surjective étale maps by [lem-trf-space-representable-etale-scheme-tests].
   Thus a : U → X, b : V → Y and w : W → Z are surjective étale, and the scheme
   projections h : U → V and q : V → W satisfy a ≫ f = h ≫ b and b ≫ g = q ≫ w.
   These give compatible presentation diagrams for f, g and f ≫ g.
2. Local finite type and local finite presentation are étale local on source-and-target
   by [lem-sfb-scheme-etale-source-target-properties]. The universal chart condition in
   [lem-sfb-space-etale-presentation-property-criterion] gives local finite type of q
   and local finite presentation of h ≫ q. Apply
   [lem-a1-map-over-base-finite-presentation] over W to conclude that h is locally of
   finite presentation; its recorded declaration is locallyOfFinitePresentation_of_comp.
3. The presentation for f has surjective source chart a. The converse direction of
   [lem-sfb-space-etale-presentation-property-criterion] therefore gives local finite
   presentation of f. No quasi-compactness or separation is used in these steps.
-/
theorem mapIsLocallyOfFinitePresentation_of_comp {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : MapIsLocallyOfFinitePresentation (f ≫ g))
    (hg : MapIsLocally (@LocallyOfFiniteType) g) :
    MapIsLocallyOfFinitePresentation f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
