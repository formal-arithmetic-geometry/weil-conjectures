/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Local finite presentation of the diagonal of a locally finite type algebraic-space map

Source: Stacks Project, Morphisms of Spaces, Tag 084P
(lemma-diagonal-morphism-finite-type), first assertion
(blueprint: lem-sfb-space-lft-diagonal-lfp).

The target of the canonical sheaf diagonal is bundled as an algebraic space using the
existing fibre-product closure theorem. Both local properties use the shared chart test.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative diagonal of a locally finite type morphism of algebraic spaces is locally
of finite presentation, without quasi-compactness, quasi-separatedness or separation.
Source: Stacks Project, Tag 084P, first assertion
(blueprint: lem-sfb-space-lft-diagonal-lfp).

Proof: (1) Choose a surjective etale scheme atlas V of Y, and an atlas U of X times_Y V.
The composite U to X is surjective etale by
[lem-trf-space-representable-etale-scheme-tests], using
[def-trf-algebraic-space] and [lem-trf-space-fibre-products-etale-covers]. The map
h : U to V is locally of finite type by [lem-sfb-space-local-properties-chart-test].
(2) Write P = X times_Y X. A compatible source atlas for the second projection P to X
over U is R = U times_V U: it covers P times_X U = X times_Y U. Its map to U is the
second projection, locally of finite type by [lem-weil-pbc-lft-base-change]. The chart
criterion therefore makes P to X locally of finite type.
(3) The identity of X is locally of finite presentation by the identity chart on U:
on an affine open its ring map has zero generators and zero relations, as in
[def-sbc-locally-finite-presentation]. Apply [lem-sfb-space-local-properties-chart-test].
(4) The diagonal followed by the second projection is the identity. Apply
[lem-sfb-space-relative-lfp-permanence] to these two maps: their composite is locally
of finite presentation by (3), and the second map is locally of finite type by (2).
No step needs a quasi-compactness, quasi-separatedness, separatedness or Noetherian
hypothesis. -/
theorem diagonal_locallyOfFinitePresentation_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsLocally (@LocallyOfFiniteType) f) :
    MapIsLocallyOfFinitePresentation
      (Y := ⟨Limits.pullback f.hom f.hom, (fibreProduct_isAlgebraicSpace X X Y f f).1⟩)
      (ObjectProperty.homMk (Limits.pullback.diagonal f.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
