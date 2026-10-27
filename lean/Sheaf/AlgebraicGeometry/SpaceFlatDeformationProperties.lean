/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeThickening
import Sheaf.RingTheory.RelativeFlatAlgebraFpLift
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-! # Morphism properties under flat deformation of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0CG6,
parts (3), (5), (7), (14), (21)
(blueprint: lem-sfb-space-flat-deformation-properties).

The reduction map is the canonical map between actual sheaf fibre products.
Finite presentation includes quasi-compactness of the relative diagonal.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The reduction of a morphism over `B'` along `B → B'`. Both its components are
specified by the fibre-product construction: identity on `B` and the given map on
its other factor.
Source: Stacks Project, Tag 0CG6, diagram of base-changed morphisms
(blueprint: lem-sfb-space-flat-deformation-properties). -/
def flatDeformationMap {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (i : B ⟶ B') {P' Q' : Over B'} (h' : P' ⟶ Q') :
    enlargedFibreProduct i P'.hom ⟶ enlargedFibreProduct i Q'.hom :=
  ObjectProperty.homMk
    (pullback.map i.hom P'.hom.hom i.hom Q'.hom.hom
      (𝟙 B.obj) h'.left.hom (𝟙 B'.obj) (by simp)
      (by simpa only [Category.comp_id, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun f : P'.left ⟶ B' ↦ f.hom) (Over.w h').symm))

/-- Isomorphisms, properness and finite presentation lift and descend through a
first-order base thickening when the source is flat over the thickened base.
Only the source structure morphism is assumed flat.

Source: Stacks Project, Tag 0CG6, parts (3), (5), (7), (14), (21)
(blueprint: lem-sfb-space-flat-deformation-properties).

Proof:
1. Choose surjective etale scheme charts U' of B', V' of Q' times_{B'} U',
   and W' of P' times_{Q'} V'. Their pullbacks give U, V, W over B. By the
   fibre-product and representable-etale scheme tests, W' is a source atlas and
   W' → U' is flat. The chart test detects local finite type and local finite
   presentation on W' → V'. On affine refinements the coordinate maps are
   R' → A' → C', with square-zero I in R', reductions R, A, C, and C' flat over R'.
   Use lem-trf-space-fibre-products-etale-covers,
   lem-trf-space-representable-etale-scheme-tests, lem-sfb-space-flat-proper-fp-locality,
   lem-sfb-space-local-properties-chart-test,
   lem-weil-pbc-quotient-base-change-closed-immersion-ideal and
   lem-weil-pbc-flat-morphism-affine-criterion.
2. Base change makes P → P' and Q → Q' thickenings. The fibre-product universal
   property identifies P with Q times_{Q'} P'. Hence the thickening topological
   properties equate quasi-compactness, quasi-separatedness, separation and universal
   closedness for h and h'. The extended ideals still have square zero, without
   assuming Q' flat. Use lem-sfb-space-thickening-base-change and
   lem-sfb-space-thickening-topological-properties.
3. Apply lem-weil-pbc-thickening-lft-cartesian to W → W' over V → V'. Its local
   finite-type equivalence passes to h and h' by the chart test from step 1.
4. Apply lem-sfb-relative-flat-algebra-fp-lift to R' → A' → C' and I on every
   affine refinement: finite presentation of A' → C' is equivalent to that of
   A → C. Use lem-weil-pbc-lfp-affine-opens-finite-presentation and the chart
   test to obtain the local finite-presentation equivalence for h and h'. No
   flatness of A' over R' is needed.
5. Combine step 2 with step 3 to equate all four constituents of properness.
   Combine step 2 with step 4 to equate local finite presentation,
   quasi-compactness and quasi-separatedness, giving finite presentation.
6. If h is an isomorphism, W → V is etale, hence flat and locally finitely
   presented, by lem-trf-space-representable-etale-scheme-tests and
   def-weil-etale-morphism. Step 4 gives local finite presentation of W' → V'.
   On the affine refinements C is A-flat and C' is R'-flat. Apply
   lem-sfb-nilpotent-fibre-flat-module to deduce C' is A'-flat, then apply
   lem-weil-pbc-flat-morphism-affine-criterion to W' → V'.
7. The square-zero ideal vanishes in every residue field of V', so every such
   field factors through V. The corresponding fibre of W' → V' is the base
   change of the etale W → V. By lem-weil-pbc-etale-base-change-finite-limits
   and lem-sbc-flat-fibre-etale-neighbourhoods every source point has an etale
   neighbourhood. By lem-sfb-scheme-etale-source-target-properties W' → V' is etale.
8. Compose with V' → Q' and use lem-trf-space-etale-source-atlas-detection
   to make h' chartwise etale. Its pullback by Q → Q' is h, so
   lem-sfb-space-etale-thickening-detects-iso implies h' is an isomorphism.
   Conversely an inverse of h' pulls back to an inverse of h; the inverse
   equations persist by the fibre-product universal property. -/
theorem flat_deformation_properties {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (i : B ⟶ B') (hi : IsSpaceFirstOrderThickening i)
    {P' Q' : Over B'} (h' : P' ⟶ Q') (hflat : MapIsFlat P'.hom) :
    (IsIso h'.left ↔ IsIso (flatDeformationMap i h')) ∧
      (MapIsProper h'.left ↔ MapIsProper (flatDeformationMap i h')) ∧
      ((MapIsLocallyOfFinitePresentation h'.left ∧
          MapIsQuasiCompact h'.left.hom.hom ∧
          MapIsQuasiCompact (pullback.diagonal h'.left.hom.hom)) ↔
        (MapIsLocallyOfFinitePresentation (flatDeformationMap i h') ∧
          MapIsQuasiCompact (flatDeformationMap i h').hom.hom ∧
          MapIsQuasiCompact (pullback.diagonal (flatDeformationMap i h').hom.hom))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
