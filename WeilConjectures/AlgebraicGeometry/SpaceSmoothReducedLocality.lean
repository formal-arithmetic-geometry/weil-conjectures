/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedAlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-!
# Reducedness is local for smooth maps of algebraic spaces

Source: Stacks Project, Descent on Spaces, Tag 0GB3, lemma-reduced-local-smooth
(blueprint: lem-sfb-space-smooth-reduced-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Reducedness ascends along smooth morphisms of algebraic spaces and descends along
surjective smooth morphisms. Smoothness uses the existing test on compatible etale
scheme charts; surjectivity means every field-valued point class is in the point image.

Source: Stacks Project, Descent on Spaces, Tag 0GB3, lemma-reduced-local-smooth
(blueprint: lem-sfb-space-smooth-reduced-locality).

Proof:
1. For a smooth scheme map T -> W with W reduced, choose compatible affine charts
Spec B -> Spec A. The ring A is reduced (def-pc-reduced-scheme), and smoothness
(def-sbc-smooth-morphisms) and lem-sfb-smooth-algebra-over-reduced-ring make B reduced.
These charts cover T. Etale scheme maps are smooth by
lem-weil-pbc-etale-smooth-zero-dimensional-fibres and def-weil-etale-morphism.
2. For a surjective smooth scheme map with reduced source, lift every target point.
The induced local-ring map is flat (lem-weil-pbc-smooth-ring-map-flat,
lem-weil-pbc-flat-local-ring-maps), local, hence faithfully flat
(lem-weil-pbc-flat-local-hom-faithfully-flat), and injective
(lem-weil-pbc-faithfully-flat-universally-injective). Thus every nilpotent in the
target local ring is zero. This proves descent without quasi-compactness.
3. Reducedness can be tested on one surjective etale atlas W -> Z: for any other
chart T -> Z, W x_Z T is a scheme, etale over W and surjective etale over T
(def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers). Apply steps 1
and 2. The identity chart recovers scheme reducedness for representable spaces.
4. Choose a surjective etale atlas V -> Y and an atlas U -> X x_Y V.
The composite U -> X is surjective etale (lem-trf-space-chartwise-etale-permanence).
The scheme map U -> V is smooth by lem-sfb-scheme-etale-source-target-properties
and lem-sfb-space-etale-presentation-property-criterion.
5. If Y is reduced, V is reduced; step 1 makes U reduced, and step 3 makes X reduced.
6. If f is surjective and X reduced, U is reduced and U -> V is surjective, by
base-change stability of point-surjectivity
(lem-sfb-space-smooth-surjective-fppf-locality). Step 2 makes V reduced and step 3
makes Y reduced. An empty source causes no exception: surjectivity forces Y empty. -/
theorem smooth_reduced_locality {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : MapIsLocally (@Smooth) f) :
    (IsReduced Y → IsReduced X) ∧
      ((∀ p : Point Y.obj.obj, p ∈ pointImage f.hom.hom) → IsReduced X → IsReduced Y) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
