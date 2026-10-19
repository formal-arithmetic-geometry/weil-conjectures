/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProperBasic
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry

/-! # Fibre ampleness near a point of a Noetherian base

Source: Stacks Project, Cohomology of Schemes, Tag 0D2N, lemma-ample-in-neighbourhood;
choose an affine open inside the relative-ampleness neighbourhood.
(blueprint: lem-trf-noetherian-fibre-ample-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module ample on a fibre of a proper morphism over a Noetherian base
is absolutely ample over some affine open neighbourhood of the base point.
The explicit invertibility witnesses are supplied by invertible_pullback_tensor;
they impose no extra hypotheses.

Source: Stacks Project, Cohomology of Schemes, Tag 0D2N,
lemma-ample-in-neighbourhood, followed by an affine neighbourhood refinement.
(blueprint: lem-trf-noetherian-fibre-ample-neighbourhood).

Proof, following the node's nine steps:
1. If the fibre is empty, properness makes the image of Z closed and disjoint from s. Choose an
affine neighbourhood disjoint from that image. Its inverse image is empty, so absolute ampleness
is vacuous. Otherwise proper base change makes the nonempty fibre proper (def-pc-scheme-fibre,
def-weil-proper-morphism, lem-weil-pbc-proper-base-change).

2. Use lem-trf-ample-fibre-section-lifting to obtain d0. Choose N at least max(1,d0). The Nth power
is ample by lem-sc-ample-positive-tensor-power. Apply
lem-weil-pbc-ample-very-ample-immersion-affine-base on the fibre to obtain an immersion for a
further positive power d = N*a, hence d >= d0. Identify the two projective-space and twist models by
lem-trf-projective-bundle-quotient-geometry.

3. The target projective space is separated; lem-weil-pbc-proper-to-separated and
lem-weil-pbc-proper-immersion-closed make that immersion closed. The quotient description of
lem-trf-projective-bundle-quotient-geometry gives generating coordinate sections of the dth power
whose associated morphism is this closed immersion.

4. Lift those finitely many sections using lem-trf-ample-fibre-section-lifting. Intersect their
neighbourhoods and refine to an affine neighbourhood. Use lem-weil-pbc-invertible-pullback-tensor
for the tensor/pullback section identifications, and lem-weil-pbc-proper-base-change for properness
of the restriction.

5. The complement of the union of the nonvanishing opens is closed by
lem-weil-pbc-nonvanishing-section-trivializes. The fibre-generating criterion
lem-weil-pbc-invertible-generating-sections-fibre and the residue-value formula of
lem-weil-pbc-invertible-pullback-tensor show it misses the fibre. Properness makes its image closed.
Shrink to an affine neighbourhood avoiding this image, so the lifted sections generate everywhere.

6. The generating quotient defines a morphism to projective space and identifies the pullback of
O(1) with the dth power, by lem-trf-projective-bundle-quotient-geometry. Naturality identifies its
fibre with the original closed immersion. Proper base change and lem-weil-pbc-proper-to-separated
make this projective-space morphism proper.

7. The fibre map is injective on points, so over every point of the projective-space fibre the
morphism has at most one point in its fibre (def-pc-scheme-fibre and def-weil-closed-immersion).
Apply lem-trf-proper-finite-fibre-finite-near and glue the resulting neighbourhoods by
lem-weil-pbc-closed-finite-etale-zariski-local. This includes empty fibres outside the image of the
closed immersion.

8. Projective space is proper over the base by lemma-nagata-projective-space-base-change-proper. The
image of the complement of the finite locus is closed and misses s. Choose an affine neighbourhood V
avoiding it. Restrict and glue finite morphisms using def-weil-finite-integral-morphism and
lem-weil-pbc-closed-finite-etale-zariski-local.

9. The morphism defined by the generating sections has standard-chart preimages equal to their
nonvanishing opens (def-weil-pbc-morphism-to-projective-space-by-sections,
lem-trf-projective-bundle-quotient-geometry, lem-weil-pbc-projective-morphism-chart-preimage). Those
charts are affine over affine V by lem-weil-pbc-projective-space-standard-charts, and finite inverse
images are affine by def-weil-finite-integral-morphism. Proper base change and pqf-lem-proper-basic
give quasi-compactness. The positive-power sections therefore witness exactly absolute ampleness
(def-weil-pbc-ample-invertible-module).
-/
theorem exists_affine_isAmple_of_fiber_of_noetherian {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] [CompactSpace S]
    (L : Z.Modules) [L.IsInvertible] (s : S)
    (hL : @IsAmple (f.fiber s) ((tensorPullback (f.fiberι s)).obj L)
      ((invertible_pullback_tensor (f.fiberι s)).1 L).2) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L)
        ((invertible_pullback_tensor (f ⁻¹ᵁ V).ι).1 L).2 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
