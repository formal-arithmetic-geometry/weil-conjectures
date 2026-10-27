/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.SpaceConstructibleTopology
public import Sheaf.AlgebraicGeometry.UniversallySubtrusive
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Topology.ConstructibleInConstructible
import WeilConjectures.Topology.ConstructibleIntersection
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Topology.ProconstructibleClosureSpecialization

/-! # Comparison of constructible topologies on algebraic spaces

Source: Rydh, Submersions and effective descent of étale morphisms,
Proposition (1.2)(i), Corollary (1.5), Remark (1.8), pp.4--7;
Stacks Project, Tags 054I, 054J, 03BX and 0903
(blueprint: lem-sfb-space-constructible-topology-comparison).

The scheme topology is the existing local affine-chart topology; the space topology is
final for all representable étale affine charts. The statements identify these on schemes,
identify the latter with every atlas quotient, and give continuity, fineness and closedness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite Topology

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme and algebraic-space constructions agree under the usual scheme point map.
Source: Rydh, Proposition (1.2)(i), Remark (1.8); Stacks, Tags 054I, 054J and 03BX
(blueprint: lem-sfb-space-constructible-topology-comparison).
Proof: step 1 of the node uses affine spectrality and
[lem-weil-pbc-spectral-constructible-clopen-constructible-topology] to identify the affine
patch basis with constructible subsets. Step 2 glues affine charts: on an affine open
inside another, [lem-weil-pbc-constructible-in-retrocompact-open] and
[lem-weil-pbc-constructible-intersection-in-constructible] identify the induced topologies.
Step 3 applies [lem-pur-scheme-constructible-preimage] on affine neighbourhoods to prove
scheme morphisms patch continuous. Step 4 applies affine Chevalley
[lem-weil-pbc-chevalley-constructible-image] to prove étale scheme maps patch open;
étaleness of restrictions follows from [lem-weil-pbc-etale-composition-cancellation],
and quasi-compactness over affine targets from [lem-weil-pbc-qcqs-morphism-permanence].
Step 6 compares any étale presentation with any scheme chart using their fibre product
and [lem-a1-space-atlas-test-open-subsets]. For a scheme, its identity chart and its affine
open charts identify the final chart topology with the local scheme topology. -/
theorem scheme_pointConstructibleTopology_eq {S : Scheme.{u}} (T : Over S)
    (hT : QuasiSeparatedSpace T.left) :
    TopologicalSpace.induced (schemePointMap (𝟙 (yoneda.obj T)))
      (pointConstructibleTopology (yoneda.obj T)) = T.left.localConstructibleTopology := by
  sorry

/-- Every surjective representable étale scheme presentation is a constructible quotient.
The topology on its scheme source is local on affine open charts, so its source need not
be quasi-compact or quasi-separated. Equality with this quotient for every presentation
expresses independence of the presentation.
Source: Rydh, Corollary (1.5), Remark (1.8); Stacks, Tags 054I, 054J and 03BX
(blueprint: lem-sfb-space-constructible-topology-comparison).
Proof: steps 1--4 give the constructible basis, affine gluing, scheme continuity and étale
openness as in `scheme_pointConstructibleTopology_eq`. In step 6 take the fibre product
of the given presentation with any étale chart. By
[lem-a1-space-atlas-test-open-subsets], its projection to the chart is surjective étale,
and its other projection is étale. Pull back a patch-open subset of the presentation and
push it down by the open surjection; the stated image equality gives its inverse image on
the chart. Conversely, test on all affine opens of the presentation, which are étale charts
by [lem-weil-pbc-open-immersion-etale] and [lem-trf-space-chartwise-etale-permanence].
This identifies its quotient topology with the final topology of all affine étale charts.
Surjectivity on points is [lem-a1-space-affine-etale-cover]. -/
theorem isQuotientMap_schemePointMap_constructible {S : Scheme.{u}}
    (X : AlgebraicSpace S) (hX : IsAbsolutelyQuasiSeparated X)
    (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (he : IsEtale p) (hs : IsSurjective p) :
    @IsQuotientMap U.left (Point X.obj.obj) U.left.localConstructibleTopology
      (pointConstructibleTopology X.obj.obj) (schemePointMap p) := by
  sorry

/-- Every morphism of quasi-separated algebraic spaces is constructibly continuous.
Source: Rydh, Proposition (1.2)(i), Remark (1.8); Stacks, Tags 054I and 03BX
(blueprint: lem-sfb-space-constructible-topology-comparison).
Proof: step 7 chooses scheme atlases of source and target using
[lem-a1-space-affine-etale-cover]. Pull back the target atlas to the source atlas using
[lem-a1-space-atlas-test-open-subsets]. Scheme patch continuity (step 3) and openness of
the surjective étale projection (step 4) show that the inverse image of any patch-open set
is patch open on the source atlas. The atlas quotient criterion (step 6) proves continuity.
Neither the morphism nor either atlas is assumed quasi-compact. -/
theorem continuous_mapPoint_constructible {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (hX : IsAbsolutelyQuasiSeparated X) (hY : IsAbsolutelyQuasiSeparated Y) (f : X ⟶ Y) :
    @Continuous (Point X.obj.obj) (Point Y.obj.obj)
      (pointConstructibleTopology X.obj.obj) (pointConstructibleTopology Y.obj.obj)
      (mapPoint f.hom.hom) := by
  sorry

/-- The constructible topology is finer than the atlas Zariski topology.
Source: Rydh, Proposition (1.2)(i), Remark (1.8); Stacks, Tag 03BX
(blueprint: lem-sfb-space-constructible-topology-comparison).
Proof: step 8 pulls a Zariski open back to each affine étale chart using the continuity
in [lem-a1-space-affine-etale-cover]. On an affine chart a Zariski open is a union of
quasi-compact affine opens, hence patch open by steps 1--2. The definition of the final
constructible topology now gives the assertion. -/
theorem pointConstructibleTopology_le {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hX : IsAbsolutelyQuasiSeparated X) :
    pointConstructibleTopology X.obj.obj ≤ pointTopologicalSpace X.obj.obj := by
  sorry

/-- Zariski closed subsets are exactly constructibly closed specialization-stable subsets.
The specialization condition is explicitly in the original atlas Zariski topology.
Source: Rydh, Proposition (1.2)(i), Remark (1.8); Stacks, Tags 0903 and 03BX
(blueprint: lem-sfb-space-constructible-topology-comparison).
Proof: step 5 works on affine spectral charts. A patch-closed set is an intersection of
constructible sets by step 1. The lemma
[lem-weil-pbc-spectral-proconstructible-closure-specialization] expresses each point of
its Zariski closure as a specialization of a point of the set; specialization stability
therefore makes it closed. In step 9 pull back the given subset to each affine étale chart.
Step 6 gives patch closedness, and Zariski continuity from
[lem-a1-space-affine-etale-cover] preserves specializations. Step 5 makes each inverse
image Zariski closed. Affine open covers of every étale chart and
[lem-weil-pbc-open-immersion-etale], [lem-trf-space-chartwise-etale-permanence] extend this
to all chart tests; [def-a1-space-point-topology] makes the original subset closed.
Conversely step 8 makes a Zariski closed subset patch closed, and a closed subset contains
the closure of each of its points. Empty subsets, whole subsets and empty spaces are included. -/
theorem isClosed_iff_constructible_closed_specialization {S : Scheme.{u}}
    (X : AlgebraicSpace S) (hX : IsAbsolutelyQuasiSeparated X) (F : Set (Point X.obj.obj)) :
    IsClosed F ↔ IsClosed[pointConstructibleTopology X.obj.obj] F ∧
      ∀ x ∈ F, ∀ z : Point X.obj.obj, z ∈ closure ({x} : Set (Point X.obj.obj)) → z ∈ F := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
