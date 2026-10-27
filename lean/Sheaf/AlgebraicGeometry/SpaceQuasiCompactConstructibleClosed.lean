/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.SpaceConstructibleTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceConstructibleTopologyComparison
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Spectral.ConstructibleTopology
import Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff

/-! # Quasi-compact morphisms are constructibly closed

Source: Rydh, Submersions and effective descent of étale morphisms,
Proposition (1.2)(ii), p.4, and Remark (1.8), pp.6--7; EGA I, Proposition 7.2.12(iv)
(blueprint: lem-sfb-space-quasicompact-constructible-closed).

The quasi-compactness and absolute quasi-separatedness predicates, the map on point
classes, and the final constructible topologies are the existing project constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact morphism of quasi-separated algebraic spaces takes every constructibly
closed subset to a constructibly closed subset.
Source: Rydh, Proposition (1.2)(ii), Remark (1.8), pp.4,6--7;
EGA I, Proposition 7.2.12(iv)
(blueprint: lem-sfb-space-quasicompact-constructible-closed).

Proof:
1. Fix a constructibly closed subset F of X and an affine representable étale chart
   u : V → Y. Form Z = X ×_Y V by [lem-trf-space-fibre-products-etale-covers]. Its point
   space is quasi-compact by the hypothesis on f. By [lem-sfb-qc-space-affine-etale-atlas],
   choose a surjective representable étale atlas h : W → Z with W affine. The composites
   a : W → X and g : W → V satisfy f a = u g.
2. The affine schemes W and V are qcqs by [lem-weil-pbc-affine-scheme-qcqs], and spectral
   by [lem-weil-pbc-qcqs-scheme-spectral]. Their constructible topologies are respectively
   quasi-compact and Hausdorff by [lem-weil-pbc-spectral-constructible-topology-quasi-compact]
   and [lem-weil-pbc-spectral-constructible-topology-hausdorff].
3. By [lem-sfb-space-constructible-topology-comparison], a and g are constructibly
   continuous, and the scheme and space constructible topologies agree. Thus C = a⁻¹(F)
   is closed in constructibly quasi-compact W, hence quasi-compact: adjoin its open
   complement to any open cover and restrict a finite subcover of W.
4. By [lem-weil-pbc-continuous-image-quasi-compact], K = g(C) is quasi-compact. It is
   closed in constructibly Hausdorff V: for a point outside K, choose disjoint
   neighborhoods separating it from each point of K; finitely many neighborhoods cover
   K, and the intersection of the corresponding outside neighborhoods misses K.
   This includes empty K, using the empty intersection.
5. By [lem-a1-space-point-open-calculus], every compatible pair of points of X and V
   lifts to Z, and the surjective representable map h is point-surjective. Consequently
   K = u⁻¹(f(F)). Since this is closed for every affine étale chart of Y, the defining
   final topology makes f(F) closed. -/
theorem isClosedMap_mapPoint_constructible {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (f : X ⟶ Y) (hX : IsAbsolutelyQuasiSeparated X) (hY : IsAbsolutelyQuasiSeparated Y)
    (hf : MapIsQuasiCompact f.hom.hom) :
    @IsClosedMap (Point X.obj.obj) (Point Y.obj.obj)
      (pointConstructibleTopology X.obj.obj) (pointConstructibleTopology Y.obj.obj)
      (mapPoint f.hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
