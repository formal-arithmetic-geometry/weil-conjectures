/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Clopen dimension loci in proper smooth connected families

Source: Stacks Project, Morphisms, Tags 02G1, 02G2, 02NK, 01W1, 01W4, 01TH;
Varieties, Tags 0387 and 06LH. Agent-formulated consequence
(blueprint: lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The geometric fibre dimension partitions the base of a proper smooth family with
nonempty connected geometric fibres into clopen loci. On each locus the geometric fibres
have the indicated pure dimension, and the dimension-zero family is quasi-finite.
Source: Stacks Project, Morphisms, Tags 02G1, 02G2, 02NK, 01W1, 01W4, 01TH;
Varieties, Tags 0387 and 06LH.
(blueprint: lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci)

Proof:
1. The local fibre dimension is locally constant by
   sbc-lem-smooth-relative-dimension-locally-constant, and is a finite natural number by
   lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension. Its rank loci in X are
   disjoint clopen subsets covering X.
2. By lem-weil-geometrically-connected-algebraic-closure, each ordinary fibre is nonempty
   and connected. The trace of each rank locus is clopen in that fibre, so precisely one
   rank occurs throughout it (def-pc-scheme-fibre, def-weil-connected-scheme).
3. Restrict to a rank locus using lem-pc-open-immersion-smooth-composition and
   lem-weil-pbc-open-fibre-product. Local dimensions are unchanged on opens by
   lem-weil-pbc-dimension-at-point-open-subspace. The restriction is smooth of that
   relative dimension (def-sbc-smooth-morphisms). By
   lem-sbc-smooth-relative-dimension-permanence, its geometric fibres have the same pure
   dimension. Thus the rank is at most d, and the rank loci are saturated inverse images
   of the dimension loci in S.
4. Properness makes the images of a rank locus and its complement closed. Saturation
   and nonempty fibres identify these images with complementary subsets of S. The
   dimension loci are therefore clopen, disjoint, and cover S.
5. Give these loci their open subscheme structures. Properness and smoothness survive
   base change (lem-pc-proper-base-change). Open restriction preserves the local rings
   and residue fields, so lem-weil-pbc-open-fibre-product and def-pc-base-change identify
   the restricted fibres with the original fibres. They remain nonempty and geometrically
   connected, and their geometric fibres have the asserted pure dimension.
6. The dimension-zero restriction is of finite type by properness. Its fibres are
   zero-dimensional finite-type schemes over fields. By lem-sc-dim0-finite each has
   finitely many closed points, so each singleton is open. The isolated-fibre-point
   definition pqf-def-quasifinite now gives quasi-finiteness, also for an empty locus. -/
theorem proper_smooth_connected_fibre_dimension_loci
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Smooth f]
    (d : ℕ)
    (hconnected : ∀ s : S, ConnectedSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))
    (hbound : ∀ s : S, topologicalKrullDim
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) ≤
        (d : WithBot ℕ∞)) :
    ∃ U : Fin (d + 1) → S.Opens,
      (∀ i : Fin (d + 1), (U i : Set S) = {s : S | topologicalKrullDim
        ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) =
          (i.val : WithBot ℕ∞)}) ∧
      (∀ i : Fin (d + 1), IsClosed (U i : Set S)) ∧
      Pairwise (fun i j : Fin (d + 1) ↦ Disjoint (U i : Set S) (U j : Set S)) ∧
      (⨆ i : Fin (d + 1), U i) = ⊤ ∧
      (∀ i : Fin (d + 1),
        IsProper (pullback.snd f (U i).ι) ∧ Smooth (pullback.snd f (U i).ι) ∧
        ∀ s : (U i).toScheme,
          Nonempty ((pullback.snd f (U i).ι).fiber s) ∧
          GeometricallyConnected ((pullback.snd f (U i).ι).fiberToSpecResidueField s) ∧
          (pullback (pullback.snd f (U i).ι)
            (Spec.map (CommRingCat.ofHom (algebraMap ((U i).toScheme.residueField s)
              (AlgebraicClosure ((U i).toScheme.residueField s)))) ≫
                (U i).toScheme.fromSpecResidueField s)).IsPureDimension i.val) ∧
      (pullback.snd f (U 0).ι).IsQuasiFinite := by
  sorry

end AlgebraicGeometry
