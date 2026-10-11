/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Étale near a point smooth of fibre dimension zero

Source: Stacks Project, Tag 0A43, final sentence of the proof; Tags 02G1, 02G2 and
02GI (blueprint: lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism smooth on an open neighbourhood of `x`, whose scheme-theoretic fibre has
local dimension zero at `x`, is étale on a smaller open neighbourhood contained in the given one.
Source: Stacks Project, Tag 0A43, final sentence of the proof, and Tags 02G1, 02G2, 02GI
(blueprint: lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension).

Proof:
1. The fibre of `U.ι ≫ f` is an open subscheme of the fibre of `f`
   (lem-weil-pbc-open-fibre-product, def-pc-scheme-fibre). The corresponding point lies in
   this open, and its local dimension is unchanged
   (lem-weil-pbc-dimension-at-point-open-subspace, def-kun-topological-dimension-at-point).
   Thus the dimension of the restricted fibre at that point is zero.
2. Apply lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension to the smooth restriction.
   On suitable affine neighbourhoods in source and target, the Kähler differential module
   (def-weil-pbc-kahler-differentials) is free of rank equal to that fibre dimension, hence of
   rank zero. It is therefore zero (Stacks 02G1, 01UT).
3. Apply lem-weil-pbc-smooth-zero-differentials-affine-open-etale: smoothness and vanishing
   differentials imply that the source affine neighbourhood maps étale to `S` (Stacks 00U1,
   02GI). This neighbourhood is open in `U`, hence open in `X`, contains `x`, and is contained
   in `U`. It is the required `U'`. -/
theorem exists_etale_open_of_smooth_of_fibre_dimension_zero
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (U : X.Opens) (hx : x ∈ U)
    (hSmooth : Smooth (U.ι ≫ f)) (hDim : topologicalKrullDimAt (f.asFiber x) = 0) :
    ∃ U' : X.Opens, U' ≤ U ∧ x ∈ U' ∧ Etale (U'.ι ≫ f) := by
  sorry

end AlgebraicGeometry
