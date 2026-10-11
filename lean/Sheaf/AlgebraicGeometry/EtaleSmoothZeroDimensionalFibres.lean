/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# An étale morphism is smooth with zero-dimensional fibres

Source: Stacks Project, remark after Definition 02GI, Lemmas 02GK, 02GL and 02H6
(blueprint: lem-weil-pbc-etale-smooth-zero-dimensional-fibres).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An étale morphism `f : X ⟶ S` is smooth; for every `x : X` the scheme-theoretic fibre
`f.fiber (f x) = X ×_S Spec κ(f x)` has dimension `0` at the point `f.asFiber x`
corresponding to `x`; in other words `f` is smooth of relative dimension zero.
Source: Stacks Project, remark after Definition 02GI, Lemmas 02GK, 02GL, 02H6
(blueprint: lem-weil-pbc-etale-smooth-zero-dimensional-fibres).

Proof:
1. `f` is smooth: by def-weil-etale-morphism it is locally of finite presentation, flat and
   unramified; by lem-weil-pbc-flat-unramified-formally-etale every first order thickening
   lifting problem of affine schemes over `S` has a (unique) solution, so `f` is formally
   smooth (def-sbc-formally-smooth), hence smooth (def-sbc-smooth-morphisms).
2. The point is isolated in its fibre: by lem-weil-pbc-etale-fibre-discrete-separable-points
   the underlying space of `X_s` is discrete, so `{x'}` is open in `X_s` (Stacks 02GL).
3. The dimension at `x'` is `0`: every open neighbourhood of `x'` is nonempty, so has
   dimension `≥ 0`, and the one-point open `{x'}` has dimension `0` (def-kun-dimension).
   Hence `f` is smooth of relative dimension zero (def-sbc-smooth-morphisms). -/
theorem smooth_and_fibre_dimension_zero_of_etale
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    Smooth f ∧ (∀ x : X, topologicalKrullDimAt (f.asFiber x) = 0) ∧
      SmoothOfRelativeDimension 0 f := by
  sorry

end AlgebraicGeometry
