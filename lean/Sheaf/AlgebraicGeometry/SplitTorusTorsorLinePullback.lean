/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Line modules on split torus torsors

Source: Stacks Project, Divisors, Tag 0BD9 (lemma-extend-invertible-module),
and EGA II, Remark 4.2.7, printed p.75, applied to the coordinate projective-line
compactifications (blueprint: lem-sfb-split-torus-torsor-line-pullback).

The torsor uses the existing represented-right-torsor structure and the actual split
multiplicative group. The conclusion uses tensor inverse image of module sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every invertible module on a split torus torsor over a smooth separated finite-type
scheme over a field is the tensor inverse image of an invertible module on the base.
No uniqueness of that base module is asserted.

Source: Stacks Project, Tag 0BD9, and EGA II, Remark 4.2.7, printed p.75.
(blueprint: lem-sfb-split-torus-torsor-line-pullback)

Proof plan:
1. Apply lem-sfb-split-torus-torsor-frame-geometry to write the torsor as the tower
   Y_r -> ... -> Y_0 = X of coordinate frame bundles. Each step q_j factors as an
   open immersion i_j into P_j = P(O + B_j), followed by its projective projection.
   All P_j are smooth over k, and the first quotient summand trivializes i_j^*O(1).
2. By lem-weil-pbc-smooth-scheme-over-field-regular each P_j is locally Noetherian
   with regular local rings. Apply lem-trf-regular-local-ufd-boundary-factorization
   with no selected parameters to obtain UFD stalks. Then
   lem-sfb-invertible-extension-factorial-complement extends each line M_j on Y_j
   to a line on P_j (Stacks 0BD9).
3. By lem-sfb-projective-bundle-picard-classification that extension is
   O(d_j) tensor p_j^*M_{j-1}, for a locally constant integer degree d_j. Restrict
   using lem-weil-pbc-module-pullback-tensor and
   lem-pc-module-pullback-identity-composition. The first-summand frame trivializes
   O(1) on Y_j, hence its positive and dual powers. These trivializations glue over
   the disjoint degree level sets, giving M_j isomorphic to q_j^*M_{j-1}.
4. Starting from L on Y_r, repeat down the finite tower and take N = M_0.
   The composition comparison of lem-pc-module-pullback-identity-composition gives
   L isomorphic to q^*N. In rank zero the frame-geometry theorem identifies q with
   the identity, and its identity-pullback comparison gives the same conclusion. -/
theorem split_torus_torsor_line_pullback
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [Smooth X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (r : ℕ) (P : RepresentedRightTorsor (MultiplicativeType.splitTorus k r) X)
    (L : P.space.left.Modules) [L.IsInvertible] :
    ∃ N : X.left.Modules, N.IsInvertible ∧
      Nonempty (L ≅ (Scheme.Modules.tensorPullback P.projection.left).obj N) := by
  sorry

end AlgebraicGeometry
