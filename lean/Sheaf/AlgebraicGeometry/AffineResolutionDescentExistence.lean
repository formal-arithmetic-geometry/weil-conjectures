/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData

/-! # Existence of one regular affine descent of an ordinary resolution rule

Source: ILO, Travaux de Gabber, VIII 2.1.9, 2.2.11 and Remark 2.3.5(ii).
(blueprint: lem-trf-affine-resolution-descent-existence).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Padded overlap compatibility suffices to construct one regular affine descent
on each reduced finite-type rational scheme. This only constructs a tower for one
cover; it asserts neither cover independence nor uniqueness of the extension.

Source: ILO VIII 2.2.11, 2.3.1 and Remark 2.3.5(ii), printed pp.91--92;
parent descent proof, Steps 1--2 and 5--7.
(blueprint: lem-trf-affine-resolution-descent-existence).

Proof: finite type over the Noetherian field Q makes S Noetherian and quasi-compact.
Choose a finite affine open cover; for empty S choose the empty cover. Each chart
and every affine open in an intersection is reduced and finite type over Q, since
opens in a Noetherian scheme are quasi-compact and open immersions are locally of
finite type. Its coordinate algebra has finitely many generators, giving a closed
embedding in affine space. This ambient is smooth, separated and finite type.
Finite disjoint unions of these presentations show that the coproduct T of the
charts is an embeddable rational input. Use its actual coproduct maps to obtain a
ResolutionAffineCover, and let its assigned tower have length n and its given labels.
Retain all n stages on each chart. The padded-overlap hypothesis identifies their
full ideals and blowups on affine refinements of every double and triple overlap.
Induct on those n labels, starting with S. At a given level, define its ideal on an
open V to consist of sections whose restrictions to every lifted chart belong to
that chart's center ideal. Overlap equality shows that this restricts to the given
ideal on each chart. The sheaf condition proves that it is an ideal sheaf and that
it is unique with those restrictions. Quasi-coherence and finite type are local.
For coherence, the kernel of any map from a finite free module restricts to the
finite-type kernel for each coherent chart ideal; these local generators prove
finite type of the kernel, including on charts with unit ideal. Blow up that ideal.
Flat base change along the lifted open charts identifies the next level with their
next assigned levels, preserving all transitions and centers; uniqueness of blowup
lifts proves agreement on refinements. Continue to the last label, producing the
full cartesian map to A(T) without contraction. Every center is nonempty because
its pullback to T is; it has empty interior because any nonempty open in its support
would meet a chart in a nonempty open of the local center. Its local rings are
regular because its chart pieces are open pieces of the regular center on T.
The same local-ring argument proves regularity of the last level. Properness of
finite-type blowups and finite-type composition give finite type of every level
over Q. Thus the resulting tower is a resolution and is an affine descent. With
the empty cover, A(T) has length zero, and the induction constructs the trivial tower.
-/
theorem exists_affine_resolution_descent {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) (_hpad : A.HasPaddedOverlaps)
    (S : RationalResolutionInput.{u}) :
    ∃ B : LabeledOrdinaryTower L S.scheme, B.IsResolution ∧ A.IsAffineDescent S B := by
  sorry

end AlgebraicGeometry
