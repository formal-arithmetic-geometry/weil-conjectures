/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.IntrinsicLabeledResolution

/-!
# Rigidity of smooth pullback comparisons of ordinary towers

Source: ILO VIII 2.1.1, 2.1.5, 2.1.9, pp.86--88; Stacks 0806.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Smooth contracted cartesian comparisons between fixed labeled ordinary towers
are unique. No synchronization or choice of embedding is involved in this assertion.

Source: ILO VIII 2.1.1, 2.1.5, 2.1.9, pp.86--88; Stacks 0806, divisors.tex,
lemma-universal-property-blowing-up
(blueprint: lem-trf-intrinsic-resolution-pullback-rigidity).

Proof: Compare two natural transformations by induction on the union of the finite
sets of labels, inserting the specified identity stages at absent labels. At the
bottom cut both maps are determined by h and the initial isomorphisms, by the
cartesian-square equation. Suppose their components agree before a label. Naturality
makes both next components lifts of the same preceding map. The extended center
ideals coincide by the center clauses. If the target label is absent, its transition
is an isomorphism, so cancellation gives equality. Otherwise the next target level
is its ordinary blowup. Use either cartesian comparison at this next cut: its map
is a smooth base change of h, hence flat. The pullback of the invertible exceptional
ideal on the target blowup is therefore invertible. The universal property of that
blowup forces the two lifts to agree. A source label absent at this stage gives the
same argument with its identity transition; no label can appear solely in the source
by retained. This proves equality at every cut by the stage isomorphisms and then
equality of natural transformations. All remaining fields are propositions, so the
comparison structures themselves agree. Empty towers start and end at the initial
step, and stages with a unit ideal are identity stages. -/
theorem intrinsic_resolution_pullback_subsingleton
    {L : Type w} [LinearOrder L] {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (A : IntrinsicLabeledOrdinaryTower L X) (B : IntrinsicLabeledOrdinaryTower L Y) :
    Subsingleton (IntrinsicLabeledResolutionPullback h A B) := by sorry

end AlgebraicGeometry
