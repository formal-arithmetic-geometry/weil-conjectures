/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates

/-! # Affine spectrum composition unit square

Source: Stacks Project, Tag 0D5S, composition coherence used in the affine reduction.
(blueprint: lem-pc-affine-spectrum-composition-unit-square).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The comparison square commutes for the unadjointified composition units.
It involves only composition comparisons and identity comparisons, not the
unit chosen by Equivalence.mk.

Proof: write h,h' for the two spectrum maps, v,v' for their inverses, and q
for Spec.map g'.appTop. Expand the forward comparison as c(g',h), transport
along g';h = h';q, and inverse c(h',q). Expand the inverse comparison as
c(q,v), transport along q;v = v';g', and inverse c(v',g'). Apply the
associativity law to h',q,v: the inverse c(h',q) followed by h'* applied to
c(q,v) becomes c(h',q;v) followed by inverse c(h';q,v), with the associativity
transport. Transport q;v to v';g' and h';q to g';h by the two naturality
identities. Apply associativity to h',v',g' to combine the inverse c(v',g')
with c(h',v') at g'* K. Apply associativity to g',h,v to combine c(g',h)
with the remaining inverse c(g';h,v). The resulting expression consists of
c(g',h;v), transported using h;v=id, followed by the identity comparison,
and the corresponding path using h';v'=id. The two unit laws for c identify
these with g'* applied to c(h,v) followed by i X. Naturality of i moves
its component through the remaining comparison. All transport maps are
induced by equalities of the same composite scheme morphism, so proof
irrelevance identifies them. Evaluating at K gives the displayed equality.
Source: Stacks Project, Tag 0D5S, composition coherence; the second step of
the original cancellation node's proof. Tag 08HY explains its base-change use.
(blueprint: lem-pc-affine-spectrum-composition-unit-square). -/
theorem affineSpectrum_composition_unit_square
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) :
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  (affineSpectrumForwardPullbackIso g').hom.app ((derivedPullback X.isoSpec.inv).obj K) ≫
      (derivedPullback X'.toSpecΓ).map
        ((affineSpectrumDerivedPullbackIso g').hom.app K) ≫
      (c X'.isoSpec.hom X'.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X' ⟶ X' ↦ derivedPullback k) X'.isoSpec.hom_inv_id) ≪≫
      i X').hom.app ((derivedPullback g').obj K) =
    (derivedPullback g').map
      ((c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫
      i X).hom.app K) := by
  sorry

end AlgebraicGeometry
