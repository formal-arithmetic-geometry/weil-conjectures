/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.JacobsonSpace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Closed points of a product

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary` (blueprint: lem-kun-closed-points-of-product).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Let `X` and `Y` be schemes of finite type over a field `K`. A point of their
fibre product over `K` is closed exactly when both of its projections are closed
(blueprint: lem-kun-closed-points-of-product).

Proof (blueprint: lem-kun-closed-points-of-product, order 1745; source proof at the
corresponding blueprint node). Put `P = X ×_K Y`. Finite affine covers of `X` and `Y`
by finitely generated `K`-algebras give a finite affine cover of `P`, using the open
fibre-product and affine fibre-product lemmas and the finite tensor-generator argument;
thus `P` is of finite type. If `z` is closed, its residue field is finite over `K` by
`closedPoint_iff_residueField_trdeg_zero_and_finite`; the residue-field maps from the
images of `z` are injective, so both image residue fields are finite over `K`, and the
same theorem makes the images closed. Conversely, if both images are closed, their
residue fields are finite over `K`, so their tensor product is finite-dimensional over
`K`. The kernel of the canonical map from this tensor product to the residue field of
`z` is prime, and the residue-field description of fibre-product points identifies the
residue field of `z` with the fraction field of the quotient. A nonzero element of this
finite-dimensional domain acts injectively and hence surjectively, so the quotient is a
field; therefore the residue field of `z` is finite over `K`. Applying the closed-point
criterion to the finite-type product proves that `z` is closed. -/
theorem closedPoint_iff_of_finiteType_product
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (z : ↑(pullback f g)) :
    z ∈ closedPoints (↑(pullback f g)) ↔
      pullback.fst f g z ∈ closedPoints X ∧
        pullback.snd f g z ∈ closedPoints Y := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace g
  constructor
  · intro hz
    exact ⟨(pullback.fst f g).closePoints_subset_preimage_closedPoints hz,
      (pullback.snd f g).closePoints_subset_preimage_closedPoints hz⟩
  · rintro ⟨hx, hy⟩
    let i := X.fromSpecResidueField (pullback.fst f g z)
    have : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
    have : IsFinite (i ≫ f) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
    let a := pullback.fst i (pullback.fst f g)
    let j := pullback.snd i (pullback.fst f g)
    let q := j ≫ pullback.snd f g
    have hcart : IsPullback a q (i ≫ f) g :=
      (IsPullback.of_hasPullback i (pullback.fst f g)).paste_vert
        (IsPullback.of_hasPullback f g)
    have : IsFinite q := MorphismProperty.of_isPullback hcart inferInstance
    have hz : z ∈ Set.range j := by
      rw [Scheme.Pullback.range_snd]
      simp [i]
    obtain ⟨w, hw⟩ := hz
    have hqw : q w = pullback.snd f g z := by
      simp [q, hw]
    have hwclosed : IsClosed ({w} : Set ↑(pullback i (pullback.fst f g))) :=
      isClosed_of_subset_discrete_closed
        (by simpa only [Set.singleton_subset_iff, Set.mem_preimage, Set.mem_singleton_iff]
              using hqw)
        (q.isDiscrete_preimage_singleton (pullback.snd f g z))
        (hy.preimage q.continuous)
    apply mem_closedPoints_iff.mpr
    simpa only [Set.image_singleton, hw] using j.isClosedEmbedding.isClosedMap _ hwclosed

end AlgebraicGeometry
