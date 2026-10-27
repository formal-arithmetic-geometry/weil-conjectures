/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.FiniteCoefficientAdjointData

/-! # Invertible normalized comparison for one coefficient arrow

Source: current blueprint reduction-exceptional, Locality and Charts, and the
ordinary closed-support argument in the parent node, proof steps 5--6.
(blueprint: lem-pur-finite-stage-normalized-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- One coefficient arrow has a unique projection and invertible counit-normalized mate
between the specified finite-stage adjunctions.

Source: current blueprint reduction-exceptional, Locality and Charts; parent
lem-pur-finite-coefficient-adjoint-comparisons, proof steps 5--6.
(blueprint: lem-pur-finite-stage-normalized-change).

Proof: identify the stage rings with positive DVR quotients using stage_ramification.
A bounded flat constructible model stays flat and constructible after coefficient
extension, giving both tensor preservation clauses. The finite-Tor site equivalence
and exact faithful comparison show that every retained bounded etale witness has
finite-Tor amplitude; scalar extension therefore remains bounded below. Open tensor
balancing and the proper direct-image coefficient comparison give an invertible q
on the etale site. Transport it using the specified site/coefficient square; its
value at any retained witness is projectionAtWitness, by naturality and full
faithfulness of comparison. Define b as the transpose of q inverse followed by the
scalar-extended A-counit. On an affine-space projection its invertibility follows
from etaleAffineProjectionCoefficientMate. For a closed immersion, tensor the
injective support sequence with a flat K-flat model of the target coefficient
ring, after restriction of scalars. The K-flat support-comparison theorem supplies
a morphism of distinguished support triangles with middle identity and invertible
open term. Two-out-of-three makes its supported term invertible. The supported
triangle mate-identification theorem identifies that term with the specified b,
using the counit equation and the vanishing of Hom from a supported object to an
open direct image in every shift. Affine factorization, adjoint locality and mate
pasting identify restrictions of b with these two invertible cases; conservative
geometric stalks prove global invertibility. Site comparison transports back to
pro-etale functors with their normalized counits. The counit equation holds by
construction. Transpose the proposed unit equation: naturality of q and the two
triangle identities reduce it to the identity. For uniqueness the tensor bounds
are proofs, q is fixed at every witness (each object has one), and b is fixed by
its transpose. These arguments apply to equal levels, identities, quotient maps,
finite-free extensions, and their mixed composites without assuming flatness. -/
theorem finite_stage_normalized_change
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    {s t : Stage l E} (a : Arrow s t) (c : Compactification f) :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∀ (dA : AdjointDatum s.ring c) (dB : AdjointDatum t.ring c),
      ∃! q : Change a.ringMap c dA dB, True := by sorry

end AlgebraicGeometry.FiniteCoefficientAdjoints
