/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples

/-! # The pointed map from the neighbourhood colimit to its residue closure

Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-pointed-map).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The compatible residue maps give a surjection to the relative separable closure.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-pointed-map).

Proof: Choose an affine open containing the geometric point. By
`Scheme.etale_local_ring_triples`, the residue embedding of every neighbourhood
lying over that open lands in the relative separable closure. These embeddings
commute with pointed transition morphisms. The initial inclusion of these
neighbourhoods therefore gives a compatible family on the whole coordinate-ring
diagram, and its colimit map psi. Under the colimit comparison with the triple
diagram this is precisely the map psi of `Scheme.strictHenselization_triples`.
That theorem proves surjectivity and identifies its kernel with the maximal ideal.
Transport both assertions along the colimit comparison. The identification of the
chart residue field with the residue field of Y respects the given embedding into
Omega, by hOmega. The triple theorem's coprojection equation and the natural
isomorphism in `Scheme.etale_local_ring_triples` give the displayed pointed
factorization for neighbourhoods over the chart. Every neighbourhood receives a
pointed map from one over the chart. Cone naturality and the equation defining a
pointed map extend that factorization to every representative j.
-/
theorem strictHenselizationPointedMap
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barY)] :
    ∃ ψ : Scheme.strictHenselizationRing barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      Function.Surjective ψ ∧
      RingHom.ker ψ = IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing barY) ∧
      ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
        Spec.map (CommRingCat.ofHom
          ((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              ψ)) ≫
          (Scheme.strictHenselizationCone barY).π.app (Opposite.op (Opposite.op j)) ≫
          (Spec (Opposite.unop ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by sorry

end AlgebraicGeometry
