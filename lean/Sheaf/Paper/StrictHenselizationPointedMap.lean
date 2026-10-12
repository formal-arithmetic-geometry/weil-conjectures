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

/- The compatible residue maps give a surjection to the relative separable closure.
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
/-- The colimit comparison supplies the residue map and its algebraic properties.
Source: Stacks Project, Tag 04HX.

Proof: Construct the compatible residue maps on the affine etale neighbourhood
diagram and pass to its colimit.  The comparison with the strict henselization
triple identifies the resulting map with `ψ`; the triple computation gives
surjectivity and identifies its kernel with the maximal ideal.  The residue
embedding is identified using `hΩ`.
(blueprint: lem-weil-pbc-strict-henselization-pointed-map-core) -/
theorem strictHenselizationPointedMap_core
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barY)] :
    ∃ ψ : Scheme.strictHenselizationRing barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      Function.Surjective ψ ∧
      RingHom.ker ψ = IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing barY) := by
  sorry

/-- The residue map is compatible with every chosen neighbourhood leg.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP.

Proof: For a representative neighbourhood, use the coprojection equation in
the strict henselization triple and the pointed transition maps.  Naturality
of the cone transports the equality from representatives over the chosen
affine chart to every small model.
(blueprint: lem-weil-pbc-strict-henselization-pointed-map-factorization)
-/
theorem strictHenselizationPointedMap_factorization
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barY)] :
    ∀ ψ : Scheme.strictHenselizationRing barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      (∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
        Spec.map (CommRingCat.ofHom
          ((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              ψ)) ≫
          (Scheme.strictHenselizationCone barY).π.app (Opposite.op (Opposite.op j)) ≫
          (Spec (Opposite.unop ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left) := by
  sorry

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
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
  obtain ⟨ψ, hsurj, hker⟩ := strictHenselizationPointedMap_core barY hΩ
  refine ⟨ψ, hsurj, hker, ?_⟩
  exact strictHenselizationPointedMap_factorization barY hΩ ψ


end AlgebraicGeometry
