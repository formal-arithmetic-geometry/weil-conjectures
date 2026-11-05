/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties

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
    [IsLocalRing (Scheme.strictHenselization barY)] :
    ∃ ψ : Scheme.strictHenselization barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      Function.Surjective ψ ∧
      RingHom.ker ψ = IsLocalRing.maximalIdeal (Scheme.strictHenselization barY) ∧
      ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
        Spec.map (CommRingCat.ofHom
          ((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              ψ)) ≫
          (Scheme.strictHenselizationAffineCone barY).π.app (Opposite.op (Opposite.op j)) ≫
          (Spec (Opposite.unop ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
  let ψ := Scheme.strictHenselizationPointEvaluationToSep barY hΩ
  have hp := Scheme.strictHenselizationPointEvaluationToSep_surjective barY hΩ
  refine ⟨ψ, hp, IsLocalRing.ker_eq_maximalIdeal ψ hp, ?_⟩
  intro j
  have h := Scheme.strictHenselizationPointEvaluation_pointed barY j
  have he : ((IntermediateField.val
      (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        (Scheme.strictHenselizationPointEvaluationToSep barY hΩ)) =
      Scheme.strictHenselizationPointEvaluation barY := by
    ext a
    rfl
  rw [he]
  exact h

end AlgebraicGeometry
