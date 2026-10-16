/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.Paper.StrictHenselizationPointEvaluationPointed
import Sheaf.Paper.StrictHenselizationPointEvaluationProperties

/-! # The pointed map from the neighbourhood colimit to its residue closure

Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-pointed-map).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The colimit comparison supplies the residue map and its algebraic properties.
Source: Stacks Project, Tag 04HX.

Proof: Choose an affine chart through the point. The neighbourhood/triple
comparison identifies the chosen small coordinate-ring colimit with the triple
colimit. Transport the triple theorem's surjection across this ring isomorphism.
The open immersion identifies the chart residue field with the residue field of
Y. After restriction of scalars along this field isomorphism, the chart's separable
closure is a separable closure of the latter field. The equivalence of separable
closures identifies it abstractly with the specified relative separable closure.
Compose the surjection with that equivalence. A surjective map from a local ring
to a field has kernel its maximal ideal. This existential assertion requires no
compatibility of the chosen equivalence with the embedding into Ω; it does not
assert that every such surjection is pointed.
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
  let ψ := Scheme.strictHenselizationPointEvaluationToSep barY hΩ
  have hp := Scheme.strictHenselizationPointEvaluationToSep_surjective barY hΩ
  exact ⟨ψ, hp, IsLocalRing.ker_eq_maximalIdeal ψ hp⟩

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
