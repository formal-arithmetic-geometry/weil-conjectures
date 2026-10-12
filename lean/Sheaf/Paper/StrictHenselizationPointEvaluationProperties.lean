/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluationImage
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples

/-! # Surjectivity of pointed evaluation

Source: Stacks Project, Tags 04GW and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-properties).
-/

@[expose] public section

universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The codomain-restricted pointed evaluation ring homomorphism. -/
noncomputable def strictHenselizationPointEvaluationToSep
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom) :
    strictHenselizationRing barY →+*
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
  (strictHenselizationPointEvaluation barY).codRestrict _
    (strictHenselizationPointEvaluation_mem barY hΩ)

/-- The codomain-restricted pointed evaluation map is surjective.
Source: Stacks Project, Tags 04GW and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-properties).

Proof: Choose an affine chart U through the image of barY and lift barY to U.
The chart residue field identifies with the residue field of Y via the open
immersion. This identification respects their embeddings into Ω: apply the
composition formula for descResidueField to the pointed chart factorization and
use hΩ. Hence their relative separable closures identify by that same embedding
in Ω, rather than by an arbitrary abstract field isomorphism.
Apply etale_local_ring_triples to this chart. The inclusion of chart-neighbourhoods
is initial, and its opposite ring-diagram inclusion is final. Together with the
small-model equivalence, this identifies the chosen ring colimit with the
residue-triple colimit. Its isomorphisms commute with coprojections, as specified
in etale_local_ring_triples. On each chart-neighbourhood, the triple residue map,
followed by the inclusion into Ω, equals the neighbourhood's geometric evaluation:
this is the equation for the triple embedding in etale_local_ring_triples combined
with the coprojection equation in strictHenselization_triples. Colimit uniqueness
therefore identifies the transported triple map with our evaluation map; injectivity
of the relative closure's inclusion identifies the maps with values in that closure.
Surjectivity now follows from strictHenselization_triples and bijectivity of the
colimit and relative-closure identifications. No local-ring hypothesis is used. -/
theorem strictHenselizationPointEvaluationToSep_surjective
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom) :
    Function.Surjective (strictHenselizationPointEvaluationToSep barY hΩ) := by
  sorry

end AlgebraicGeometry.Scheme
