/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples

/-! # The maximal ideal in an affine chart of the strict henselization

Source: Stacks Project, Tags 04HX, 04GW and 04GP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- Comparing the nested chart, triple and small-model diagrams requires extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- In any affine open chart through which the geometric point factors, the structural
ring map extends the distinguished prime to the maximal ideal of the strict henselization.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-chart-maximal-ideal)

Proof: restrict affine pointed neighbourhoods to those over the chart. This inclusion
is initial by the shrinking argument in Tag 04HX. Identify its opposite with the category
of etale residue triples over R, pointed in the relative separable closure of the residue
field of xR in Ω. The residue embeddings land in this closure because etale residue
extensions are finite separable. The coordinate-ring diagram comparison respects the
R-map on each object. Initiality, this diagram comparison, and the small representative
comparison give a canonical ring isomorphism from the chosen strict-henselization ring
to the triple colimit. Tags 04GW and 04GP say the latter is local with maximal ideal equal
to the extension of the distinguished prime. Transport its local-ring structure and
its R-map through this isomorphism. Ring isomorphisms carry maximal ideals and extended
ideals to the corresponding ideals, giving the displayed equality. On the chart
neighbourhood the coprojection defines the structure morphism; the comparison preserves
that coprojection, so the transported R-map has spectrum followed by i equal to the
chosen structural morphism. The assertion includes the field case; the triple colimit
has a field quotient, so it is nonzero even when a chart ring has zero divisors. - /
theorem strictHenselization_chart_maximalIdeal
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    ∃ (_ : IsLocalRing (strictHenselizationRing (xR ≫ i)))
      (ρ : R ⟶ strictHenselizationRing (xR ≫ i)),
      Spec.map ρ ≫ i = strictHenselizationStructuralMap (xR ≫ i) ∧
      IsLocalRing.maximalIdeal (strictHenselizationRing (xR ≫ i)) =
        (xR (IsLocalRing.closedPoint Ω)).asIdeal.map ρ.hom  := by
  sorry
-/

end AlgebraicGeometry.Scheme
