/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples

/-! # Compatibility of the affine-chart colimit comparison

Source: Stacks Project, Tag 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The nested chart, triple and small-model diagram comparisons need extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The coordinate-ring colimit comparison preserves geometric evaluation.
Source: Stacks Project, Tag 04HX, and `etale_local_ring_triples`.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-comparison)

Proof: the ring-written affine pointed neighbourhoods are equivalent to the full
subcategory of affine pointed neighbourhoods, by
`strictHenselizationAffineInclusion_isEquivalence`. Compose this with the small-model
equivalence. Restrict to neighbourhoods over the chosen chart; the inclusion is
initial by `etale_local_ring_triples`, and its opposite is final. That theorem's
natural diagram isomorphism then identifies the ring diagram with the residue-triple
diagram. Transport the colimit along these functors and identify the resulting
colimit cocone with `c` using `hc`. All comparison maps commute with coprojections.
On a neighbourhood over the chart, the pointed embedding equation in
`etale_local_ring_triples`, after applying global sections and the affine spectrum
adjunction, identifies evaluation into Ω with the triple residue map followed by
inclusion into Ω. The hypothesis `hψ` identifies that map with ψ on each
coprojection. These equations therefore agree on the chart-neighbourhood diagram.
Finality extends equality to its whole colimit; the small-model and affine
comparisons give the displayed equality for every element of the chosen colimit.
This comparison does not assert or assume surjectivity of ψ. - /
theorem strictHenselizationPointEvaluation_comparison
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let emb := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := emb.hom.toAlgebra
    let K := separableClosure F Ω
    ∀ (c : Cocone (etaleResidueTriplesRingDiagram A p K
        (CommRingCat.ofHom (algebraMap F K)))) (_hc : IsColimit c)
      (ψ : c.pt →+* K),
      (∀ t, ψ.comp (c.ι.app t).hom =
        ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) →
      ∃ e : strictHenselizationRing (xU ≫ i) ≅ c.pt,
        ∀ a, (ψ (e.hom a) : Ω) = strictHenselizationPointEvaluation (xU ≫ i) a := by
  sorry
-/

end AlgebraicGeometry.Scheme
