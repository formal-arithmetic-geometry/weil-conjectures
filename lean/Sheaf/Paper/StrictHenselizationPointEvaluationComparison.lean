/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Sheaf.Paper.StrictHenselizationPointEvaluationPointed

/-! # Compatibility of the affine-chart colimit comparison

Source: Stacks Project, Tag 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem pointed_ring_equation
    {Ω : Type v} [Field Ω] {X : Scheme.{v}} {B C : CommRingCat.{v}}
    (f : Spec (.of Ω) ⟶ X) (d : Γ(X, ⊤) ⟶ B)
    (b : B ⟶ C) (k : C ⟶ CommRingCat.of Ω)
    (h : f ≫ X.toSpecΓ = Spec.map k ≫ Spec.map b ≫ Spec.map d) :
    d ≫ b ≫ k = f.appTop ≫ (ΓSpecIso (.of Ω)).hom := by
  apply Spec.map_injective
  simp only [Spec.map_comp, Category.assoc]
  rw [SpecMap_ΓSpecIso_hom]
  exact h.symm.trans (Scheme.toSpecΓ_naturality f)

set_option backward.isDefEq.respectTransparency false in
private theorem pointEvaluation_leg {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods x)) :
    colimit.ι (strictHenselizationAffineDiagram x) (op j) ≫
      CommRingCat.ofHom (strictHenselizationPointEvaluation x) =
      ((equivSmallModel.{v} (strictHenselizationNeighbourhoods x)).inverse.obj j).2.left.appTop ≫
        (ΓSpecIso (.of Ω)).hom := by
  let N := (equivSmallModel.{v} (strictHenselizationNeighbourhoods x)).inverse
  have hp := strictHenselizationPointEvaluation_pointed x j
  dsimp [strictHenselizationCone] at hp
  apply pointed_ring_equation ((N.obj j).2.left)
    (colimit.ι (strictHenselizationAffineDiagram x) (op j))
    (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) (𝟙 _)
  simp only [Spec.map_id, Category.id_comp]
  have hh := congrArg (fun f ↦ f ≫ (Spec (N.obj j).1.left.unop).isoSpec.hom) hp
  dsimp only [N] at hh
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  change (N.obj j).2.left ≫ (Spec (N.obj j).1.left.unop).isoSpec.hom = _
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem pointEvaluation_eq_upstream
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Y) :
    CommRingCat.ofHom (strictHenselizationPointEvaluation x) =
      (smallStrictHenselizationColimitIso x).hom ≫ strictHenselizationEval x := by
  let : HasColimit (strictHenselizationDiagram x) := inferInstance
  apply colimit.hom_ext
  intro j
  rw [pointEvaluation_leg x j.unop]
  let F := (equivSmallModel (strictHenselizationNeighbourhoods x)).inverse ⋙
    strictHenselizationAffineInclusion x
  let : (strictHenselizationAffineInclusion x).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence x
  change _ = colimit.ι (F.op ⋙ strictHenselizationDiagram x) j ≫
    (Functor.Final.colimitIso F.op (strictHenselizationDiagram x)).hom ≫ _
  rw [Functor.Final.ι_colimitIso_hom_assoc]
  conv_rhs => erw [ι_strictHenselizationEval x (F.obj j.unop)]
  rfl

set_option maxHeartbeats 800000 in
-- The nested chart, triple and small-model diagram comparisons need extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate-ring colimit comparison preserves geometric evaluation.
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
This comparison does not assert or assume surjectivity of ψ. -/
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
  classical
  dsimp only
  intro c hc ψ hψ
  let x := xU ≫ i
  let p := (SpecToEquivOfField Ω (Spec A) xU).1
  let F := (Spec A).residueField p
  let emb := (SpecToEquivOfField Ω (Spec A) xU).2
  let : Algebra F Ω := emb.hom.toAlgebra
  let K := separableClosure F Ω
  let P : ObjectProperty (pointSmallEtale x).fiber.Elements :=
    fun n ↦ IsAffine n.1.left
  let Q : ObjectProperty P.FullSubcategory :=
    fun n ↦ ∃ g : n.obj.1.left ⟶ Spec A, g ≫ i = n.obj.1.hom
  obtain ⟨hN, hQ, href, hres, E, δ, hpoint, cn, cu, ct,
    ⟨hcn⟩, ⟨hcu⟩, ⟨hct⟩, r, s, hr, hs⟩ :=
    etale_local_ring_triples Y Ω A i xU
  let e₀ : strictHenselizationRing x ≅ strictHenselization x :=
    smallStrictHenselizationColimitIso x
  let e₁ : strictHenselization x ≅ cn.pt :=
    (colimit.isColimit (strictHenselizationDiagram x)).coconePointUniqueUpToIso hcn
  let e₂ := hct.coconePointUniqueUpToIso hc
  let e := e₀ ≪≫ e₁ ≪≫ s ≪≫ e₂
  refine ⟨e, ?_⟩
  have hev₁ : e₁.hom ≫ s.hom ≫ e₂.hom ≫ CommRingCat.ofHom ψ ≫
        CommRingCat.ofHom K.subtype = strictHenselizationEval x := by
    have : Q.ι.Initial := hQ
    have hcol := (Functor.Final.isColimitWhiskerEquiv Q.ι.op
      (colimit.cocone (strictHenselizationDiagram x))).symm
        (colimit.isColimit (strictHenselizationDiagram x))
    apply hcol.hom_ext
    intro j
    change colimit.ι (strictHenselizationDiagram x) (Q.ι.op.obj j) ≫
        e₁.hom ≫ s.hom ≫ e₂.hom ≫ CommRingCat.ofHom ψ ≫
          CommRingCat.ofHom K.subtype =
      colimit.ι (strictHenselizationDiagram x) (Q.ι.op.obj j) ≫
        strictHenselizationEval x
    rw [colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    rw [← Category.assoc (cn.ι.app _) s.hom, hs j]
    simp only [Category.assoc]
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    have hψ' : c.ι.app (E.functor.obj j) ≫ CommRingCat.ofHom ψ =
        (ΓSpecIso (E.functor.obj j).B).inv ≫
          (Spec (E.functor.obj j).B).Γevaluation (E.functor.obj j).q ≫
            (E.functor.obj j).φ := by
      exact congrArg CommRingCat.ofHom (hψ (E.functor.obj j))
    rw [← Category.assoc (c.ι.app _) (CommRingCat.ofHom ψ), hψ']
    conv_rhs => erw [ι_strictHenselizationEval x j.unop.obj]
    exact pointed_ring_equation j.unop.obj.obj.2.left (δ.hom.app j)
      ((ΓSpecIso (E.functor.obj j).B).inv ≫
        (Spec (E.functor.obj j).B).Γevaluation (E.functor.obj j).q ≫
          (E.functor.obj j).φ) (CommRingCat.ofHom K.subtype) (hpoint j.unop).2
  have hev : e.hom ≫ CommRingCat.ofHom ψ ≫ CommRingCat.ofHom K.subtype =
      CommRingCat.ofHom (strictHenselizationPointEvaluation x) := by
    change e₀.hom ≫ e₁.hom ≫ s.hom ≫ e₂.hom ≫
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom K.subtype = _
    rw [hev₁]
    exact (pointEvaluation_eq_upstream x).symm
  intro a
  have hh := congrArg CommRingCat.Hom.hom hev
  exact congrArg (fun f ↦ f a) hh

end AlgebraicGeometry.Scheme
