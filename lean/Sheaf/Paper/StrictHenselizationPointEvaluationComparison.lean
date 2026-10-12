/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples

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
  obtain ⟨_, hinitial, _, _, E, δ, hδ, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩,
      r, t, _, ht⟩ := etale_local_ring_triples Y Ω A i xU
  let Nall := (pointSmallEtale x).fiber.Elements
  let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
  let Q : ObjectProperty P.FullSubcategory := fun n ↦
    ∃ g : n.obj.1.left ⟶ Spec A, g ≫ i = n.obj.1.hom
  let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale x).fiber ⋙
    Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
  let : HasColimit D := ⟨⟨cn, hcn⟩⟩
  let incl := strictHenselizationAffineInclusion x
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence x
  let rep := (equivSmallModel.{v} (strictHenselizationNeighbourhoods x)).inverse
  let q := (rep ⋙ incl).op
  let cmp : strictHenselizationRing x ≅ cn.pt :=
    Functor.Final.colimitIso q D ≪≫ colimit.isoColimitCocone ⟨cn, hcn⟩
  let k := hct.coconePointUniqueUpToIso hc
  let ringIso : strictHenselizationRing x ≅ c.pt := cmp ≪≫ t ≪≫ k
  let ev : Cocone D := {
    pt := .of Ω
    ι := {
      app := fun n ↦ n.unop.obj.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom
      naturality := by
        intro n m f
        have h := congrArg Over.Hom.left f.unop.hom.property
        change m.unop.obj.2.left ≫ f.unop.hom.1.left = n.unop.obj.2.left at h
        change f.unop.hom.1.left.appTop ≫
          m.unop.obj.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom = _
        rw [← Category.assoc, ← Hom.comp_appTop, h]
        simp } }
  let m := hcn.desc ev
  have hcmp (j) : colimit.ι (strictHenselizationDiagram x) j ≫ cmp.hom =
      cn.ι.app (q.obj j) := by
    change colimit.ι (q ⋙ D) j ≫
      ((Functor.Final.colimitIso q D).hom ≫
        (colimit.isoColimitCocone ⟨cn, hcn⟩).hom) = _
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact colimit.isoColimitCocone_ι_hom ⟨cn, hcn⟩ (q.obj j)
  have hsmall : cmp.hom ≫ m = CommRingCat.ofHom
      (strictHenselizationPointEvaluation x) := by
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc, hcmp, hcn.fac ev]
    exact (colimit.ι_desc (strictHenselizationPointCocone x) j).symm
  let := hinitial
  have hchart : t.hom ≫ k.hom ≫ CommRingCat.ofHom ψ ≫
      CommRingCat.ofHom K.subtype = m := by
    apply ((Functor.Final.isColimitWhiskerEquiv Q.ι.op cn).symm hcn).hom_ext
    intro d
    change cn.ι.app (Q.ι.op.obj d) ≫ _ = cn.ι.app (Q.ι.op.obj d) ≫ m
    have hleg : cn.ι.app (Q.ι.op.obj d) ≫ t.hom ≫ k.hom =
        δ.hom.app d ≫ c.ι.app (E.functor.obj d) := by
      calc
        _ = (δ.hom.app d ≫ ct.ι.app (E.functor.obj d)) ≫ k.hom :=
          congrArg (fun f ↦ f ≫ k.hom) (ht d)
        _ = _ := by
          simp only [Category.assoc, k, IsColimit.comp_coconePointUniqueUpToIso_hom]
    rw [← Category.assoc _ t.hom, ← Category.assoc _ k.hom,
      Category.assoc (cn.ι.app _) t.hom k.hom, hleg]
    rw [hcn.fac ev]
    have hres : c.ι.app (E.functor.obj d) ≫ CommRingCat.ofHom ψ =
        (ΓSpecIso (E.functor.obj d).B).inv ≫
          (Spec (E.functor.obj d).B).Γevaluation (E.functor.obj d).q ≫
          (E.functor.obj d).φ := by
      apply CommRingCat.hom_ext
      exact hψ _
    simp only [Category.assoc]
    rw [← Category.assoc (c.ι.app _) (CommRingCat.ofHom ψ), hres]
    change δ.hom.app d ≫
      ((ΓSpecIso (E.functor.obj d).B).inv ≫
        (Spec (E.functor.obj d).B).Γevaluation (E.functor.obj d).q ≫
        (E.functor.obj d).φ) ≫ CommRingCat.ofHom K.subtype =
      d.unop.obj.obj.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom
    apply Spec.map_injective
    simp only [Spec.map_comp, Category.assoc]
    have hpoint := (hδ d.unop).2
    have hnat := Scheme.toSpecΓ_naturality d.unop.obj.obj.2.left
    change d.unop.obj.obj.2.left ≫ d.unop.obj.obj.1.left.toSpecΓ =
      (Spec (.of Ω)).toSpecΓ ≫ Spec.map d.unop.obj.obj.2.left.appTop at hnat
    rw [← SpecMap_ΓSpecIso_hom] at hnat
    simpa only [Spec.map_comp, Category.assoc] using hpoint.symm.trans hnat
  refine ⟨ringIso, ?_⟩
  have hmap : ringIso.hom ≫ CommRingCat.ofHom ψ ≫ CommRingCat.ofHom K.subtype =
      CommRingCat.ofHom (strictHenselizationPointEvaluation x) := by
    change cmp.hom ≫ t.hom ≫ k.hom ≫ CommRingCat.ofHom ψ ≫
      CommRingCat.ofHom K.subtype = _
    rw [hchart, hsmall]
  intro a
  exact ConcreteCategory.congr_hom hmap a

end AlgebraicGeometry.Scheme
