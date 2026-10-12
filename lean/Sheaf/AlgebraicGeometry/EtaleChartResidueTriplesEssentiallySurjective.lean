/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Sheaf.AlgebraicGeometry.EtaleResidueTriples

/-!
# Essential surjectivity of the compatible affine chart functor

Source: Stacks Project, proof of Tag 04HX and Remark Tag 04HT
(blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, proof of Tag 04HX (lemma-describe-etale-local-ring),
translation of pointed affine neighbourhoods into triples, and Tag 04HT
(remark-etale-neighbourhoods).
(blueprint: lem-weil-pbc-etale-chart-essentially-surjective).

Proof: Given a triple t, form V = Spec t.B, with structure map Spec t.α followed by i
and point the spectrum map of B → κ(t.q) → K → Ω. Its structure map is étale by
composition, and the compatibility equation of t makes its point lie over xU ≫ i.
It is affine and factors through the chart, so it defines c in NU. The component δ_c,
followed backwards by ΓSpecIso, identifies the ring of H(c) with B. The first formula
shows that this ring isomorphism commutes with the maps from A. The second formula,
after cancelling the injective inclusion K → Ω using full faithfulness of Spec,
shows that it also commutes with the maps to K. It and its inverse therefore define
an isomorphism of triples between H(op c) and t. This proves essential surjectivity;
no arbitrary equivalence of indexing categories is used. -/
theorem etale_chart_residue_triples_essentially_surjective
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    ∀ (H : NUᵒᵖ ⥤ T) (δ : DU ≅ H ⋙ DT),
        (∀ c : NU,
          let t := H.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) → H.EssSurj := by sorry

end AlgebraicGeometry.Scheme
