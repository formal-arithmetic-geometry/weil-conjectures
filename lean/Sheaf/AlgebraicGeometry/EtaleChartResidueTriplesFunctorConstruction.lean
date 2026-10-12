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
# Construction of the compatible affine chart functor

Source: Stacks Project, proof of Tag 04HX and Remark Tag 04HT
(blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, proof of Tag 04HX (lemma-describe-etale-local-ring),
first paragraph, and Tag 04HT (remark-etale-neighbourhoods).
(blueprint: lem-weil-pbc-etale-chart-functor-construction).

Proof: For c = (V, v) choose the chart map g. It is unique because i is a monomorphism.
Put B = Γ(V) and α = (ΓSpecIso A).inv followed by g.appTop. The affine isomorphism
V ≅ Spec B identifies Spec α with g; cancellation of the étale open immersion i
shows that g, hence Spec α, is étale. Transport v along V → Spec Γ(V), obtain its
prime q and residue embedding into Ω, and restrict that embedding to K using the
assumed image containment. Cancellation of i in v followed by the structure map
shows that q lies over p and gives the required compatibility on A. This constructs
the triple H(c); its underlying ring is Γ(V). On a reversed neighbourhood morphism
use the map on global sections. Commutation with the structure maps gives A-linearity.
Commutation with the points gives commutation of the maps to Ω; injectivity of K → Ω
gives commutation of the maps to K. These are exactly the morphisms of triples.
Functoriality follows from functoriality of global sections. The identity maps on
Γ(V) give the natural isomorphism δ, the definition of α gives the first formula,
and the residue-field factorization of the transported point gives the second.
This statement constructs only a functor, without claiming fullness or surjectivity. -/
theorem etale_chart_residue_triples_functor_construction
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
    (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) →
      ∃ (H : NUᵒᵖ ⥤ T) (δ : DU ≅ H ⋙ DT),
        (∀ c : NU,
          let t := H.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) := by sorry

end AlgebraicGeometry.Scheme
