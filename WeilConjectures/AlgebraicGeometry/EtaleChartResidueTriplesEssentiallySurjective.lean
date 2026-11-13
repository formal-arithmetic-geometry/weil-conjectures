/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-!
# Essential surjectivity of the compatible affine chart functor

Source: Stacks Project, proof of Tag 04HX and Remark Tag 04HT.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem fromSpecResidueField_toSpecΓ (X : Scheme.{v}) (q : X) :
    X.fromSpecResidueField q ≫ X.toSpecΓ = Spec.map (X.Γevaluation q) := by
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

private theorem residueTriple_iso {A : CommRingCat.{v}} {p : Spec A}
    {K : Type v} [Field K] {χ : (Spec A).residueField p ⟶ CommRingCat.of K}
    (s t : EtaleResidueTriples A p K χ) (e : s.B ≅ t.B)
    (hA : s.α ≫ e.hom = t.α)
    (hK : e.hom ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) :
    Nonempty (s ≅ t) := by
  refine ⟨InducedCategory.isoMk (Under.isoMk (Over.isoMk e hK) ?_)⟩
  apply Over.OverMorphism.ext
  exact hA

/-- Source: Stacks Project, proof of Tag 04HX,
translation of pointed affine neighbourhoods into triples, and Tag 04HT. -/
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
    let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
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
              Spec.map (δ.hom.app (op c))) → H.EssSurj := by
  intro x p F e K χ Nall P N Q NU D DU T DT H δ hδ
  refine ⟨fun t ↦ ?_⟩
  let ψ : t.B ⟶ CommRingCat.of K :=
    (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
  let j : CommRingCat.of K ⟶ CommRingCat.of Ω := CommRingCat.ofHom K.subtype
  let y : Spec (.of Ω) ⟶ Spec t.B := Spec.map j ≫ Spec.map ψ
  have hχ : χ ≫ j = e := by
    ext a
    rfl
  have hxU : Spec.map e ≫ (Spec A).fromSpecResidueField p = xU :=
    (SpecToEquivOfField Ω (Spec A)).symm_apply_apply xU
  have hy : y ≫ Spec.map t.α = xU := by
    have hc : t.α ≫ ψ ≫ j =
        (ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ e := by
      calc
        t.α ≫ ψ ≫ j = (t.α ≫ ψ) ≫ j := (Category.assoc _ _ _).symm
        _ = ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ χ) ≫ j :=
          congrArg (fun f ↦ f ≫ j) t.compatible
        _ = _ := by rw [Category.assoc, Category.assoc, hχ]
    apply (cancel_mono (Spec A).toSpecΓ).mp
    calc
      (y ≫ Spec.map t.α) ≫ (Spec A).toSpecΓ =
          Spec.map (t.α ≫ ψ ≫ j) ≫ (Spec A).toSpecΓ := by
        simp only [y, Spec.map_comp, Category.assoc]
      _ = Spec.map ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ e) ≫
          (Spec A).toSpecΓ := congrArg (fun f ↦ Spec.map f ≫ (Spec A).toSpecΓ) hc
      _ = (Spec.map e ≫ (Spec A).fromSpecResidueField p) ≫
          (Spec A).toSpecΓ := by
        simp only [Spec.map_comp, Category.assoc, SpecMap_ΓSpecIso_inv_toSpecΓ,
          Category.comp_id, fromSpecResidueField_toSpecΓ]
      _ = _ := congrArg (fun f ↦ f ≫ (Spec A).toSpecΓ) hxU
  have : Etale (Spec.map t.α) := t.etale
  let c0 : Nall := Functor.elementsMk _ (Etale.mk (Spec.map t.α ≫ i)) (Over.homMk y (by
    dsimp [y] at hy ⊢
    rw [← Category.assoc, hy]))
  let c : NU := ⟨⟨c0, inferInstanceAs (IsAffine (Spec t.B))⟩,
    ⟨Spec.map t.α, rfl⟩⟩
  let r : t.B ≅ (H.obj (op c)).B := (ΓSpecIso t.B).symm ≪≫ δ.app (op c)
  have hrA : t.α ≫ r.hom = (H.obj (op c)).α := by
    have h := (hδ c).1 (Spec.map t.α) rfl
    dsimp [r]
    calc
      t.α ≫ (ΓSpecIso t.B).inv ≫ δ.hom.app (op c) =
          (ΓSpecIso A).inv ≫ (Spec.map t.α).appTop ≫ δ.hom.app (op c) :=
        congrArg (fun f ↦ f ≫ δ.hom.app (op c))
          (ΓSpecIso_inv_naturality t.α)
      _ = _ := h
  have hrK : r.hom ≫ (ΓSpecIso (H.obj (op c)).B).inv ≫
      (Spec (H.obj (op c)).B).Γevaluation (H.obj (op c)).q ≫ (H.obj (op c)).φ = ψ := by
    have h := (hδ c).2
    change y ≫ (Spec t.B).toSpecΓ = _ at h
    dsimp [r]
    have heq : (r.hom ≫ (ΓSpecIso (H.obj (op c)).B).inv ≫
        (Spec (H.obj (op c)).B).Γevaluation (H.obj (op c)).q ≫
        (H.obj (op c)).φ) ≫ j = ψ ≫ j := by
      apply Spec.map_injective
      simp only [Spec.map_comp, Category.assoc]
      calc
        _ = (y ≫ (Spec t.B).toSpecΓ) ≫ Spec.map (ΓSpecIso t.B).inv := by
          simpa only [Category.assoc, r, j, Iso.trans_hom, Iso.symm_hom,
            Iso.app_hom, Spec.map_comp] using
            congrArg (fun f ↦ f ≫ Spec.map (ΓSpecIso t.B).inv) h.symm
        _ = _ := by
          simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, y]
    ext a
    exact ConcreteCategory.congr_hom heq a
  exact ⟨op c, (residueTriple_iso t (H.obj (op c)) r hrA hrK).map Iso.symm⟩

end AlgebraicGeometry.Scheme

