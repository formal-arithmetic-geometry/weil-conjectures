/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.CategoryTheory.RingedSitePerfectEvaluationModel
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Yoneda

/-! # RingedSitePerfectBidualModel

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-perfect-bidual-model).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory

private theorem evaluation_slide {D : Type*} [Category D] [MonoidalCategory D]
    (P V : D) (e : V ⊗ P ⟶ 𝟙_ D) (η : 𝟙_ D ⟶ P ⊗ V) :
    ((ρ_ V).inv ≫ (𝟙 V ⊗ₘ η) ≫ (α_ V P V).inv ≫
      (e ⊗ₘ 𝟙 V) ≫ (λ_ V).hom) ▷ P ≫ e =
    V ◁ ((λ_ P).inv ≫ (η ⊗ₘ 𝟙 P) ≫ (α_ P V P).hom ≫
      (𝟙 P ⊗ₘ e) ≫ (ρ_ P).hom) ≫ e := by
  calc
    _ = 𝟙 (V ⊗ P) ⊗≫ (V ◁ η) ▷ P ⊗≫
        (e ▷ (V ⊗ P) ≫ (𝟙_ D) ◁ e) ≫ (λ_ (𝟙_ D)).hom := by monoidal
    _ = 𝟙 (V ⊗ P) ⊗≫ (V ◁ η) ▷ P ⊗≫
        ((V ⊗ P) ◁ e ≫ e ▷ (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom := by
      rw [whisker_exchange]
    _ = _ := by monoidal

private theorem pairing_of_evaluation
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (O : D) (u : S.monoidal.tensorUnit ≅ O) (P : D)
    (h : ∀ N, IsIso (ringedSiteDualEvaluation S O u P N)) :
    ∃ t : @ExactPairing D _ S.monoidal P (H.obj (op P, O)),
      t.evaluation' = S.evaluation P O ≫ u.inv := by
  let := S.monoidal
  let V := H.obj (op P, O)
  let e : V ⊗ P ⟶ 𝟙_ D := S.evaluation P O ≫ u.inv
  let φ := ringedSiteDualEvaluation S O u P
  have hφ (N : D) : IsIso (φ N) := h N
  let η : 𝟙_ D ⟶ P ⊗ V :=
    S.transpose _ P P (λ_ P).hom ≫ inv (φ P)
  have hη : η ≫ φ P = S.transpose _ P P (λ_ P).hom := by
    dsimp only [η]
    simp
  have hnat {A B Q : D} (a : A ⟶ B) (f : B ⟶ H.obj (op P, Q)) :
      (S.transpose A P Q).symm (a ≫ f) =
        (a ⊗ₘ 𝟙 P) ≫ (S.transpose B P Q).symm f :=
    by
      rw [tensorHom_id]
      exact (S.adjunction P).homEquiv_naturality_left_symm a f
  have hdef (N : D) :
      φ N = S.transpose _ P N ((α_ N V P).hom ≫ (𝟙 N ⊗ₘ e) ≫ (ρ_ N).hom) := by
    change S.transpose _ P N ((α_ N V P).hom ≫
      (𝟙 N ⊗ₘ S.evaluation P O) ≫ (𝟙 N ⊗ₘ u.inv) ≫ (ρ_ N).hom) = _
    dsimp only [e]
    simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
  have hfirst : (λ_ P).hom =
      (η ⊗ₘ 𝟙 P) ≫ (α_ P V P).hom ≫ (𝟙 P ⊗ₘ e) ≫ (ρ_ P).hom := by
    have hh := congrArg (S.transpose _ P P).symm hη
    rw [Equiv.symm_apply_apply, hnat, hdef, Equiv.symm_apply_apply] at hh
    exact hh.symm
  have hP : (λ_ P).inv ≫ (η ⊗ₘ 𝟙 P) ≫ (α_ P V P).hom ≫
      (𝟙 P ⊗ₘ e) ≫ (ρ_ P).hom = 𝟙 P := by
    rw [← hfirst, Iso.inv_hom_id]
  let g := (ρ_ V).inv ≫ (𝟙 V ⊗ₘ η) ≫ (α_ V P V).inv ≫
    (e ⊗ₘ 𝟙 V) ≫ (λ_ V).hom
  have hg : (g ⊗ₘ 𝟙 P) ≫ e = e := by
    rw [tensorHom_id]
    dsimp only [g]
    rw [evaluation_slide, hP]
    simp
  let t := (λ_ V).inv ≫ φ (𝟙_ D)
  have ht : (S.transpose _ P (𝟙_ D)).symm t = e := by
    dsimp only [t]
    rw [hnat, hdef, Equiv.symm_apply_apply]
    monoidal
  have hgt : g ≫ t = t := by
    apply (S.transpose _ P (𝟙_ D)).symm.injective
    rw [hnat, ht, hg]
  have : IsIso t := by dsimp only [t]; infer_instance
  have hgid : g = 𝟙 V := by
    apply (cancel_mono t).1
    simpa only [Category.id_comp] using hgt
  refine ⟨{
    coevaluation' := η
    evaluation' := e
    coevaluation_evaluation' := ?_
    evaluation_coevaluation' := ?_ }, rfl⟩
  · have hh := hgid
    dsimp only [g] at hh
    apply (cancel_epi (ρ_ V).inv).1
    apply (cancel_mono (λ_ V).hom).1
    simpa only [V, id_tensorHom, tensorHom_id, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh
  · apply (cancel_epi (λ_ P).inv).1
    apply (cancel_mono (ρ_ P).hom).1
    simpa only [V, id_tensorHom, tensorHom_id, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hP

private theorem bidual_of_evaluation
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (s : @SymmetricCategory D _ S.monoidal)
    (O : D) (u : S.monoidal.tensorUnit ≅ O) (P : D)
    (h : ∀ N, IsIso (ringedSiteDualEvaluation S O u P N)) :
    IsIso (ringedSiteBidual S s O P) := by
  let := S.monoidal
  let := s
  let V := H.obj (op P, O)
  obtain ⟨t, ht⟩ := pairing_of_evaluation S O u P h
  let : ExactPairing P V := t
  let : ExactPairing V P := BraidedCategory.exactPairing_swap P V
  apply isIso_of_yoneda_map_bijective
  intro A
  let q : (A ⟶ H.obj (op V, O)) ≃ (A ⊗ V ⟶ 𝟙_ D) :=
    (S.transpose A V O).symm.trans (Iso.homCongr (Iso.refl (A ⊗ V)) u.symm)
  let k : (A ⟶ P) ≃ (A ⊗ V ⟶ 𝟙_ D) :=
    (Iso.homCongr (Iso.refl _) (λ_ P).symm).trans
      (tensorRightHomEquiv A V P (𝟙_ D)).symm
  have hev : ExactPairing.evaluation V P =
      (s.braiding P V).hom ≫ S.evaluation P O ≫ u.inv := by
    change (s.braiding P V).hom ≫ t.evaluation' = _
    rw [ht]
  have hk (f : A ⟶ P) : k f =
      (f ⊗ₘ 𝟙 V) ≫ (s.braiding P V).hom ≫ S.evaluation P O ≫ u.inv := by
    change ((𝟙 A ≫ f ≫ (λ_ P).inv) ▷ V) ≫ (α_ (𝟙_ D) P V).hom ≫
      (𝟙_ D) ◁ ExactPairing.evaluation V P ≫ (ρ_ (𝟙_ D)).hom = _
    rw [hev]
    monoidal
  have hh (f : A ⟶ P) : q (f ≫ ringedSiteBidual S s O P) = k f := by
    dsimp only [q, Iso.homCongr, Equiv.trans_apply]
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    rw [show (S.transpose A V O).symm (f ≫ ringedSiteBidual S s O P) =
      (f ⊗ₘ 𝟙 V) ≫ (S.transpose P V O).symm (ringedSiteBidual S s O P) from
        by
          rw [tensorHom_id]
          exact (S.adjunction V).homEquiv_naturality_left_symm f
            (ringedSiteBidual S s O P)]
    rw [ringedSiteBidual, Equiv.symm_apply_apply, hk]
    change ((f ⊗ₘ 𝟙 V) ≫ (s.braiding P V).hom ≫ S.evaluation P O) ≫ u.inv = _
    simp only [Category.assoc]
  have heq : (fun f ↦ f ≫ ringedSiteBidual S s O P) = ⇑(k.trans q.symm) := by
    funext f
    apply q.injective
    rw [hh]
    exact (q.apply_symm_apply (k f)).symm
  rw [heq]
  exact (k.trans q.symm).bijective

/-- Canonical biduality for the localization of a locally strictly perfect complex.
Source: Stacks Project, sites-cohomology.tex, Tag 08JJ; categorical duality via
Mathlib.CategoryTheory.Monoidal.Rigid.Basic and Rigid.Braided.
Proof: apply the canonical evaluation-model theorem for every target N. For
V=RHom(QK,O), the inverse of evaluation at QK takes the transpose of the left
unitor to a coevaluation O to QK tensor V. Transposing its defining equation
gives the first triangle identity. Slide this triangle through evaluation to
show that the other triangle endomorphism g of V satisfies g followed by the
isomorphism V to RHom(QK,O) equals that same isomorphism; cancellation gives the
second triangle identity. Thus QK,V is an exact pairing with evaluation equal
to the specified closed evaluation followed by the unit isomorphism inverse.
Mathlib swaps this pairing using the braiding. For every A its tensor-Hom
equivalence identifies maps A to QK with maps A tensor V to O. The closed Hom
adjunction gives the same latter maps from maps A to RHom(V,O). Under these
bijections postcomposition with the canonical bidual map is the identity:
this follows by transposing its definition and applying the formula for the
swapped evaluation. Consequently every Yoneda map is bijective, and the
canonical bidual map is an isomorphism. No second local signed calculation
or additional descent argument is required.
(blueprint: lem-sfb-perfect-bidual-model). -/
theorem ringedSitePerfectBidual_model
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (K : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hK : SheafOfModules.IsLocallyStrictPerfectComplexOfUniverses.{c, v, r} R K)
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    : IsIso (ringedSiteBidual M.closed M.symmetric
      (ringedSiteDualityUnit.{c, v, r, w} J R) (DerivedCategory.Q.obj K)) := by
  apply bidual_of_evaluation M.closed M.symmetric _ M.unitIso
  exact fun N ↦ ringedSitePerfectEvaluation_model J R K hK M N

end CategoryTheory
