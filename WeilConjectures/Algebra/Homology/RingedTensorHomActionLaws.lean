/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorHomActionDefinitions
import all WeilConjectures.Algebra.Homology.RingedHomTargetShiftEvaluation
import WeilConjectures.Mathlib.Algebra.Homology.MonoidalShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Algebra.Homology.Monoidal.BraidingShift
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
import all WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.Algebra.Homology.RingedTensorConstraintCompletion

/-! # A step in the exactness of the ringed tensor-Hom action -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a b c v u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite WeilConjectures
open CategoryTheory.MonoidalCategory SheafOfModules RingedHomTargetShift

namespace CategoryTheory

attribute [local implicit_reducible] CoefficientClosedStructure.tensor Prod.sectR
  coefficientTotalTensor RingedHomTargetShift.totalShift
  RingedDerivedTensorComparison Functor.map₂HomologicalComplex Iso.prod
  TensorFlatRepresentative

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

private abbrev ActionD := DerivedCategory (RingedTensorModules.{c, v, u} J R)
private abbrev ActionComplex := RingedHomUniverses.Complex.{c, v, u} J R

set_option maxHeartbeats 2000000 in
-- Nested derived tensor comparisons need additional elaboration heartbeats.
private theorem actionTensorComparison
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    ∃ e : siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R ≅ S.tensor,
      ∀ (A B : ActionComplex.{c, v, u} J R)
        (hA : TensorFlatRepresentative (J := J) (R := R) A)
        (hB : TensorFlatRepresentative (J := J) (R := R) B),
        (tensorDescentPair (J := J) (R := R) A B hA hB).hom ≫
          e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
            (hc.tensorIso A B (Or.inl hA.1)).hom := by
  let PC := flatProperty.{c, v, u} J R
  let P := tensorDescentClass.{c, v, max c v u, w} (R := R)
  let d := site_derived_tensor_descent_independentCoefficients.{c, v, max c v u, w, 0, 0} J R
  let L := (PC.ι ⋙ DerivedCategory.Q).prod (PC.ι ⋙ DerivedCategory.Q)
  let U := siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R
  let ff := flatPairWhiskering PC P d.choose_spec.1 (resolvingLocalization.{c, v, u, w} J R)
    (ActionD.{c, v, u, w} J R)
  let I : PC.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)) :=
    ObjectProperty.lift _ PC.ι (fun X ↦ X.property.1)
  let e₀ : L ⋙ U ≅ L ⋙ S.tensor :=
    (publishedComparison.{c, v, u, w} J R).symm ≪≫ Functor.isoWhiskerLeft (I.prod I) T.comparison
  let e : U ≅ S.tensor := ff.preimageIso e₀
  refine ⟨e, ?_⟩
  intro A B hA hB
  have hh := congr_app (ff.map_preimage e₀.hom) (⟨A, hA⟩, ⟨B, hB⟩)
  change e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
    e₀.hom.app (⟨A, hA⟩, ⟨B, hB⟩) at hh
  dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at hh
  conv_rhs at hh =>
    arg 1
    rw [← Iso.app_inv, publishedComparison_app.{c, v, u, w} J R A B hA hB]
  have h : e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
      (tensorDescentPair (J := J) (R := R) A B hA hB).inv ≫
        (T.iso J R S A B hA.1 hB.1).hom := hh
  rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    hc.tensorIso_both A B hA.1 hB.1]

private theorem action_natTrans_ext
    {F G : ActionD.{c, v, u, w} J R ⥤ ActionD.{c, v, u, w} J R}
    (η θ : F ⟶ G)
    (h : ∀ (P : ActionComplex.{c, v, u} J R)
      (_ : TensorFlatRepresentative (J := J) (R := R) P),
      η.app (DerivedCategory.Q.obj P) = θ.app (DerivedCategory.Q.obj P)) : η = θ := by
  ext M
  obtain ⟨P, hP, ⟨e⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R M
  apply (cancel_epi (F.map e.hom)).mp
  rw [η.naturality, θ.naturality, h P hP]

set_option maxHeartbeats 2000000 in
-- Elaborating the recorded tensor and shift comparisons requires extra heartbeats.
private theorem action_representative_eq
    (P B : ActionComplex.{c, v, u} J R)
    (hP : TensorFlatRepresentative (J := J) (R := R) P)
    (hB : TensorFlatRepresentative (J := J) (R := R) B) :
    (KFlatFixedTensor.representativeIso R P B hP.1 hB.1 hP.2 hB.2).hom =
      (tensorDescentPair (J := J) (R := R) P B hP hB).hom := by
  let U := siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R
  let t := (KFlatFixedTensor.representativeIso R P B hP.1 hB.1 hP.2 hB.2).hom
  have h : (tensorDescentPair (J := J) (R := R) P B hP hB).hom =
      t ≫ U.map (𝟙 (DerivedCategory.Q.obj P, DerivedCategory.Q.obj B)) := by
    have qh (A : ActionComplex.{c, v, u} J R) :
        (DerivedCategory.quotientCompQhIso
          (RingedTensorModules.{c, v, u} J R)).hom.app A = 𝟙 _ := by rfl
    have qi (A : ActionComplex.{c, v, u} J R) :
        (DerivedCategory.quotientCompQhIso
          (RingedTensorModules.{c, v, u} J R)).inv.app A = 𝟙 _ := by rfl
    simp only [t, KFlatFixedTensor.representativeIso,
      KFlatFixedTensor.TensorPresentation.representativeIso, tensorDescentPair,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom,
      qh, qi, Category.id_comp]
    simp only [id, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_hom]
    simp only [Category.assoc]
    with_unfolding_all rfl
  exact ((congrArg (fun f ↦ t ≫ f) (U.map_id _)).trans (Category.comp_id t)).symm.trans h.symm

set_option maxHeartbeats 2000000 in
-- Nested derived tensor comparisons need additional elaboration heartbeats.
private theorem action_tensor_transport
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : ActionD.{c, v, u, w} J R, (tensorHomActionSource S V).CommShift ℤ)
    (hs : tensorHomActionShiftNormalization J R S T β hc s) :
    ∃ s₀ : (KFlatFixedTensor.derivedTensor R).CommShift₂Int,
      ∃ e : siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R ≅ S.tensor,
        letI := s₀
        let (V : ActionD.{c, v, u, w} J R) := s V
        let (V : ActionD.{c, v, u, w} J R) :
            ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
        (∀ V, (tensorHomActionSource S V).IsTriangulated ∧
          NatTrans.CommShift ((Functor.curry.mapIso e).app V).hom ℤ) ∧
        (∀ (P : ActionComplex.{c, v, u} J R)
          (hP : TensorFlatRepresentative (J := J) (R := R) P),
          ∃ cL : (KFlatFixedTensor.totalTensor R).obj P ⋙ DerivedCategory.Q ≅
              DerivedCategory.Q ⋙ (KFlatFixedTensor.derivedTensor R).obj
                (DerivedCategory.Q.obj P),
            NatTrans.CommShift cL.hom ℤ ∧
            ∀ (B : ActionComplex.{c, v, u} J R)
              (hB : TensorFlatRepresentative (J := J) (R := R) B),
              cL.hom.app B = (tensorDescentPair (J := J) (R := R) P B hP hB).hom) ∧
        ∀ (P B : ActionComplex.{c, v, u} J R)
          (hP : TensorFlatRepresentative (J := J) (R := R) P)
          (hB : TensorFlatRepresentative (J := J) (R := R) B),
          (tensorDescentPair (J := J) (R := R) P B hP hB).hom ≫
              e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj B) =
            (hc.tensorIso P B (Or.inl hP.1)).hom := by
  let (V : ActionD.{c, v, u, w} J R) := s V
  let (V : ActionD.{c, v, u, w} J R) :
      ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
  obtain ⟨e, he⟩ := actionTensorComparison.{c, v, u, w} J R S T β hc
  obtain ⟨s₀, ht⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s₀
  refine ⟨s₀, e, ?_, ?_, he⟩
  swap
  · intro P hP
    obtain ⟨cL, hcL, hnL⟩ := (ht P hP.1 hP.2).2.2.2.1
    refine ⟨cL, hcL, fun B hB ↦ ?_⟩
    change (cL.app B).hom = _
    rw [hnL B hB.1 hB.2]
    exact action_representative_eq.{c, v, u, w} J R P B hP hB
  intro V
  obtain ⟨P, hP, ⟨eP⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R V
  have htri := (ht P hP.1 hP.2).2.2.1.1
  let := htri
  obtain ⟨cL, hcL, hnL⟩ := (ht P hP.1 hP.2).2.2.2.1
  let := hcL
  let F := (KFlatFixedTensor.derivedTensor R).obj (DerivedCategory.Q.obj P)
  let G := tensorHomActionSource S V
  let d : F ≅ G :=
    (Functor.curry.mapIso e).app (DerivedCategory.Q.obj P) ≪≫
      (Functor.curry.obj S.tensor).mapIso eP
  have hcomp (B : ActionComplex.{c, v, u} J R) (hB : TensorFlatRepresentative (J := J) (R := R) B) :
      cL.hom.app B ≫ d.hom.app (DerivedCategory.Q.obj B) =
        (hc.tensorIso P B (Or.inl hP.1)).hom ≫
          S.tensor.map (Prod.mkHom eP.hom (𝟙 _)) := by
    rw [show cL.hom.app B =
      (tensorDescentPair (J := J) (R := R) P B hP hB).hom from
        by
          change (cL.app B).hom = _
          rw [hnL B hB.1 hB.2]
          exact action_representative_eq.{c, v, u, w} J R P B hP hB]
    change (tensorDescentPair (J := J) (R := R) P B hP hB).hom ≫
      (e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj B) ≫
        S.tensor.map (Prod.mkHom eP.hom (𝟙 _))) = _
    rw [← Category.assoc, he P B hP hB]
  have hd : NatTrans.CommShift d.hom ℤ := by
    constructor
    intro n
    apply action_natTrans_ext.{c, v, u, w} J R
    intro B hB
    have hBs := RingedHomTargetShift.flatShift.{c, v, u} J R B hB n
    have h := hs V P B hP.1 hB.1 eP n
    have hL := NatTrans.shift_app_comm cL.hom n B
    have hb := hcomp B hB
    have hbs := hcomp (B⟦n⟧) hBs
    change (F.commShiftIso n).hom.app (DerivedCategory.Q.obj B) ≫
      (d.hom.app (DerivedCategory.Q.obj B))⟦n⟧' =
        d.hom.app ((DerivedCategory.Q.obj B)⟦n⟧) ≫
          (G.commShiftIso n).hom.app (DerivedCategory.Q.obj B)
    apply (cancel_epi (cL.hom.app (B⟦n⟧) ≫
      F.map ((DerivedCategory.Q.commShiftIso n).hom.app B))).mp
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hL
    rw [← Category.assoc] at hL
    calc
      _ = (((KFlatFixedTensor.totalTensor R).obj P ⋙
          DerivedCategory.Q).commShiftIso n).hom.app B ≫
            (cL.hom.app B ≫ d.hom.app (DerivedCategory.Q.obj B))⟦n⟧' := by
        simp only [Functor.map_comp, Functor.commShiftIso_comp_hom_app, ← Category.assoc]
        rw [← hL]
      _ = _ := by
        have hp : S.tensor.map (Prod.mkHom eP.hom (𝟙 _)) ≫
            G.map ((DerivedCategory.Q.commShiftIso n).hom.app B) =
          S.tensor.map (Prod.mkHom eP.hom
            ((DerivedCategory.Q.commShiftIso n).hom.app B)) := by
          change S.tensor.map (Prod.mkHom eP.hom (𝟙 _)) ≫
            S.tensor.map (Prod.mkHom (𝟙 V)
              ((DerivedCategory.Q.commShiftIso n).hom.app B)) = _
          rw [← Functor.map_comp]
          congr 1
          ext <;> simp
        have hh : (cL.hom.app (B⟦n⟧) ≫
            d.hom.app (DerivedCategory.Q.obj (B⟦n⟧))) ≫
              G.map ((DerivedCategory.Q.commShiftIso n).hom.app B) ≫
                (G.commShiftIso n).hom.app (DerivedCategory.Q.obj B) =
            (((KFlatFixedTensor.totalTensor R).obj P ⋙
              DerivedCategory.Q).commShiftIso n).hom.app B ≫
                (cL.hom.app B ≫ d.hom.app (DerivedCategory.Q.obj B))⟦n⟧' := by
          rw [hbs, hb, Category.assoc, ← Category.assoc _ _
            ((G.commShiftIso n).hom.app (DerivedCategory.Q.obj B))]
          erw [hp]
          simpa only [G, Functor.commShiftIso_comp_hom_app,
            KFlatFixedTensor.totalTensor, Functor.commShiftIso_map₂CochainComplex_hom_app,
            coefficientTotalTensor, KFlatFixedTensor.ordinaryTensor, Functor.comp_obj,
            Functor.uncurry_obj_obj, Functor.map₂CochainComplex, Category.assoc] using h
        rw [← hh]
        simp only [Category.assoc]
        rw [← d.hom.naturality_assoc]
        rfl
  let := hd
  have heq : ((Functor.curry.mapIso e).app V).hom =
      (KFlatFixedTensor.derivedTensor R).map eP.inv ≫ d.hom := by
    ext A
    let U := siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R
    change e.hom.app (V, A) = U.map (Prod.mkHom eP.inv (𝟙 A)) ≫ d.hom.app A
    apply (cancel_epi (U.map (eP.prod (Iso.refl A)).hom)).mp
    simp only [Iso.prod_hom, Iso.refl_hom]
    rw [← Category.assoc, ← Functor.map_comp]
    have hp : Prod.mkHom eP.hom (𝟙 A) ≫ Prod.mkHom eP.inv (𝟙 A) = 𝟙 _ := by
      ext <;> simp
    rw [hp, Functor.map_id, Category.id_comp]
    exact e.hom.naturality (Prod.mkHom eP.hom (𝟙 A))
  refine ⟨Functor.isTriangulated_of_iso d, ?_⟩
  rw [heq]
  infer_instance

private theorem action_shift_naturality
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (s : ∀ V : ActionD.{c, v, u, w} J R, (tensorHomActionSource S V).CommShift ℤ)
    (s₀ : (KFlatFixedTensor.derivedTensor R).CommShift₂Int)
    (e : siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R ≅ S.tensor)
    (he : letI := s₀
      letI (V : ActionD.{c, v, u, w} J R) := s V
      letI (V : ActionD.{c, v, u, w} J R) :
          ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
      ∀ V, NatTrans.CommShift ((Functor.curry.mapIso e).app V).hom ℤ) :
    letI (V : ActionD.{c, v, u, w} J R) := s V
    ∀ (X Y : ActionD.{c, v, u, w} J R) (f : X ⟶ Y)
      (A : ActionD.{c, v, u, w} J R) (n : ℤ),
      S.tensor.map (Prod.mkHom f (𝟙 (A⟦n⟧))) ≫
          ((tensorHomActionSource S Y).commShiftIso n).hom.app A =
        ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
          (S.tensor.map (Prod.mkHom f (𝟙 A)))⟦n⟧' := by
  let := s₀
  let (V : ActionD.{c, v, u, w} J R) := s V
  let (V : ActionD.{c, v, u, w} J R) :
      ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
  intro X Y f A n
  let eX := (Functor.curry.mapIso e).app X
  let eY := (Functor.curry.mapIso e).app Y
  have := he X
  have := he Y
  have heq : (Functor.curry.obj S.tensor).map f =
      eX.inv ≫ (KFlatFixedTensor.derivedTensor R).map f ≫ eY.hom := by
    ext B
    change S.tensor.map (Prod.mkHom f (𝟙 B)) =
      e.inv.app (X, B) ≫
        (siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R).map
          (Prod.mkHom f (𝟙 B)) ≫ e.hom.app (Y, B)
    rw [e.hom.naturality]
    simp
  have hm : NatTrans.CommShift ((Functor.curry.obj S.tensor).map f) ℤ := by
    rw [heq]
    infer_instance
  let := hm
  exact (NatTrans.shift_app_comm ((Functor.curry.obj S.tensor).map f) n A).symm

private theorem action_model_symmetry
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P Q : ActionComplex.{c, v, u} J R)
    (hP : P.IsKFlatIndependentCoefficients (J := J) (R := R))
    (hQ : Q.IsKFlatIndependentCoefficients (J := J) (R := R)) :
    (T.iso J R S P Q hP hQ).hom ≫
        (β.toBraidedCategory.braiding (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (β_ P Q).hom ≫ (T.iso J R S Q P hQ hP).hom := by
  obtain ⟨σ, hσ, he⟩ := hc.symmetry_model P Q hP hQ
  have heq : σ.hom = (β_ P Q).hom := by
    apply tensorGenerator_ext.{c, v, u} J R
    intro p q k hpq U x y
    have hqp : q + p = k := (add_comm q p).trans hpq
    exact (hσ p q k hpq hqp U x y).trans
      ((RingedDerivedNative.complexConstraints.{c, v, u} J R).symmetry
        P Q p q k hpq hqp U x y).symm
  simpa only [heq] using he

set_option maxHeartbeats 800000 in
-- Matching nested total-tensor comparisons requires additional elaboration heartbeats.
private theorem action_model_associator
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P Q N : ActionComplex.{c, v, u} J R)
    (hP : P.IsKFlatIndependentCoefficients (J := J) (R := R))
    (hQ : Q.IsKFlatIndependentCoefficients (J := J) (R := R))
    (hN : N.IsKFlatIndependentCoefficients (J := J) (R := R)) :
    (hc.tensorIso ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) N (Or.inr hN)).hom ≫
        S.tensor.map (Prod.mkHom (T.iso J R S P Q hP hQ).hom (𝟙 _)) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map (α_ P Q N).hom ≫
        (hc.tensorIso P ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N))
          (Or.inl hP)).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 _) (T.iso J R S Q N hQ hN).hom) := by
  obtain ⟨a, ha, he⟩ := hc.associator_model P Q N hP hQ hN
  have heq : a.hom = (α_ P Q N).hom := by
    apply tensorGenerator_ext₃.{c, v, u} J R
    intro p q t i k hpq hit U x y z
    have hpj : p + (q + t) = k := by omega
    exact (ha p q t i (q + t) k hpq rfl hit hpj U x y z).trans
      ((RingedDerivedNative.complexConstraints.{c, v, u} J R).associator
        P Q N p q t i (q + t) k hpq rfl hit hpj U x y z).symm
  simpa only [heq] using he

private def actionExchange {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory D _ S.monoidal)
    (X A K : D) : S.tensor.obj (S.tensor.obj (X, A), K) ⟶
      S.tensor.obj (S.tensor.obj (X, K), A) :=
  (S.monoidal.associator X A K).hom ≫
    S.tensor.map (Prod.mkHom (𝟙 X) (β.toBraidedCategory.braiding A K).hom) ≫
      (S.monoidal.associator X K A).inv

private theorem action_uncurry {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory D _ S.monoidal)
    (K L A : D) :
    S.tensor.map (Prod.mkHom (tensorHomAction S β K L A) (𝟙 K)) ≫
        S.evaluation K (S.tensor.obj (L, A)) =
      actionExchange S β (H.obj (op K, L)) A K ≫
        S.tensor.map (Prod.mkHom (S.evaluation K L) (𝟙 A)) := by
  let _ := S.monoidal
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map]
  rw [tensorHom_id]
  change (S.transpose _ K _).symm (tensorHomAction S β K L A) = _
  unfold tensorHomAction
  rw [Equiv.symm_apply_apply]
  simp only [actionExchange, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, Category.assoc]

private theorem action_complex_ext
    {F : ActionD.{c, v, u, w} J R ⥤ ActionD.{c, v, u, w} J R}
    {G : ActionComplex.{c, v, u} J R ⥤ ActionD.{c, v, u, w} J R}
    (η θ : DerivedCategory.Q ⋙ F ⟶ G)
    (h : ∀ (P : ActionComplex.{c, v, u} J R)
      (_ : TensorFlatRepresentative (J := J) (R := R) P), η.app P = θ.app P) : η = θ := by
  ext B
  obtain ⟨P, f, hP, hf⟩ :=
    SheafOfModules.flat_resolution (J := J) (R := R) B
  let := hf
  apply (cancel_epi (F.map (DerivedCategory.Q.map f))).mp
  change (DerivedCategory.Q ⋙ F).map f ≫ η.app B =
    (DerivedCategory.Q ⋙ F).map f ≫ θ.app B
  rw [η.naturality, θ.naturality, h P hP]

private theorem action_exchange_of_assoc_braid
    {D : Type a} [Category.{b} D] [HasShift D ℤ]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal)
    (s : ∀ V : D, (tensorHomActionSource S V).CommShift ℤ)
    (l : ∀ n : ℤ, (shiftFunctor D n).prod (𝟭 D) ⋙ S.tensor ≅
      S.tensor ⋙ shiftFunctor D n)
    (hmap : let (V : D) := s V
      ∀ (X Y : D) (f : X ⟶ Y) (A : D) (n : ℤ),
        S.tensor.map (Prod.mkHom f (𝟙 (A⟦n⟧))) ≫
          ((tensorHomActionSource S Y).commShiftIso n).hom.app A =
        ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
          (S.tensor.map (Prod.mkHom f (𝟙 A)))⟦n⟧')
    (hassoc : let (V : D) := s V
      ∀ (X Y A : D) (n : ℤ),
        (S.monoidal.associator X Y (A⟦n⟧)).hom ≫
          S.tensor.map (Prod.mkHom (𝟙 X)
            (((tensorHomActionSource S Y).commShiftIso n).hom.app A)) ≫
          ((tensorHomActionSource S X).commShiftIso n).hom.app (S.tensor.obj (Y, A)) =
        ((tensorHomActionSource S (S.tensor.obj (X, Y))).commShiftIso n).hom.app A ≫
          ((S.monoidal.associator X Y A).hom)⟦n⟧')
    (hbraid : let (V : D) := s V
      ∀ (X K : D) (n : ℤ),
        (β.toBraidedCategory.braiding (X⟦n⟧) K).hom ≫
          ((tensorHomActionSource S K).commShiftIso n).hom.app X =
        (l n).hom.app (X, K) ≫ ((β.toBraidedCategory.braiding X K).hom)⟦n⟧') :
    let (V : D) := s V
    ∀ (X K A : D) (n : ℤ),
      actionExchange S β X (A⟦n⟧) K ≫
        ((tensorHomActionSource S (S.tensor.obj (X, K))).commShiftIso n).hom.app A =
      S.tensor.map (Prod.mkHom
        (((tensorHomActionSource S X).commShiftIso n).hom.app A) (𝟙 K)) ≫
        (l n).hom.app (S.tensor.obj (X, A), K) ≫ (actionExchange S β X A K)⟦n⟧' := by
  let _ := S.monoidal
  let _ := β
  let (V : D) := s V
  dsimp only
  intro X K A n
  have hex (B : D) : actionExchange S β X B K =
      (β_ (X ⊗ B) K).hom ≫ (α_ K X B).inv ≫ (β_ X K).inv ▷ B := by
    simp only [BraidedCategory.braiding_tensor_left_hom, Category.assoc,
      Iso.hom_inv_id_assoc, actionExchange,
      CoefficientClosedStructure.tensor, tensor_map, id_tensorHom]
    simp only [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.comp_id]
  have ha := hassoc K X A n
  have hai : (α_ K X (A⟦n⟧)).inv ≫
      ((tensorHomActionSource S (K ⊗ X)).commShiftIso n).hom.app A =
      K ◁ (((tensorHomActionSource S X).commShiftIso n).hom.app A) ≫
        ((tensorHomActionSource S K).commShiftIso n).hom.app (X ⊗ A) ≫
        ((α_ K X A).inv)⟦n⟧' := by
    have hh := congrArg (fun f ↦ (α_ K X (A⟦n⟧)).inv ≫ f ≫
      ((α_ K X A).inv)⟦n⟧') ha
    simp only [CoefficientClosedStructure.tensor, tensor_map, tensor_obj,
      id_tensorHom, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
      Iso.hom_inv_id, Functor.map_id] at hh
    simpa only [tensorHomActionSource, Functor.comp_obj, Prod.sectR,
      CoefficientClosedStructure.tensor, tensor_obj, Category.comp_id] using hh.symm
  have hm := hmap (K ⊗ X) (X ⊗ K) (β_ X K).inv A n
  dsimp only [CoefficientClosedStructure.tensor, tensor_map] at hm ⊢
  simp only [tensorHom_id] at hm ⊢
  rw [hex (A⟦n⟧)]
  simp only [Category.assoc]
  erw [hm, reassoc_of% hai]
  rw [← BraidedCategory.braiding_naturality_left_assoc]
  erw [reassoc_of% hbraid (X ⊗ A) K n]
  simp only [← Functor.map_comp]
  erw [tensorHom_id]
  erw [← hex A]; rfl

private def actionAssocNatTrans
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (X Y : D) :
    tensorHomActionSource S (S.tensor.obj (X, Y)) ⟶
      tensorHomActionSource S Y ⋙ tensorHomActionSource S X := by
  let _ := S.monoidal
  refine { app := fun A ↦ (α_ X Y A).hom, naturality := ?_ }
  intro A B f
  dsimp only [tensorHomActionSource, Functor.comp_map, Functor.comp_obj, Prod.sectR,
    CoefficientClosedStructure.tensor, tensor_map, tensor_obj]
  simpa only [id_tensorHom] using associator_naturality_right X Y f

set_option maxHeartbeats 2000000 in
-- Elaborating the recorded tensor and shift comparisons requires extra heartbeats.
private theorem action_associator_shift
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : ActionD.{c, v, u, w} J R, (tensorHomActionSource S V).CommShift ℤ)
    (hm : let (V : ActionD.{c, v, u, w} J R) :
        ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
      ∀ {X Y : ActionD.{c, v, u, w} J R} (f : X ⟶ Y),
        NatTrans.CommShift ((Functor.curry.obj S.tensor).map f) ℤ)
    (hCS : let (V : ActionD.{c, v, u, w} J R) := s V
      ∀ (P : ActionComplex.{c, v, u} J R)
        (hP : TensorFlatRepresentative (J := J) (R := R) P),
        ∃ cP : (KFlatFixedTensor.totalTensor R).obj P ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ tensorHomActionSource S (DerivedCategory.Q.obj P),
          NatTrans.CommShift cP.hom ℤ ∧
          ∀ (B : ActionComplex.{c, v, u} J R)
            (hB : TensorFlatRepresentative (J := J) (R := R) B),
            cP.hom.app B = (T.iso J R S P B hP.1 hB.1).hom) :
    let (V : ActionD.{c, v, u, w} J R) := s V
    let (V : ActionD.{c, v, u, w} J R) :
        ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
    ∀ (X Y A : ActionD.{c, v, u, w} J R) (n : ℤ),
      (S.monoidal.associator X Y (A⟦n⟧)).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 X)
          (((tensorHomActionSource S Y).commShiftIso n).hom.app A)) ≫
        ((tensorHomActionSource S X).commShiftIso n).hom.app (S.tensor.obj (Y, A)) =
      ((tensorHomActionSource S (S.tensor.obj (X, Y))).commShiftIso n).hom.app A ≫
        ((S.monoidal.associator X Y A).hom)⟦n⟧' := by
  let _ := S.monoidal
  let (V : ActionD.{c, v, u, w} J R) := s V
  let (V : ActionD.{c, v, u, w} J R) :
      ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
  let {X Y : ActionD.{c, v, u, w} J R} (f : X ⟶ Y) := hm f
  have hflat (P Q : ActionComplex.{c, v, u} J R)
      (hP : TensorFlatRepresentative (J := J) (R := R) P)
      (hQ : TensorFlatRepresentative (J := J) (R := R) Q) :
      NatTrans.CommShift (actionAssocNatTrans S
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) ℤ := by
    let PQ := ((KFlatFixedTensor.totalTensor R).obj P).obj Q
    have hPQ : TensorFlatRepresentative (J := J) (R := R) PQ := by
      have hh := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hP.1 hQ.1 hP.2 hQ.2
      exact ⟨hh.1, hh.2.1⟩
    obtain ⟨cP, hcP, hnP⟩ := hCS P hP
    obtain ⟨cQ, hcQ, hnQ⟩ := hCS Q hQ
    obtain ⟨cPQ, hcPQ, hnPQ⟩ := hCS PQ hPQ
    let := hcP
    let := hcQ
    let := hcPQ
    let f := T.iso J R S P Q hP.1 hQ.1
    let e₁ := Functor.isoWhiskerLeft DerivedCategory.Q
      ((Functor.curry.obj S.tensor).mapIso f.symm) ≪≫ cPQ.symm
    let e₂ := (Functor.associator DerivedCategory.Q
        (tensorHomActionSource S (DerivedCategory.Q.obj Q))
        (tensorHomActionSource S (DerivedCategory.Q.obj P))).symm ≪≫
      Functor.isoWhiskerRight cQ.symm
        (tensorHomActionSource S (DerivedCategory.Q.obj P)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((KFlatFixedTensor.totalTensor R).obj Q) cP.symm ≪≫
      (Functor.associator _ _ _).symm
    let chainAssoc : (KFlatFixedTensor.totalTensor R).obj PQ ⟶
        (KFlatFixedTensor.totalTensor R).obj Q ⋙ (KFlatFixedTensor.totalTensor R).obj P :=
      { app := fun A ↦ (α_ P Q A).hom
        naturality := fun {A B} f ↦ associator_naturality_right P Q f }
    have hchain : NatTrans.CommShift chainAssoc ℤ := by
      constructor
      intro n
      refine NatTrans.ext (funext fun A ↦ ?_)
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, KFlatFixedTensor.totalTensor,
        Functor.commShiftIso_map₂CochainComplex_hom_app]
      exact (CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₂Iso_hom
        P Q A n).symm
    let := hchain
    have hf : NatTrans.CommShift ((Functor.curry.obj S.tensor).map f.inv) ℤ := hm _
    let := hf
    have he₁ : NatTrans.CommShift e₁.hom ℤ := by
      dsimp only [e₁, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
        Functor.mapIso_hom, Iso.symm_hom]
      infer_instance
    let := he₁
    have he₂ : NatTrans.CommShift e₂.hom ℤ := by
      dsimp only [e₂, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.associator_hom_app, Iso.symm_hom]
      infer_instance
    let := he₂
    let τ := actionAssocNatTrans S (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    let σ := Functor.whiskerRight chainAssoc DerivedCategory.Q
    have hcompat : Functor.whiskerLeft DerivedCategory.Q τ ≫ e₂.hom = e₁.hom ≫ σ := by
      apply action_complex_ext.{c, v, u, w} J R
      intro A hA
      have hQA : TensorFlatRepresentative (J := J) (R := R)
          (((KFlatFixedTensor.totalTensor R).obj Q).obj A) := by
        have hh := KFlatTotalTensorModel.kFlat_total_tensor_model R Q A hQ.1 hA.1 hQ.2 hA.2
        exact ⟨hh.1, hh.2.1⟩
      have ha := action_model_associator.{c, v, u, w} J R S T β hc P Q A hP.1 hQ.1 hA.1
      erw [hc.tensorIso_both PQ A hPQ.1 hA.1,
        hc.tensorIso_both P (((KFlatFixedTensor.totalTensor R).obj Q).obj A) hP.1 hQA.1,
        ← hnPQ A hA, ← hnP _ hQA, ← hnQ A hA] at ha
      simp only [τ, σ, e₁, e₂, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        actionAssocNatTrans, chainAssoc]
      apply (cancel_epi (cPQ.hom.app A ≫
        (S.tensor.mapIso (f.prod (Iso.refl (DerivedCategory.Q.obj A)))).hom)).mp
      dsimp only [f, Functor.mapIso_hom, Iso.prod, Iso.refl_hom, Iso.symm_hom,
        tensorHomActionSource, Functor.comp_map, Prod.sectR,
        Functor.curry_obj_map_app, Functor.curry_obj_obj_map,
        CoefficientClosedStructure.tensor, tensor_map] at ha ⊢
      simp only [tensorHom_id, id_tensorHom, Category.assoc] at ha ⊢
      rw [reassoc_of% ha]
      simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id_app,
        Category.id_comp, Iso.hom_inv_id_app_assoc,
        ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight]
      erw [whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
    have heq : Functor.whiskerLeft DerivedCategory.Q τ = e₁.hom ≫ σ ≫ e₂.inv := by
      apply (cancel_mono e₂.hom).mp
      rw [Category.assoc, Category.assoc, e₂.inv_hom_id, Category.comp_id, hcompat]
    have hcomm : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q τ) ℤ := by
      rw [heq]
      dsimp only [σ]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft τ DerivedCategory.Q (fun X ↦ by
      obtain ⟨A, hA, ⟨e⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R X
      exact ⟨A, e.inv, inferInstance⟩)
  have hall (X Y : ActionD.{c, v, u, w} J R) :
      NatTrans.CommShift (actionAssocNatTrans S X Y) ℤ := by
    obtain ⟨P, hP, ⟨eP⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R X
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R Y
    have := hflat P Q hP hQ
    have he : actionAssocNatTrans S X Y =
        (Functor.curry.obj S.tensor).map (eP.inv ⊗ₘ eQ.inv) ≫
        actionAssocNatTrans S
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        Functor.whiskerRight ((Functor.curry.obj S.tensor).map eQ.hom)
          ((Functor.curry.obj S.tensor).obj (DerivedCategory.Q.obj P)) ≫
        Functor.whiskerLeft ((Functor.curry.obj S.tensor).obj Y)
          ((Functor.curry.obj S.tensor).map eP.hom) := by
      ext A
      dsimp only [actionAssocNatTrans, tensorHomActionSource, Functor.curry_obj_obj_obj,
        Functor.curry_obj_map_app, Functor.curry_obj_obj_map, Functor.comp_obj,
        NatTrans.comp_app, actionAssocNatTrans, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, curriedTensor_obj_map,
        CoefficientClosedStructure.tensor, tensor_map, tensor_obj, Prod.sectR]
      simp only [tensorHom_def, comp_whiskerRight, Category.assoc]
      simp only [Category.id_comp, Category.comp_id, ← comp_whiskerRight_assoc,
        whiskerLeft_id, id_whiskerRight]
      erw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc]
      simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight,
        Iso.inv_hom_id, id_whiskerRight, whiskerLeft_id, Category.id_comp]
      erw [associator_naturality_left_assoc]
      simp only [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    rw [he]
    infer_instance
  dsimp only
  intro X Y A n
  have := hall X Y
  have hh := NatTrans.shift_app_comm
    (actionAssocNatTrans S X Y) n A
  simpa only [Functor.commShiftIso_comp_hom_app, actionAssocNatTrans,
    tensorHomActionSource, Functor.comp_obj, Functor.comp_map, Prod.sectR,
    CoefficientClosedStructure.tensor, tensor_map, tensor_obj, id_tensorHom] using hh.symm

private theorem action_natTrans_ext₂
    {F G : ActionD.{c, v, u, w} J R × ActionD.{c, v, u, w} J R ⥤
      ActionD.{c, v, u, w} J R}
    (η θ : F ⟶ G)
    (h : ∀ (P Q : ActionComplex.{c, v, u} J R)
      (_ : TensorFlatRepresentative (J := J) (R := R) P)
      (_ : TensorFlatRepresentative (J := J) (R := R) Q),
      η.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        θ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : η = θ := by
  ext ⟨M, N⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R M
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := RingedHomTargetShift.flatRepresentatives.{c, v, u, w} J R N
  apply (cancel_epi (F.map (eP.prod eQ).hom)).mp
  rw [η.naturality, θ.naturality, h P Q hP hQ]

private def action_secondShiftIso
    {D : Type a} [Category.{b} D] [HasShift D ℤ]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (s : ∀ V : D, (tensorHomActionSource S V).CommShift ℤ)
    (hm : let (V : D) := s V
      ∀ (X Y : D) (f : X ⟶ Y) (A : D) (n : ℤ),
        S.tensor.map (Prod.mkHom f (𝟙 (A⟦n⟧))) ≫
          ((tensorHomActionSource S Y).commShiftIso n).hom.app A =
        ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
          (S.tensor.map (Prod.mkHom f (𝟙 A)))⟦n⟧')
    (n : ℤ) : (𝟭 D).prod (shiftFunctor D n) ⋙ S.tensor ≅
      S.tensor ⋙ shiftFunctor D n := by
  let (V : D) := s V
  refine NatIso.ofComponents
    (fun X ↦ ((tensorHomActionSource S X.1).commShiftIso n).app X.2) ?_
  rintro ⟨X, A⟩ ⟨Y, B⟩ ⟨f, g⟩
  change S.tensor.map (Prod.mkHom f (g⟦n⟧')) ≫
      ((tensorHomActionSource S Y).commShiftIso n).hom.app B =
    ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
      (S.tensor.map (Prod.mkHom f g))⟦n⟧'
  have hn := (tensorHomActionSource S X).commShiftIso_hom_naturality g n
  change S.tensor.map (Prod.mkHom (𝟙 X) (g⟦n⟧')) ≫
      ((tensorHomActionSource S X).commShiftIso n).hom.app B =
    ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
      (S.tensor.map (Prod.mkHom (𝟙 X) g))⟦n⟧' at hn
  have hp : Prod.mkHom f (g⟦n⟧') =
      Prod.mkHom (𝟙 X) (g⟦n⟧') ≫ Prod.mkHom f (𝟙 (B⟦n⟧)) := by
    ext <;> simp
  rw [hp, Functor.map_comp, Category.assoc]
  erw [hm X Y f B n]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  have hp' : Prod.mkHom (𝟙 X) g ≫ Prod.mkHom f (𝟙 B) = Prod.mkHom f g := by
    ext <;> simp
  rw [hp']

set_option maxHeartbeats 2000000 in
-- Elaborating the recorded tensor and shift comparisons requires extra heartbeats.
private theorem action_braiding_shift
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : ActionD.{c, v, u, w} J R, (tensorHomActionSource S V).CommShift ℤ)
    (hs : tensorHomActionShiftNormalization J R S T β hc s)
    (hm : let (V : ActionD.{c, v, u, w} J R) := s V
      ∀ (X Y : ActionD.{c, v, u, w} J R) (f : X ⟶ Y)
        (A : ActionD.{c, v, u, w} J R) (n : ℤ),
        S.tensor.map (Prod.mkHom f (𝟙 (A⟦n⟧))) ≫
          ((tensorHomActionSource S Y).commShiftIso n).hom.app A =
        ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
          (S.tensor.map (Prod.mkHom f (𝟙 A)))⟦n⟧') :
    let (V : ActionD.{c, v, u, w} J R) := s V
    let (V : ActionD.{c, v, u, w} J R) :
        ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
    ∀ (X K : ActionD.{c, v, u, w} J R) (n : ℤ),
      (β.toBraidedCategory.braiding (X⟦n⟧) K).hom ≫
        ((tensorHomActionSource S K).commShiftIso n).hom.app X =
      (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app (X, K) ≫
        ((β.toBraidedCategory.braiding X K).hom)⟦n⟧' := by
  let _ := S.monoidal
  let _ := β
  let (V : ActionD.{c, v, u, w} J R) := s V
  let (V : ActionD.{c, v, u, w} J R) :
      ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
  dsimp only
  intro X K n
  let D := ActionD.{c, v, u, w} J R
  let b : S.tensor ≅ Prod.swap D D ⋙ S.tensor :=
    NatIso.ofComponents (fun Y ↦ β_ Y.1 Y.2) (by
      rintro ⟨U, V⟩ ⟨U', V'⟩ ⟨f, g⟩
      exact BraidedCategory.braiding_naturality f g)
  let σ := action_secondShiftIso S s hm n
  let η := Functor.whiskerLeft ((shiftFunctor D n).prod (𝟭 D)) b.hom ≫
    Functor.whiskerLeft (Prod.swap D D) σ.hom
  let θ := (RingedHomTargetShift.tensorShift J R S T β hc n).hom ≫
    Functor.whiskerRight b.hom (shiftFunctor D n)
  have he : η = θ := by
    apply action_natTrans_ext₂.{c, v, u, w} J R
    intro P Q hP hQ
    have hPs := RingedHomTargetShift.flatShift.{c, v, u} J R P hP n
    have hβ₁ := action_model_symmetry.{c, v, u, w} J R S T β hc
      (P⟦n⟧) Q hPs.1 hQ.1
    have hβ₀ := action_model_symmetry.{c, v, u, w} J R S T β hc P Q hP.1 hQ.1
    rw [← hc.tensorIso_both, ← hc.tensorIso_both] at hβ₁ hβ₀
    have h₂ := hs (DerivedCategory.Q.obj Q) Q P hQ.1 hP.1 (Iso.refl _) n
    have hid : S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj Q))
        (𝟙 (DerivedCategory.Q.obj P))) = 𝟙 _ :=
      S.tensor.map_id (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P)
    simp only [Iso.refl_hom, hid, Category.comp_id] at h₂
    have h₁ := (RingedHomTargetShift.tensorShift_existsUnique.{c, v, u, w}
      J R S T β hc).exists.choose_spec P Q hP hQ n
    change (hc.tensorIso (P⟦n⟧) Q (Or.inr hQ.1)).hom ≫
      S.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 _)) ≫
      (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) = _ at h₁
    have hb : (β_ (P⟦n⟧) Q).hom ≫
        (CochainComplex.mapBifunctorShift₂Iso Q P
          (curriedTensor (RingedTensorModules.{c, v, u} J R)) n).hom =
      (CochainComplex.mapBifunctorShift₁Iso P Q
          (curriedTensor (RingedTensorModules.{c, v, u} J R)) n).hom ≫
        ((β_ P Q).hom)⟦n⟧' := by
      apply (cancel_epi (β_ Q (P⟦n⟧)).hom).mp
      rw [← Category.assoc, RingedDerivedNative.complex_symmetry, Category.id_comp]
      rw [← Category.assoc]
      erw [CochainComplex.Monoidal.braiding_hom_mapBifunctorShift₁Iso_hom Q P n]
      change _ = (CochainComplex.mapBifunctorShift₂Iso Q P
        (curriedTensor (RingedTensorModules.{c, v, u} J R)) n).hom ≫
          ((β_ Q P).hom)⟦n⟧' ≫ ((β_ P Q).hom)⟦n⟧'
      rw [← Functor.map_comp, RingedDerivedNative.complex_symmetry]
      erw [Functor.map_id, Category.comp_id]
    have hγ := (DerivedCategory.Q.commShiftIso n).hom.naturality (β_ P Q).hom
    let γ := ((DerivedCategory.Q.commShiftIso n).app P)
    let z := hc.tensorIso (P⟦n⟧) Q (Or.inr hQ.1) ≪≫
      S.tensor.mapIso (γ.prod (Iso.refl (DerivedCategory.Q.obj Q)))
    change (β_ ((DerivedCategory.Q.obj P)⟦n⟧) (DerivedCategory.Q.obj Q)).hom ≫
      ((tensorHomActionSource S (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
        (DerivedCategory.Q.obj P) =
      (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        ((β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom)⟦n⟧'
    apply (cancel_epi z.hom).mp
    dsimp only [z, γ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
      Iso.refl_hom, Iso.app_hom]
    calc
      _ = DerivedCategory.Q.map (β_ (P⟦n⟧) Q).hom ≫
          ((hc.tensorIso Q (P⟦n⟧) (Or.inl hQ.1)).hom ≫
            S.tensor.map (Prod.mkHom (𝟙 _)
              ((DerivedCategory.Q.commShiftIso n).hom.app P)) ≫
            ((tensorHomActionSource S (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
              (DerivedCategory.Q.obj P)) := by
        dsimp only [CoefficientClosedStructure.tensor, tensor_map] at hβ₁ ⊢
        simp only [tensorHom_id, id_tensorHom, Category.assoc]
        erw [BraidedCategory.braiding_naturality_left_assoc
          ((DerivedCategory.Q.commShiftIso n).hom.app P) (DerivedCategory.Q.obj Q),
          reassoc_of% hβ₁]
      _ = DerivedCategory.Q.map ((β_ (P⟦n⟧) Q).hom ≫
          (CochainComplex.mapBifunctorShift₂Iso Q P
            (curriedTensor (RingedTensorModules.{c, v, u} J R)) n).hom) ≫
          (DerivedCategory.Q.commShiftIso n).hom.app
            ((coefficientTotalTensor.{u, c, v} J R).obj (Q, P)) ≫
          ((hc.tensorIso Q P (Or.inl hQ.1)).hom)⟦n⟧' := by
        rw [h₂]
        simp only [Functor.map_comp, Category.assoc]
      _ = DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₁Iso P Q
            (curriedTensor (RingedTensorModules.{c, v, u} J R)) n).hom ≫
          (DerivedCategory.Q.commShiftIso n).hom.app
            ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≫
          ((hc.tensorIso P Q (Or.inl hP.1)).hom ≫
            (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom)⟦n⟧' := by
        rw [hb]
        simp only [Functor.map_comp, Category.assoc]
        erw [reassoc_of% hγ]
        rw [← Functor.map_comp, ← hβ₀]
        simp only [Functor.map_comp]; with_unfolding_all rfl
      _ = _ := by
        simpa only [Functor.map_comp, Category.assoc, RingedHomTargetShift.totalShift,
          Iso.prod_hom, Iso.refl_hom, Iso.app_hom] using
          (congrArg (fun f ↦ f ≫
            ((β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom)⟦n⟧') h₁).symm
  simpa only [η, θ, b, σ, action_secondShiftIso, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
    Functor.prod_obj, Functor.id_obj, Prod.swap_obj, Iso.app_hom]
    using NatTrans.congr_app he (X, K)

set_option maxHeartbeats 2000000 in
-- Elaborating the recorded tensor and shift comparisons requires extra heartbeats.
private theorem action_shift_of_exchange
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (ActionD.{c, v, u, w} J R) _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : ActionD.{c, v, u, w} J R, (tensorHomActionSource S V).CommShift ℤ)
    (hmap : letI (V : ActionD.{c, v, u, w} J R) := s V
      ∀ (X Y : ActionD.{c, v, u, w} J R) (f : X ⟶ Y)
        (A : ActionD.{c, v, u, w} J R) (n : ℤ),
        S.tensor.map (Prod.mkHom f (𝟙 (A⟦n⟧))) ≫
            ((tensorHomActionSource S Y).commShiftIso n).hom.app A =
          ((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
            (S.tensor.map (Prod.mkHom f (𝟙 A)))⟦n⟧')
    (hexchange : letI (V : ActionD.{c, v, u, w} J R) := s V
      ∀ (X K A : ActionD.{c, v, u, w} J R) (n : ℤ),
        actionExchange S β X (A⟦n⟧) K ≫
            ((tensorHomActionSource S (S.tensor.obj (X, K))).commShiftIso n).hom.app A =
          S.tensor.map (Prod.mkHom
            (((tensorHomActionSource S X).commShiftIso n).hom.app A) (𝟙 K)) ≫
            (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app
              (S.tensor.obj (X, A), K) ≫ (actionExchange S β X A K)⟦n⟧') :
    let (V : ActionD.{c, v, u, w} J R) := s V
    let (V : ActionD.{c, v, u, w} J R) :
        ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
    ∀ (K L A : ActionD.{c, v, u, w} J R) (n : ℤ),
      tensorHomAction S β K L (A⟦n⟧) ≫
          ((tensorHomActionTarget S K L).commShiftIso n).hom.app A =
        ((tensorHomActionSource S
          ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))).commShiftIso n).hom.app
          A ≫ (tensorHomAction S β K L A)⟦n⟧' := by
  let (V : ActionD.{c, v, u, w} J R) := s V
  let (V : ActionD.{c, v, u, w} J R) :
      ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
  dsimp only
  intro K L A n
  let X := (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L)
  let M := S.tensor.obj (L, A)
  let h := ((RingedHomUniverses.hom.{c, v, u, w} J R K).commShiftIso n).app M
  let _ := S.monoidal
  let _ := β
  apply (cancel_mono h.inv).mp
  simp only [tensorHomActionTarget, Functor.commShiftIso_comp_hom_app, Category.assoc]
  change tensorHomAction S β K L (A⟦n⟧) ≫
      (RingedHomUniverses.hom J R K).map
        (((tensorHomActionSource S L).commShiftIso n).hom.app A) ≫ h.hom ≫ h.inv = _
  rw [h.hom_inv_id]
  erw [Category.comp_id]
  apply (S.transpose _ K (M⟦n⟧)).symm.injective
  change ((tensorHomAction S β K L (A⟦n⟧) ≫
      (RingedHomUniverses.hom J R K).map
        (((tensorHomActionSource S L).commShiftIso n).hom.app A)) ▷ K) ≫
        S.evaluation K (M⟦n⟧) =
    ((((tensorHomActionSource S X).commShiftIso n).hom.app A ≫
        (tensorHomAction S β K L A)⟦n⟧' ≫ h.inv) ▷ K) ≫ S.evaluation K (M⟦n⟧)
  have hev :
      ((RingedHomUniverses.hom J R K).map
          (((tensorHomActionSource S L).commShiftIso n).hom.app A) ▷ K) ≫
        S.evaluation K (M⟦n⟧) =
      S.evaluation K (S.tensor.obj (L, A⟦n⟧)) ≫
        ((tensorHomActionSource S L).commShiftIso n).hom.app A := by
    simpa only [RingedHomUniverses.hom, M, tensorHomActionSource,
      Functor.curry_obj_obj_map, Functor.curry_obj_obj_obj,
      CoefficientClosedStructure.evaluation, Functor.comp_map, Functor.comp_obj, Prod.sectR,
      MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip,
      Functor.id_map] using
      (S.adjunction K).counit.naturality
        (((tensorHomActionSource S L).commShiftIso n).hom.app A)
  have hl := (RingedHomTargetShift.tensorShift J R S T β hc n).hom.naturality
    (Prod.mkHom (tensorHomAction S β K L A) (𝟙 K))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
    CoefficientClosedStructure.tensor, tensor_map] at hl
  simp only [tensorHom_id] at hl
  erw [tensorHom_id] at hl
  change ((tensorHomAction S β K L A)⟦n⟧' ▷ K) ≫
      (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app
        ((RingedHomUniverses.hom J R K).obj M, K) =
    (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app
        (S.tensor.obj (X, A), K) ≫
      ((tensorHomAction S β K L A ▷ K)⟦n⟧') at hl
  have he := RingedHomTargetShift.evaluation_eq J R S T β hc K M n
  dsimp only [CoefficientClosedStructure.tensor, tensor_map] at he
  simp only [tensorHom_id] at he
  change S.evaluation K (M⟦n⟧) = (h.hom ▷ K) ≫
    (RingedHomTargetShift.tensorShift J R S T β hc n).hom.app
      ((RingedHomUniverses.hom J R K).obj M, K) ≫
        (S.evaluation K M)⟦n⟧' at he
  have hu (B : ActionD.{c, v, u, w} J R) :
      (tensorHomAction S β K L B ▷ K) ≫ S.evaluation K (S.tensor.obj (L, B)) =
        actionExchange S β X B K ≫ (S.evaluation K L ▷ B) := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id] using
      action_uncurry S β K L B
  dsimp only [CoefficientClosedStructure.tensor, tensor_map] at hmap hexchange
  simp only [tensorHom_id] at hmap hexchange
  simp only [CoefficientClosedStructure.tensor,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [hev, ← Category.assoc, hu, Category.assoc, hmap]
  erw [reassoc_of% hexchange X K A n]
  erw [tensorHom_id]
  erw [← Functor.map_comp, ← hu A]
  erw [he]
  simp only [← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  simp only [comp_whiskerRight, Category.assoc, Functor.map_comp]
  erw [reassoc_of% hl]; rfl

/-- Exactness and the coefficient-shift square.

Proof: identify each fixed tensor functor with tensoring by a flat-term K-flat
representative. K-flat fixed-tensor exactness, transported through the normalized
shift comparison, proves it is triangulated. Compose it with the exact covariant
internal-Hom functor to get target exactness. For the
shift square, descend the proved chain associator and braiding shift identities
through the normalized fixed-factor comparisons. Extend the identities along
flat representatives, and use the symmetric hexagon to obtain the exchange
shift identity. This carries the Koszul signs of the second-factor shift.
The normalization hypothesis and tensor descent identify the supplied shifts.
The target-Hom evaluation shift equation identifies the two
uncurried sides of the action shift square; injectivity of transposition proves it.
Naturality and the unit law are separate proved generic results;
the triangle-morphism clause is constructed in the entry module.
Source: Stacks 0BYU, with Tags 0A8X and 08JC (blueprint: lem-sf-tensor-hom-action-normalized-laws).
-/
theorem ringed_tensor_hom_action_laws_of_shift
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ)
    (hs : tensorHomActionShiftNormalization J R S T β hc s) :
    tensorHomActionExactCore J R S β s := by
  let (V : ActionD.{c, v, u, w} J R) := s V
  let (V : ActionD.{c, v, u, w} J R) :
      ((Functor.curry.obj S.tensor).obj V).CommShift ℤ := s V
  obtain ⟨s₀, e, ht, hCL, he⟩ := action_tensor_transport.{c, v, u, w} J R S T β hc s hs
  let := s₀
  have hF : ∀ V, (tensorHomActionSource S V).IsTriangulated := fun V ↦ (ht V).1
  have hm := action_shift_naturality.{c, v, u, w} J R S s s₀ e (fun V ↦ (ht V).2)
  have hmn {X Y : ActionD.{c, v, u, w} J R} (f : X ⟶ Y) :
      NatTrans.CommShift ((Functor.curry.obj S.tensor).map f) ℤ := by
    constructor
    intro n
    ext A
    exact (hm X Y f A n).symm
  have hCS (P : ActionComplex.{c, v, u} J R)
      (hP : TensorFlatRepresentative (J := J) (R := R) P) :
      ∃ cP : (KFlatFixedTensor.totalTensor R).obj P ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ tensorHomActionSource S (DerivedCategory.Q.obj P),
        NatTrans.CommShift cP.hom ℤ ∧
        ∀ (B : ActionComplex.{c, v, u} J R)
          (hB : TensorFlatRepresentative (J := J) (R := R) B),
          cP.hom.app B = (T.iso J R S P B hP.1 hB.1).hom := by
    obtain ⟨cL, hcL, hnL⟩ := hCL P hP
    let := hcL
    let eP := (Functor.curry.mapIso e).app (DerivedCategory.Q.obj P)
    have : NatTrans.CommShift eP.hom ℤ := (ht (DerivedCategory.Q.obj P)).2
    let cP := cL ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q eP
    refine ⟨cP, ?_, fun B hB ↦ ?_⟩
    · dsimp only [cP, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
      infer_instance
    · change cL.hom.app B ≫
        e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj B) = _
      rw [hnL B hB, he P B hP hB]
      exact congrArg Iso.hom (hc.tensorIso_both P B hP.1 hB.1)
  have ha := action_associator_shift.{c, v, u, w} J R S T β hc s hmn hCS
  have hb := action_braiding_shift.{c, v, u, w} J R S T β hc s hs hm
  refine ⟨hF, ?_, ?_⟩
  · intro K L
    have := hF L
    have := RingedHomUniverses.hom_isTriangulated.{c, v, u, w} J R K
    change ((tensorHomActionSource S L) ⋙ RingedHomUniverses.hom J R K).IsTriangulated
    infer_instance
  · apply action_shift_of_exchange.{c, v, u, w} J R S T β hc s hm
    exact action_exchange_of_assoc_braid S β s
      (RingedHomTargetShift.tensorShift J R S T β hc) hm ha hb

end CategoryTheory
