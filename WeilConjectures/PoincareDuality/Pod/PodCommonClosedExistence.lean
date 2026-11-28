/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCommonClosedHomNaturality
import WeilConjectures.PoincareDuality.Pod.PodPairHomDescent
import WeilConjectures.PoincareDuality.Derived.PodPartialHomNaturality
import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import all WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Existence and uniqueness of normalized common-stage closed data

A family of finite-stage rational closed data whose inverse transpositions, conjugated by the
stage comparisons, commute with the stage transitions descends to a unique common-stage
partial closed datum normalized by it.

## Main definitions

* `commonStageInverseTranspose`: the stage-level inverse transposition conjugated by the
  stage comparisons.

## Main statements

* `commonTransposeNormalized_exists`: existence of a normalized common-stage closed datum.
* `commonTransposeNormalized_unique`: uniqueness of a normalized common-stage closed datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard

section Abstract

-- Conjugate an additive bijection of Hom groups by equalities of objects.
private theorem homAddEquiv_conj {P : Type*} [Category P] [Preadditive P]
    {L H H' T T' N : P} (eT : T = T') (eH : H = H') (σ : (L ⟶ H') ≃+ (T' ⟶ N)) :
    ∃ e : (T ⟶ N) ≃+ (L ⟶ H), ∀ q, e.symm q = eqToHom eT ≫ σ (q ≫ eqToHom eH) := by
  subst eT eH
  exact ⟨σ.symm, fun q ↦ by simp⟩

-- Parameter naturality of conjugated descended bijections.
private theorem conj_parameter_naturality {P : Type*} [Category P] [Preadditive P]
    {L L' H H' T T' TL TL' N : P} (eT : T = TL) (eT' : T' = TL') (eH : H = H')
    (σ : (L ⟶ H') ≃+ (TL ⟶ N)) (σ' : (L' ⟶ H') ≃+ (TL' ⟶ N))
    (e : (T ⟶ N) ≃+ (L ⟶ H)) (e' : (T' ⟶ N) ≃+ (L' ⟶ H))
    (he : ∀ q, e.symm q = eqToHom eT ≫ σ (q ≫ eqToHom eH))
    (he' : ∀ q, e'.symm q = eqToHom eT' ≫ σ' (q ≫ eqToHom eH))
    (f : L' ⟶ L) (Tf : T' ⟶ T)
    (hσ : ∀ q, σ' (f ≫ q) = (eqToHom eT'.symm ≫ Tf ≫ eqToHom eT) ≫ σ q)
    (h : T ⟶ N) : e' (Tf ≫ h) = f ≫ e h := by
  subst eT eT' eH
  apply e'.symm.injective
  have h₁ := he (e h)
  simp only [AddEquiv.symm_apply_apply, eqToHom_refl, Category.comp_id,
    Category.id_comp] at h₁
  rw [AddEquiv.symm_apply_apply]
  simp only [he', eqToHom_refl, Category.comp_id, Category.id_comp, hσ, ← h₁]


-- Inverse transposes of conjugated descended bijections on representatives.
private theorem conj_normalization {P : Type*} [Category P] [Preadditive P]
    {L H H' T T' N : P} (eT : T = T') (eH : H = H') (σ : (L ⟶ H') ≃+ (T' ⟶ N))
    (e : (T ⟶ N) ≃+ (L ⟶ H)) (he : ∀ q, e.symm q = eqToHom eT ≫ σ (q ≫ eqToHom eH))
    (q : L ⟶ H) (x : L ⟶ H') (hq : HEq q x) (y : T' ⟶ N) (hy : σ x = y) :
    HEq (e.symm q) y := by
  subst eT eH
  rw [he, eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp, eq_of_heq hq, hy]

-- Parameter naturality of a conjugated inverse transposition.
private theorem param_algebra {C : Type*} [Category C] [Preadditive C] {T : C × C ⥤ C}
    {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C} (S : PodPartialClosed T J H)
    {L L' X U U' : C} (P : J.FullSubcategory) (f₀ : L' ⟶ L) (φ : L ⟶ X) (c : X ≅ H.obj P)
    (d' : U' ≅ T.obj (L', P.obj.1.unop)) (d : U ≅ T.obj (L, P.obj.1.unop)) :
    d'.hom ≫ (S.transpose L' P).symm ((f₀ ≫ φ) ≫ c.hom) =
      (d'.hom ≫ T.map (Prod.mkHom f₀ (𝟙 _)) ≫ d.inv) ≫ d.hom ≫
        (S.transpose L P).symm (φ ≫ c.hom) := by
  rw [Category.assoc, PodPartialClosed.symm_comp, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
end Abstract

section CommonClosed
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The stage-level inverse transposition at a finite stage, conjugated by the stage
comparisons of the tensor and the internal Hom. -/
def commonStageInverseTranspose
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory) (F : Index l Ω)
    (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F) (hN : P.obj.2.stage ≤ F) :
    (L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP) ≃+
      ((commonStageTensorObject l Ω W L P.obj.1.unop).toStage hT ⟶ P.obj.2.toStage hN) where
  toFun φ := (commonStageTensorComparison l Ω W L P.obj.1.unop F hT).hom ≫
    ((R F).transpose (L.toStage hL) (commonStageHomPairAtStage l Ω W P F hP)).symm
      (φ ≫ (commonStageHomComparison l Ω W P F hP).hom)
  invFun ψ := (R F).transpose (L.toStage hL) (commonStageHomPairAtStage l Ω W P F hP)
      ((commonStageTensorComparison l Ω W L P.obj.1.unop F hT).inv ≫ ψ) ≫
    (commonStageHomComparison l Ω W P F hP).inv
  left_inv φ := by
    simp only [Iso.inv_hom_id_assoc, AddEquiv.apply_symm_apply, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  right_inv ψ := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, AddEquiv.symm_apply_apply,
      Iso.hom_inv_id_assoc]
  map_add' φ φ' := by
    simp only [Preadditive.add_comp, map_add, Preadditive.comp_add]


-- The tensor with an identity, represented at a finite stage.
private theorem tensor_param_representative
    (L L' M : generalAlgebraicallyClosedConstructibleCategory l Ω W) (f : L' ⟶ L)
    (F : Index l Ω) (hL' : L'.stage ≤ F) (hL : L.stage ≤ F)
    (f₀ : L'.toStage hL' ⟶ L.toStage hL) (hf : f = ofHom L' L F hL' hL f₀)
    (hT' : (commonStageTensorObject l Ω W L' M).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L M).stage ≤ F)
    (e' : (commonStageDerivedTensor l Ω W).obj (L', M) = commonStageTensorObject l Ω W L' M)
    (e : (commonStageDerivedTensor l Ω W).obj (L, M) = commonStageTensorObject l Ω W L M) :
    eqToHom e'.symm ≫ (commonStageDerivedTensor l Ω W).map (Prod.mkHom f (𝟙 M)) ≫
        eqToHom e =
      ofHom (commonStageTensorObject l Ω W L' M) (commonStageTensorObject l Ω W L M) F hT' hT
        ((commonStageTensorComparison l Ω W L' M F hT').hom ≫
        (rationalDerivedTensor l (Coefficient.{u} l Ω F) W).map (Prod.mkHom f₀ (𝟙 _)) ≫
        (commonStageTensorComparison l Ω W L M F hT).inv) := by
  have hm := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.2 L' M L M F hT' hT
    f₀ (𝟙 _)
  have hid : 𝟙 M = ofHom M M F
      (((Padic.finiteCoefficientFields_properties l Ω).1 L'.stage M.stage).2.trans hT')
      (((Padic.finiteCoefficientFields_properties l Ω).1 L.stage M.stage).2.trans hT) (𝟙 _) :=
    StageSystem.PairCategory.id_eq_mkHom M _
  subst hf
  apply eq_of_heq
  exact ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans ((heq_of_eq (congrArg (fun z ↦
    (commonStageDerivedTensor l Ω W).map (Prod.mkHom (ofHom L' L F hL' hL f₀) z)) hid)).trans hm)

-- Conjugated inverse transposition is natural in the tensor parameter.
private theorem inverseTranspose_param
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (L L' : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory) (F : Index l Ω)
    (hL' : L'.stage ≤ F) (hL : L.stage ≤ F) (f₀ : L'.toStage hL' ⟶ L.toStage hL)
    (hH : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT' : (commonStageTensorObject l Ω W L' P.obj.1.unop).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F) (hN : P.obj.2.stage ≤ F)
    (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hH) :
    commonStageInverseTranspose l Ω W R L' P F hL' hH hT' hN (f₀ ≫ φ) =
      ((commonStageTensorComparison l Ω W L' P.obj.1.unop F hT').hom ≫
        (rationalDerivedTensor l (Coefficient.{u} l Ω F) W).map (Prod.mkHom f₀ (𝟙 _)) ≫
        (commonStageTensorComparison l Ω W L P.obj.1.unop F hT).inv) ≫
      commonStageInverseTranspose l Ω W R L P F hL hH hT hN φ := by
  have key := param_algebra (R F) (commonStageHomPairAtStage l Ω W P F hH) f₀ φ
    (commonStageHomComparison l Ω W P F hH)
    (commonStageTensorComparison l Ω W L' P.obj.1.unop F hT')
    (commonStageTensorComparison l Ω W L P.obj.1.unop F hT)
  exact key

/-- If the conjugated stage-level inverse transpositions of a family `R` of rational closed
data commute with the stage transitions, then there is a common-stage partial closed datum
normalized by `R`. -/
theorem commonTransposeNormalized_exists
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (htr : ∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (P : (commonStageHomPairs l Ω W).FullSubcategory) (F F' : Index l Ω) (k : F ≤ F')
      (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
      (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F) (hN : P.obj.2.stage ≤ F)
      (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP),
      (stageSystem l Ω W).tr k (commonStageInverseTranspose l Ω W R L P F hL hP hT hN φ) =
        commonStageInverseTranspose l Ω W R L P F' (hL.trans k) (hP.trans k) (hT.trans k)
          (hN.trans k) ((stageSystem l Ω W).tr k φ)) :
    ∃ S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W),
      CommonTransposeNormalized l Ω W R S := by
  have hHo : ∀ P, (commonStageDerivedInternalHom l Ω W).obj P = commonStageHomObject l Ω W P :=
    (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.1
  have hTo : ∀ L M, (commonStageDerivedTensor l Ω W).obj (L, M) =
      commonStageTensorObject l Ω W L M :=
    (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1
  have hd (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (P : (commonStageHomPairs l Ω W).FullSubcategory) :=
    StageSystem.PairCategory.homAddEquiv_descent
      (S := stageSystem l Ω W) (instP := GeneralAlgebraicallyClosedCoefficients.preadditive)
      (fun hX hY u v ↦ GeneralAlgebraicallyClosedCoefficients.mkHom_add hX hY u v)
      (commonStageInverseTranspose l Ω W R L P) (htr L P)
  choose σ hσ using hd
  have hc (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (P : (commonStageHomPairs l Ω W).FullSubcategory) :=
    homAddEquiv_conj (hTo L P.obj.1.unop) (hHo P) (σ L P)
  choose e he using hc
  refine ⟨⟨e, fun L L' P f h ↦ ?_⟩, ?_⟩
  · refine conj_parameter_naturality (hTo L P.obj.1.unop) (hTo L' P.obj.1.unop) (hHo P)
      (σ L P) (σ L' P) (e L P) (e L' P) (he L P) (he L' P) f
      ((commonStageDerivedTensor l Ω W).map (Prod.mkHom f (𝟙 _))) (fun q ↦ ?_) h
    refine StageSystem.PairCategory.homAddEquiv_descent_comp (σ L P) (σ L' P)
      (fun F hL hH hT hN ↦ commonStageInverseTranspose l Ω W R L P F hL hH hT hN)
      (fun F hL hH hT hN ↦ commonStageInverseTranspose l Ω W R L' P F hL hH hT hN)
      (hσ L P) (hσ L' P) f _ ?_ q
    intro F hL' hL f₀ hf hT' hT
    exact ⟨_, tensor_param_representative l Ω W L L' P.obj.1.unop f F hL' hL f₀ hf hT' hT
      (hTo L' _) (hTo L _), fun hH hN φ ↦ inverseTranspose_param l Ω W R L L' P F hL' hL f₀
        hH hT' hT hN φ⟩
  · intro L P F hL hP hT hN φ q hq
    exact conj_normalization (hTo L P.obj.1.unop) (hHo P) (σ L P) (e L P) (he L P) q _ hq _
      (hσ L P F hL hP hT hN φ)


/-- A common-stage partial closed datum normalized by a family of rational closed data is
unique. -/
theorem commonTransposeNormalized_unique
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (S S' : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W))
    (hS : CommonTransposeNormalized l Ω W R S) (hS' : CommonTransposeNormalized l Ω W R S') :
    S = S' := by
  have hHo : ∀ P, (commonStageDerivedInternalHom l Ω W).obj P = commonStageHomObject l Ω W P :=
    (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.1
  apply podPartialClosed_ext
  intro L P
  apply AddEquiv.symm_bijective.injective
  ext q
  obtain ⟨n₀, hL₀, hP₀, hq⟩ :=
    StageSystem.PairCategory.exists_mkHom_eq (q ≫ eqToHom (hHo P))
  obtain ⟨n₁, h₁, h₂⟩ :=
    exists_ge_ge n₀ (commonStageTensorObject l Ω W L P.obj.1.unop).stage
  obtain ⟨n, h₃, h₄⟩ := exists_ge_ge n₁ P.obj.2.stage
  obtain ⟨φ, hφ⟩ := hq n (h₁.trans h₃)
  have hq' : HEq q (ofHom L (commonStageHomObject l Ω W P) n (hL₀.trans (h₁.trans h₃))
      (hP₀.trans (h₁.trans h₃)) φ) :=
    (comp_eqToHom_heq q (hHo P)).symm.trans (heq_of_eq hφ)
  exact eq_of_heq ((hS L P n _ _ (h₂.trans h₃) h₄ φ q hq').trans
    (hS' L P n _ _ (h₂.trans h₃) h₄ φ q hq').symm)
end CommonClosed

end WeilConjectures
