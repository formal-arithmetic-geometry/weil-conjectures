/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationBase
import WeilConjectures.SmoothPurity.CommonStageInternalHomDescent.CommonStageInternalHomDescent

/-! # Naturality of common-stage inverse transposition in the Hom pair

A partial closed datum on the algebraically closed common-stage category whose inverse
transposition is given, at every large finite stage, by finite-stage rational transpositions
conjugated by the stage comparisons, has inverse transposition natural in the permitted
Hom pair as soon as the finite-stage transpositions do.

## Main definitions

* `CommonTransposeNormalized`: the representative normalization of a common-stage closed
  datum by a family of finite-stage rational closed data.

## Main statements

* `commonClosed_symm_comp_map`: naturality of normalized inverse transposition in the
  permitted Hom pair.
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

-- The stage-level identity behind naturality of normalized inverse transposition.
private theorem stage_equation {C : Type*} [Category C]
    {L H₁ H₂ R₁ R₂ T₁ T₂ U₁ U₂ N₁ N₂ : C}
    (φ : L ⟶ H₁) (c₁ : H₁ ≅ R₁) (c₂ : H₂ ≅ R₂) (m : R₁ ⟶ R₂)
    (d₂ : T₂ ≅ U₂) (d₁ : T₁ ≅ U₁) (t : U₂ ⟶ U₁) (b : N₁ ⟶ N₂)
    (s₂ : (L ⟶ R₂) → (U₂ ⟶ N₂)) (s₁ : (L ⟶ R₁) → (U₁ ⟶ N₁))
    (hs : ∀ ψ, s₂ (ψ ≫ m) = t ≫ s₁ ψ ≫ b) :
    d₂.hom ≫ s₂ ((φ ≫ c₁.hom ≫ m ≫ c₂.inv) ≫ c₂.hom) =
      (d₂.hom ≫ t ≫ d₁.inv) ≫ (d₁.hom ≫ s₁ (φ ≫ c₁.hom)) ≫ b := by
  have h : (φ ≫ c₁.hom ≫ m ≫ c₂.inv) ≫ c₂.hom = (φ ≫ c₁.hom) ≫ m := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, hs]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]


-- Naturality of normalized inverse transposition, in an arbitrary stage system.
private theorem pair_symm_comp_map {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (𝒮 : StageSystem C) {n : I}
    {L HP HQ TQ TP N₁ N₂ HP' HQ' TQ' TP' : 𝒮.PairCategory}
    (eP : HP = HP') (eQ : HQ = HQ') (eTQ : TQ = TQ') (eTP : TP = TP')
    (hL : L.stage ≤ n) (hP : HP'.stage ≤ n) (hQ : HQ'.stage ≤ n) (hTQ : TQ'.stage ≤ n)
    (hTP : TP'.stage ≤ n) (h₁ : N₁.stage ≤ n) (h₂ : N₂.stage ≤ n)
    {RP RQ UQ UP : C n}
    (cP : HP'.toStage hP ≅ RP) (cQ : HQ'.toStage hQ ≅ RQ) (m : RP ⟶ RQ)
    (dQ : TQ'.toStage hTQ ≅ UQ) (dP : TP'.toStage hTP ≅ UP) (τ : UQ ⟶ UP)
    (b : N₁.toStage h₁ ⟶ N₂.toStage h₂)
    (rQ : (L.toStage hL ⟶ RQ) → (UQ ⟶ N₂.toStage h₂))
    (rP : (L.toStage hL ⟶ RP) → (UP ⟶ N₁.toStage h₁))
    (hr : ∀ ψ, rQ (ψ ≫ m) = τ ≫ rP ψ ≫ b)
    (sQ : (L ⟶ HQ) → (TQ ⟶ N₂)) (sP : (L ⟶ HP) → (TP ⟶ N₁))
    (hsQ : ∀ (ψ : L.toStage hL ⟶ HQ'.toStage hQ) (q : L ⟶ HQ),
      HEq q (StageSystem.PairCategory.mkHom n hL hQ ψ) →
        HEq (sQ q) (StageSystem.PairCategory.mkHom n hTQ h₂ (dQ.hom ≫ rQ (ψ ≫ cQ.hom))))
    (hsP : ∀ (ψ : L.toStage hL ⟶ HP'.toStage hP) (q : L ⟶ HP),
      HEq q (StageSystem.PairCategory.mkHom n hL hP ψ) →
        HEq (sP q) (StageSystem.PairCategory.mkHom n hTP h₁ (dP.hom ≫ rP (ψ ≫ cP.hom))))
    (φ : L ⟶ HP) (φ₀ : L.toStage hL ⟶ HP'.toStage hP)
    (hφ : HEq φ (StageSystem.PairCategory.mkHom n hL hP φ₀))
    (g : HP ⟶ HQ) (hg : HEq g (StageSystem.PairCategory.mkHom n hP hQ (cP.hom ≫ m ≫ cQ.inv)))
    (t t₀ : TQ ⟶ TP) (htt : t = t₀)
    (ht : HEq t₀ (StageSystem.PairCategory.mkHom n hTQ hTP (dQ.hom ≫ τ ≫ dP.inv))) :
    sQ (φ ≫ g) = t ≫ sP φ ≫ StageSystem.PairCategory.mkHom n h₁ h₂ b := by
  subst eP eQ eTQ eTP htt
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq ht
  rw [StageSystem.PairCategory.mkHom_comp_mkHom,
    eq_of_heq (hsQ _ _ HEq.rfl), eq_of_heq (hsP _ _ HEq.rfl),
    StageSystem.PairCategory.mkHom_comp_mkHom, StageSystem.PairCategory.mkHom_comp_mkHom]
  exact congrArg (StageSystem.PairCategory.mkHom n hTQ h₂)
    (stage_equation φ₀ cP cQ m dQ dP τ b rQ rP hr)
end Abstract

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar
attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  rationalDerivedInternalHom ScalarLocalization.composition
attribute [local irreducible] commonStageHomComparison commonStageTensorComparison

section CommonClosed
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- A common-stage closed datum is normalized by a family `R` of finite-stage rational
closed data if, at every finite stage containing the entries, inverse transposition is the
stage rational inverse transposition conjugated by the stage comparisons. -/
def CommonTransposeNormalized
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W)) : Prop :=
  ∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F)
    (hN : P.obj.2.stage ≤ F)
    (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP)
    (q : L ⟶ (commonStageDerivedInternalHom l Ω W).obj P),
    HEq q (ofHom L (commonStageHomObject l Ω W P) F hL hP φ) →
    HEq ((S.transpose L P).symm q)
      (ofHom (commonStageTensorObject l Ω W L P.obj.1.unop) P.obj.2 F hT hN
        ((commonStageTensorComparison l Ω W L P.obj.1.unop F hT).hom ≫
          ((R F).transpose (L.toStage hL)
            (commonStageHomPairAtStage l Ω W P F hP)).symm
              (φ ≫ (commonStageHomComparison l Ω W P F hP).hom)))

/-- Inverse transposition of a normalized common-stage closed datum is natural in the
permitted Hom pair, provided each finite-stage rational transposition is. -/
theorem commonClosed_symm_comp_map
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (hR : ∀ (F : Index l Ω) (L : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) W)
      (P Q : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W).FullSubcategory)
      (h : P ⟶ Q) (φ : L ⟶ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W).obj P),
      ((R F).transpose L Q).symm
          (φ ≫ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W).map h) =
        (rationalDerivedTensor l (Coefficient.{u} l Ω F) W).map
            (Prod.mkHom (𝟙 L) h.hom.1.unop) ≫
          ((R F).transpose L P).symm φ ≫ h.hom.2)
    (S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W))
    (hS : CommonTransposeNormalized l Ω W R S)
    (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P Q : (commonStageHomPairs l Ω W).FullSubcategory) (f : P ⟶ Q)
    (φ : L ⟶ (commonStageDerivedInternalHom l Ω W).obj P) :
    (S.transpose L Q).symm (φ ≫ (commonStageDerivedInternalHom l Ω W).map f) =
      (commonStageDerivedTensor l Ω W).map (Prod.mkHom (𝟙 L) f.hom.1.unop) ≫
        (S.transpose L P).symm φ ≫ f.hom.2 := by
  have hHo := (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.1
  have hHm := (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.2
  have hTo := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1
  have hTm := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.2
  obtain ⟨n₀, hL₀, hP₀, hφ⟩ :=
    StageSystem.PairCategory.exists_mkHom_eq (φ ≫ eqToHom (hHo P))
  obtain ⟨N₁, h₁, h₂⟩ :=
    exists_ge_ge n₀ (commonStageTensorObject l Ω W L Q.obj.1.unop).stage
  obtain ⟨N, h₃, h₄⟩ :=
    exists_ge_ge N₁ (commonStageTensorObject l Ω W L P.obj.1.unop).stage
  obtain ⟨n, hNn, hP, hQ, a, b, rfl⟩ :=
    CommonStageInternalHomDescent.homRepresentative_exists l Ω W P Q f N
  obtain ⟨φ₀, hφ₀⟩ := hφ n (h₁.trans (h₃.trans hNn))
  have hL : L.stage ≤ n := hL₀.trans (h₁.trans (h₃.trans hNn))
  have hT : (commonStageTensorObject l Ω W L Q.obj.1.unop).stage ≤ n :=
    h₂.trans (h₃.trans hNn)
  have hT' : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ n := h₄.trans hNn
  have hN : Q.obj.2.stage ≤ n :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 Q.obj.1.unop.stage Q.obj.2.stage).2.trans hQ
  have hN' : P.obj.2.stage ≤ n :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 P.obj.1.unop.stage P.obj.2.stage).2.trans hP
  have hφ' : HEq φ (ofHom L (commonStageHomObject l Ω W P) n hL hP φ₀) :=
    (comp_eqToHom_heq φ (hHo P)).symm.trans (heq_of_eq hφ₀)
  have ht := hTm L Q.obj.1.unop L P.obj.1.unop n hT hT' (𝟙 _) a
  have hid : (commonStageDerivedTensor l Ω W).map (Prod.mkHom (𝟙 L)
      (CommonStageInternalHom.input l Ω W P Q n hP hQ a b).hom.1.unop) =
    (commonStageDerivedTensor l Ω W).map (Prod.mkHom (ofHom L L n
      (((Padic.finiteCoefficientFields_properties l Ω).1 L.stage Q.obj.1.unop.stage).1.trans hT)
      (((Padic.finiteCoefficientFields_properties l Ω).1 L.stage Q.obj.1.unop.stage).1.trans hT)
      (𝟙 _)) (CommonStageInternalHom.input l Ω W P Q n hP hQ a b).hom.1.unop) := by
    exact congrArg (fun z ↦ (commonStageDerivedTensor l Ω W).map (Prod.mkHom z _))
      (StageSystem.PairCategory.id_eq_mkHom L _)
  exact pair_symm_comp_map (stageSystem l Ω W) (n := n) (L := L)
    (HP := (commonStageDerivedInternalHom l Ω W).obj P)
    (HQ := (commonStageDerivedInternalHom l Ω W).obj Q)
    (TQ := (commonStageDerivedTensor l Ω W).obj (L, Q.obj.1.unop))
    (TP := (commonStageDerivedTensor l Ω W).obj (L, P.obj.1.unop))
    (N₁ := P.obj.2) (N₂ := Q.obj.2) (HP' := commonStageHomObject l Ω W P)
    (HQ' := commonStageHomObject l Ω W Q) (TQ' := commonStageTensorObject l Ω W L Q.obj.1.unop)
    (TP' := commonStageTensorObject l Ω W L P.obj.1.unop)
    (RP := (rationalDerivedInternalHom l (Coefficient.{u} l Ω n) W).obj
      (commonStageHomPairAtStage l Ω W P n hP))
    (RQ := (rationalDerivedInternalHom l (Coefficient.{u} l Ω n) W).obj
      (commonStageHomPairAtStage l Ω W Q n hQ))
    (UQ := (rationalDerivedTensor l (Coefficient.{u} l Ω n) W).obj (L.toStage hL,
      Q.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        L.stage Q.obj.1.unop.stage).2.trans hT)))
    (UP := (rationalDerivedTensor l (Coefficient.{u} l Ω n) W).obj (L.toStage hL,
      P.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        L.stage P.obj.1.unop.stage).2.trans hT')))
    (hHo P) (hHo Q)
    (hTo L Q.obj.1.unop) (hTo L P.obj.1.unop) hL hP hQ hT hT' hN' hN
    (commonStageHomComparison l Ω W P n hP) (commonStageHomComparison l Ω W Q n hQ)
    ((rationalDerivedInternalHom l (Coefficient.{u} l Ω n) W).map
      (ObjectProperty.homMk
        (X := commonStageHomPairAtStage l Ω W P n hP)
        (Y := commonStageHomPairAtStage l Ω W Q n hQ) (Prod.mkHom a.op b)))
    (commonStageTensorComparison l Ω W L Q.obj.1.unop n hT)
    (commonStageTensorComparison l Ω W L P.obj.1.unop n hT')
    ((rationalDerivedTensor l (Coefficient.{u} l Ω n) W).map (Prod.mkHom (𝟙 _) a)) b
    ((R n).transpose (L.toStage hL) (commonStageHomPairAtStage l Ω W Q n hQ)).symm
    ((R n).transpose (L.toStage hL) (commonStageHomPairAtStage l Ω W P n hP)).symm
    (fun ψ ↦ hR n _ _ _ _ ψ) (S.transpose L Q).symm (S.transpose L P).symm
    (fun ψ q hq ↦ hS L Q n hL hQ hT hN ψ q hq) (fun ψ q hq ↦ hS L P n hL hP hT' hN' ψ q hq)
    φ φ₀ hφ' ((commonStageDerivedInternalHom l Ω W).map
      (CommonStageInternalHom.input l Ω W P Q n hP hQ a b)) (hHm P Q n hP hQ a b) _ _ hid ht
end CommonClosed

end WeilConjectures
