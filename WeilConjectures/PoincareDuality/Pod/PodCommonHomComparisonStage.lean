/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.PoincareDuality.Pod.PodCommonClosedHomNaturality
import WeilConjectures.PoincareDuality.Derived.PodPartialHomNaturality
public import WeilConjectures.PoincareDuality.Pod.PodCommonHomComparisonIsIso
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality

/-! # Invertibility of the common-stage internal Hom comparison

For common-stage closed data normalized by finite-stage rational closed data, the
evaluation-defined internal Hom comparison for pullback is represented, at a large finite
stage, by the rational comparison conjugated by the stage comparisons. Hence it is invertible
as soon as all rational comparisons are.

## Main statements

* `commonHomComparison_isIso`: invertibility of the common-stage comparison.
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

-- The stage-level algebra identifying the transported representative with the
-- rational composite.
private theorem stage_algebra {C D : Type*} [Category C] [Category D]
    (RT : D × D ⥤ D) (RP : C ⥤ D) {TX' TXl GTY GA GM XA XM W : D} {TYn UY A₀ M₀ N₀ : C}
    (dX : TX' ≅ RT.obj (XA, XM)) (dXl : TXl ≅ RT.obj (GA, GM)) (h₁ : TX' = TXl)
    (pAT : GTY ≅ TXl) (pT : GTY ≅ RP.obj TYn) (dY : TYn ≅ UY)
    (κ : RP.obj UY ≅ RT.obj (RP.obj A₀, RP.obj M₀)) (pcA : GA ≅ RP.obj A₀)
    (pcM : GM ≅ RP.obj M₀)
    (hp : pAT = pT ≪≫ RP.mapIso dY ≪≫ κ ≪≫
      RT.mapIso (Iso.prod pcA.symm pcM.symm) ≪≫ dXl.symm)
    (α : XA ⟶ GA) (β : XM ⟶ GM)
    (hcong : dX.inv ≫ eqToHom h₁ ≫ dXl.hom = RT.map (Prod.mkHom α β))
    (s : UY ⟶ N₀) (w : RP.obj N₀ ⟶ W) :
    dX.inv ≫ eqToHom h₁ ≫ pAT.inv ≫ pT.hom ≫ RP.map (dY.hom ≫ s) ≫ w =
      RT.map (Prod.mkHom (α ≫ pcA.hom) (β ≫ pcM.hom)) ≫ κ.inv ≫ RP.map s ≫ w := by
  subst hp
  have hm : Prod.mkHom (α ≫ pcA.hom) (β ≫ pcM.hom) =
      (Prod.mkHom α β : (XA, XM) ⟶ (GA, GM)) ≫ Prod.mkHom pcA.hom pcM.hom := rfl
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.prod_inv,
    Category.assoc, Iso.inv_hom_id_assoc, ← RP.map_comp_assoc, hm, RT.map_comp]
  rw [← reassoc_of% hcong]

-- Tensor comparisons at equal pairs of objects differ by the induced transports.
private theorem tensorComparison_congr {l : ℕ} [Fact l.Prime] {Ω : Type v} [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] {W : Scheme.{u}}
    [∀ w : W, Invertible (l : W.residueField w)]
    {A₁ A₂ M₁ M₂ : generalAlgebraicallyClosedConstructibleCategory l Ω W}
    (eA : A₁ = A₂) (eM : M₁ = M₂) (n : AlgebraicallyClosedCoefficients.Index l Ω)
    (h₁ : (commonStageTensorObject l Ω W A₁ M₁).stage ≤ n)
    (h₂ : (commonStageTensorObject l Ω W A₂ M₂).stage ≤ n)
    (H : (commonStageTensorObject l Ω W A₁ M₁).toStage h₁ =
      (commonStageTensorObject l Ω W A₂ M₂).toStage h₂)
    (HA : A₁.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A₁.stage M₁.stage).1.trans h₁) =
      A₂.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1 A₂.stage M₂.stage).1.trans h₂))
    (HM : M₁.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        A₁.stage M₁.stage).2.trans h₁) =
      M₂.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1 A₂.stage M₂.stage).2.trans h₂)) :
    (commonStageTensorComparison l Ω W A₁ M₁ n h₁).inv ≫ eqToHom H ≫
        (commonStageTensorComparison l Ω W A₂ M₂ n h₂).hom =
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω n) W).map
        (Prod.mkHom (eqToHom HA) (eqToHom HM)) := by
  subst eA eM
  simp only [eqToHom_refl, Category.id_comp, Iso.inv_hom_id]
  exact ((rationalDerivedTensor l _ W).map_id _).symm

section CommonTransport
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

-- The inverse rational pullback/tensor comparison is natural in the first variable.
private theorem canonicalRationalPullbackTensor_inv_naturality (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L L' M : sfRationalConstructibleCategory l E Y) (t : L' ⟶ L) :
    (rationalDerivedTensor l E X).map
        (Prod.mkHom ((rationalDerivedPullback l E g).map t) (𝟙 _)) ≫
      (canonicalRationalPullbackTensor l E g L M).inv =
    (canonicalRationalPullbackTensor l E g L' M).inv ≫
      (rationalDerivedPullback l E g).map
        ((rationalDerivedTensor l E Y).map (Prod.mkHom t (𝟙 _))) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  simpa using (canonicalRationalPullbackTensor_naturality l E g t (𝟙 M)).symm

-- The stage-level transpose representing the common-stage comparison is invertible.
private theorem stage_isIso
    (RY : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) Y)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) Y)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) Y))
    (RX : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) X)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) X)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X))
    (hrp : ∀ (F : Index l Ω)
      (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) Y).FullSubcategory),
      constructibleRationalHomPairs l (Coefficient.{u} l Ω F) X
        (((rationalDerivedPullback l (Coefficient.{u} l Ω F) g).op.prod
          (rationalDerivedPullback l (Coefficient.{u} l Ω F) g)).obj P.obj))
    (hRX : ∀ (F : Index l Ω) (L : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) X)
      (P Q : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) X).FullSubcategory)
      (h : P ⟶ Q) (φ : L ⟶ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X).obj P),
      ((RX F).transpose L Q).symm
          (φ ≫ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X).map h) =
        (rationalDerivedTensor l (Coefficient.{u} l Ω F) X).map
            (Prod.mkHom (𝟙 L) h.hom.1.unop) ≫
          ((RX F).transpose L P).symm φ ≫ h.hom.2)
    (hRiso : ∀ (F : Index l Ω)
      (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) Y).FullSubcategory),
      IsIso (podPartialHomComparison (RY F) (RX F)
        (rationalDerivedPullback l (Coefficient.{u} l Ω F) g) (hrp F)
        (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω F) g) P))
    (hp : ∀ P : (commonStageHomPairs l Ω Y).FullSubcategory,
      commonStageHomPairs l Ω X
        (((commonStageDerivedPullback l Ω g).op.prod
          (commonStageDerivedPullback l Ω g)).obj P.obj))
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) (n : Index l Ω)
    (hTY : (commonStageTensorObject l Ω Y
      ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop).stage ≤ n)
    (hA' : (commonStageHomObject l Ω Y P).stage ≤ n)
    (hXH : (commonStageHomObject l Ω X
      ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P)).stage ≤ n)
    (h₆ : (commonStageTensorObject l Ω X
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop)).stage ≤ n)
    (hA : ((commonStageDerivedInternalHom l Ω Y).obj P).stage ≤ n)
    (hN : P.obj.2.stage ≤ n)
    (hXA : ((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω Y).obj P)).stage ≤ n)
    (hXN : ((commonStageDerivedPullback l Ω g).obj P.obj.2).stage ≤ n)
    (eHA : (commonStageDerivedInternalHom l Ω Y).obj P = commonStageHomObject l Ω Y P)
    (hGo : ∀ Q, (commonStageDerivedPullback l Ω g).obj Q = commonStagePullbackObject l Ω g Q)
    (eTXl : commonStageTensorObject l Ω X
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop) =
    commonStageTensorObject l Ω X
      (commonStagePullbackObject l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P))
      (commonStagePullbackObject l Ω g P.obj.1.unop)) :
    IsIso (((RX n).transpose (((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω Y).obj P)).toStage hXA)
      (commonStageHomPairAtStage l Ω X
        ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P) n hXH)).toEquiv
      ((commonStageTensorComparison l Ω X
          ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
          ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop) n h₆).inv ≫
        eqToHom (StageSystem.PairCategory.toStage_congr eTXl h₆ hTY) ≫
        (pullbackTensorAtCommonStage l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P)
          P.obj.1.unop n hTY).inv ≫
        (commonStagePullbackComparison l Ω g (commonStageTensorObject l Ω Y
          ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop) n hTY).hom ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω n) g).map
          ((commonStageTensorComparison l Ω Y ((commonStageDerivedInternalHom l Ω Y).obj P)
            P.obj.1.unop n hTY).hom ≫
          ((RY n).transpose (((commonStageDerivedInternalHom l Ω Y).obj P).toStage hA)
            (commonStageHomPairAtStage l Ω Y P n hA')).symm
            (eqToHom (StageSystem.PairCategory.toStage_congr eHA hA hA') ≫
              (commonStageHomComparison l Ω Y P n hA').hom)) ≫
        (commonStagePullbackComparison l Ω g P.obj.2 n hN).inv ≫
        eqToHom (StageSystem.PairCategory.toStage_congr (hGo P.obj.2).symm hN hXN))) := by
  have hcong := tensorComparison_congr (hGo ((commonStageDerivedInternalHom l Ω Y).obj P))
    (hGo P.obj.1.unop) n h₆ hTY (StageSystem.PairCategory.toStage_congr eTXl h₆ hTY)
    (StageSystem.PairCategory.toStage_congr (hGo _) _ _)
    (StageSystem.PairCategory.toStage_congr (hGo _) _ _)
  rw [stage_algebra (rationalDerivedTensor l (Coefficient.{u} l Ω n) X)
    (rationalDerivedPullback l (Coefficient.{u} l Ω n) g)
    (commonStageTensorComparison l Ω X
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop) n h₆)
    (commonStageTensorComparison l Ω X
      (commonStagePullbackObject l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P))
      (commonStagePullbackObject l Ω g P.obj.1.unop) n hTY) _
    (pullbackTensorAtCommonStage l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P)
      P.obj.1.unop n hTY)
    (commonStagePullbackComparison l Ω g (commonStageTensorObject l Ω Y
      ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop) n hTY)
    (commonStageTensorComparison l Ω Y ((commonStageDerivedInternalHom l Ω Y).obj P)
      P.obj.1.unop n hTY)
    (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω n) g _ _)
    (commonStagePullbackComparison l Ω g _ n
      (((Padic.finiteCoefficientFields_properties l Ω).1 _ _).1.trans hTY))
    (commonStagePullbackComparison l Ω g _ n
      (((Padic.finiteCoefficientFields_properties l Ω).1 _ _).2.trans hTY)) rfl _ _ hcong]
  exact podPartialHomComparison_transpose_isIso (RY n) (RX n)
    (rationalDerivedPullback l (Coefficient.{u} l Ω n) g) (hrp n)
    (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω n) g) (hRX n)
    (canonicalRationalPullbackTensor_inv_naturality l g (Coefficient.{u} l Ω n))
    (commonStageHomPairAtStage l Ω Y P n hA')
    (((commonStageDerivedInternalHom l Ω Y).obj P).toStage hA)
    (eqToIso (StageSystem.PairCategory.toStage_congr eHA hA hA') ≪≫
      commonStageHomComparison l Ω Y P n hA')
    (((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω Y).obj P)).toStage hXA)
    (eqToIso (StageSystem.PairCategory.toStage_congr (hGo _) _ _) ≪≫
      commonStagePullbackComparison l Ω g _ n
        (((Padic.finiteCoefficientFields_properties l Ω).1 _ _).1.trans hTY))
    (commonStageHomPairAtStage l Ω X
      ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P) n hXH)
    (ObjectProperty.isoMk _ (Iso.prod
      (eqToIso (StageSystem.PairCategory.toStage_congr (hGo _) _ _) ≪≫
        commonStagePullbackComparison l Ω g _ n
          (((Padic.finiteCoefficientFields_properties l Ω).1 _ _).2.trans hTY)).op
      ((commonStagePullbackComparison l Ω g P.obj.2 n hN).symm ≪≫
        eqToIso (StageSystem.PairCategory.toStage_congr (hGo P.obj.2).symm hN hXN))))
    (hRiso n _)

/-- The evaluation-defined common-stage internal Hom comparison for pullback is invertible,
for common-stage closed data normalized by finite-stage rational closed data whose own
comparisons are invertible and whose inverse transpositions are natural in the Hom pair. -/
theorem commonHomComparison_isIso
    (RY : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) Y)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) Y)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) Y))
    (RX : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) X)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) X)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X))
    (hrp : ∀ (F : Index l Ω)
      (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) Y).FullSubcategory),
      constructibleRationalHomPairs l (Coefficient.{u} l Ω F) X
        (((rationalDerivedPullback l (Coefficient.{u} l Ω F) g).op.prod
          (rationalDerivedPullback l (Coefficient.{u} l Ω F) g)).obj P.obj))
    (hRX : ∀ (F : Index l Ω) (L : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) X)
      (P Q : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) X).FullSubcategory)
      (h : P ⟶ Q) (φ : L ⟶ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X).obj P),
      ((RX F).transpose L Q).symm
          (φ ≫ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X).map h) =
        (rationalDerivedTensor l (Coefficient.{u} l Ω F) X).map
            (Prod.mkHom (𝟙 L) h.hom.1.unop) ≫
          ((RX F).transpose L P).symm φ ≫ h.hom.2)
    (hRiso : ∀ (F : Index l Ω)
      (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) Y).FullSubcategory),
      IsIso (podPartialHomComparison (RY F) (RX F)
        (rationalDerivedPullback l (Coefficient.{u} l Ω F) g) (hrp F)
        (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω F) g) P))
    (SY : PodPartialClosed (commonStageDerivedTensor l Ω Y)
      (commonStageHomPairs l Ω Y) (commonStageDerivedInternalHom l Ω Y))
    (SX : PodPartialClosed (commonStageDerivedTensor l Ω X)
      (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X))
    (hSY : CommonTransposeNormalized l Ω Y RY SY) (hSX : CommonTransposeNormalized l Ω X RX SX)
    (hp : ∀ P : (commonStageHomPairs l Ω Y).FullSubcategory,
      commonStageHomPairs l Ω X
        (((commonStageDerivedPullback l Ω g).op.prod
          (commonStageDerivedPullback l Ω g)).obj P.obj))
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    IsIso (podPartialHomComparison SY SX (commonStageDerivedPullback l Ω g) hp
      (canonicalCommonStagePullbackTensor l Ω g) P) := by
  have hHoY := (commonStageDerivedInternalHom_existsUnique l Ω Y).exists.choose_spec.1
  have hHoX := (commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1
  have hToY := (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1
  have hToX := (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1
  have hGo : ∀ Q,
      (commonStageDerivedPullback l Ω g).obj Q = commonStagePullbackObject l Ω g Q :=
    (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1
  have hGm := (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.2
  have hc := Padic.finiteCoefficientFields_properties l Ω
  obtain ⟨n₁, h₁, h₂⟩ := exists_ge_ge (commonStageTensorObject l Ω Y
    ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop).stage
    (commonStageHomObject l Ω Y P).stage
  obtain ⟨n₂, h₃, h₄⟩ := exists_ge_ge n₁ (commonStageHomObject l Ω X
    ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P)).stage
  obtain ⟨n, h₅, h₆⟩ := exists_ge_ge n₂ (commonStageTensorObject l Ω X
    ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
    ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop)).stage
  have hTY := h₁.trans (h₃.trans h₅)
  have hA' := h₂.trans (h₃.trans h₅)
  have hXH := h₄.trans h₅
  have hA := (hc.1 ((commonStageDerivedInternalHom l Ω Y).obj P).stage
    P.obj.1.unop.stage).1.trans hTY
  have hN := (hc.1 P.obj.1.unop.stage P.obj.2.stage).2.trans hA'
  have hXA := (hc.1 ((commonStageDerivedPullback l Ω g).obj
    ((commonStageDerivedInternalHom l Ω Y).obj P)).stage
    ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop).stage).1.trans h₆
  have hXN := (hc.1 ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop).stage
    ((commonStageDerivedPullback l Ω g).obj P.obj.2).stage).2.trans hXH
  have eTXl : commonStageTensorObject l Ω X
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop) =
    commonStageTensorObject l Ω X
      (commonStagePullbackObject l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P))
      (commonStagePullbackObject l Ω g P.obj.1.unop) := by
    rw [hGo, hGo]
  refine StageSystem.PairCategory.isIso_transpose_of_representatives
    (commonStageDerivedPullback l Ω g)
    (n := n) (A := (commonStageDerivedInternalHom l Ω Y).obj P)
    (A' := commonStageHomObject l Ω Y P) (N := P.obj.2)
    (TY := (commonStageDerivedTensor l Ω Y).obj
      ((commonStageDerivedInternalHom l Ω Y).obj P, P.obj.1.unop))
    (TY' := commonStageTensorObject l Ω Y ((commonStageDerivedInternalHom l Ω Y).obj P)
      P.obj.1.unop)
    (RHY := (rationalDerivedInternalHom l (Coefficient.{u} l Ω n) Y).obj
      (commonStageHomPairAtStage l Ω Y P n hA'))
    (UY := (rationalDerivedTensor l (Coefficient.{u} l Ω n) Y).obj
      (((commonStageDerivedInternalHom l Ω Y).obj P).toStage hA,
        P.obj.1.unop.toStage ((hc.1 _ _).2.trans hTY)))
    (XH := (commonStageDerivedInternalHom l Ω X).obj
      ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P))
    (XH' := commonStageHomObject l Ω X
      ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P))
    (TX := (commonStageDerivedTensor l Ω X).obj
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P),
        (commonStageDerivedPullback l Ω g).obj P.obj.1.unop))
    (TX' := commonStageTensorObject l Ω X
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop))
    (TXl := commonStageTensorObject l Ω X
      (commonStagePullbackObject l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P))
      (commonStagePullbackObject l Ω g P.obj.1.unop))
    (GTY := commonStagePullbackObject l Ω g (commonStageTensorObject l Ω Y
      ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop))
    (GN := commonStagePullbackObject l Ω g P.obj.2)
    (RHX := (rationalDerivedInternalHom l (Coefficient.{u} l Ω n) X).obj
      (commonStageHomPairAtStage l Ω X
        ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P) n hXH))
    (UX := (rationalDerivedTensor l (Coefficient.{u} l Ω n) X).obj
      (((commonStageDerivedPullback l Ω g).obj
        ((commonStageDerivedInternalHom l Ω Y).obj P)).toStage hXA,
        ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop).toStage ((hc.1 _ _).2.trans h₆)))
    (RP := rationalDerivedPullback l (Coefficient.{u} l Ω n) g)
    (hHoY P) (hToY ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop) hA hA' hTY hN
    (commonStageHomComparison l Ω Y P n hA')
    (commonStageTensorComparison l Ω Y ((commonStageDerivedInternalHom l Ω Y).obj P)
      P.obj.1.unop n hTY)
    ((RY n).transpose (((commonStageDerivedInternalHom l Ω Y).obj P).toStage hA)
      (commonStageHomPairAtStage l Ω Y P n hA')).symm
    (SY.transpose ((commonStageDerivedInternalHom l Ω Y).obj P) P).symm
    (fun ψ q hq ↦ hSY _ P n hA hA' hTY hN ψ q hq)
    (hHoX ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P))
    (hToX _ _) eTXl (hGo _) (hGo _) hXA hXH h₆ hTY hTY hN hXN
    (commonStageHomComparison l Ω X
      ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P) n hXH)
    (commonStageTensorComparison l Ω X
      ((commonStageDerivedPullback l Ω g).obj ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop) n h₆)
    ((RX n).transpose (((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω Y).obj P)).toStage hXA)
      (commonStageHomPairAtStage l Ω X
        ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P) n hXH)).toEquiv
    (SX.transpose ((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω Y).obj P))
      ((podPairPullback (commonStageDerivedPullback l Ω g) _ _ hp).obj P)).toEquiv
    (fun ψ q hq ↦ hSX _ _ n hXA hXH h₆ hXN ψ q hq)
    (canonicalCommonStagePullbackTensor l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P)
      P.obj.1.unop)
    (pullbackTensorAtCommonStage l Ω g ((commonStageDerivedInternalHom l Ω Y).obj P)
      P.obj.1.unop n hTY)
    ((canonicalCommonStagePullbackTensor_existsUnique l Ω g
      ((commonStageDerivedInternalHom l Ω Y).obj P) P.obj.1.unop).exists.choose_spec n hTY)
    (commonStagePullbackComparison l Ω g _ n hTY) (commonStagePullbackComparison l Ω g _ n hN)
    (fun u ↦ hGm _ _ n hTY hN u)
    (StageSystem.PairCategory.toStage_congr eTXl _ _)
    (StageSystem.PairCategory.toStage_congr (hHoY P) _ _)
    (StageSystem.PairCategory.toStage_congr (hGo _).symm _ _) ?_
  exact stage_isIso l Ω g RY RX hrp hRX hRiso hp P n hTY hA' hXH h₆ hA hN hXA hXN (hHoY P) hGo
    eTXl

end CommonTransport

end WeilConjectures
