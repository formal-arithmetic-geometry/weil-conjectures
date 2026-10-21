/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.PbcActualRingedExchange
import Sheaf.Paper.PbcConstructibleReductionPullback
import Sheaf.Paper.PbcConstructibleReductionCriterion
import Sheaf.Paper.PbcUniformReductionCriterion

/-! # Completed pullback on the actual common-stage Qbar category

Source: Stacks Tag 099N (2),(5); Bhatt--Scholze, Section 6.8, Remark 6.8.15
(blueprint: def-weil-pbc-completed-pullback).
The published strict-tower pullback is retained. Its integral restriction and the
normalized completed scalar comparisons descend it to the existing pair category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- Restriction of the actual completed pullback to the integral constructible objects.
Source: BS 6.8.2 and Remark 6.8.15; Stacks 099N
(blueprint: def-weil-pbc-completed-pullback).
Proof: take finite reductions of a K-flat integral representative. The strict-tower
comparison identifies the reductions of completed pullback with exact finite-level
inverse image. Pull back the finite constructible stratification and its etale-origin
witnesses. Boundedness is unchanged by exact finite inverse image, and the tower
construction gives intrinsic completeness. These verify each defining integral
constructibility condition. No nonemptiness or base-field invertibility is used. -/
theorem pbcQbarIntegralPull_mem (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω Y E) :
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
      ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj) := by
  let E' := pbcFiniteField.{u} l Ω E
  let d := pbcIntegralDatum l E'
  obtain ⟨a, b, hp⟩ := (pbcUniformReductionCriterion l E' Y K.obj).mp
    ⟨K.property.2.1, K.property.2.2⟩
  have hb : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction Y d n).obj K.obj)) := by
    intro n q hq
    let R := pbcRestrict (pbcLevelConstantComparison Y d n).hom
    have := (hp n).1
    have := (hp n).2.1
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcConstantReduction Y d n).obj K.obj)) := by
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq
      · exact DerivedCategory.isZero_of_isLE _ b q hq
    have hz' := hz.of_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app
      ((pbcCompletedReduction Y d n).obj K.obj))
    have : R.Faithful := by
      constructor
      intro M N α β h
      apply SheafOfModules.Hom.ext
      exact (PresheafOfModules.restrictScalars _).map_injective
        (congrArg SheafOfModules.Hom.val h)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply R.map_injective
    simpa using (IsZero.iff_id_eq_zero _).mp hz'
  obtain ⟨hc, hcons, hbounds⟩ := pbc_constructible_reduction_pullback l E' f a b K.obj
    K.property.1 (fun n ↦ (hp n).2.2) hb
  have hstrict := (pbc_constructible_reduction_criterion l E' X a b _ hbounds).mpr
    ⟨hc, hcons⟩
  let e := (pbcActualCompletedPullback_tower d f).exists.choose.app
    ⟨K.obj, K.property.1⟩
  let := (pbcIntegralUniformComplete_isTriangulated l E' X dX.out iX.out).1
  exact ObjectProperty.prop_of_iso _ e hstrict

/-- The coherent pullback family is fixed by the actual integral pullback and the
normalized scalar comparison; in particular no arbitrary natural isomorphism is chosen.
Source: BS Remark 6.8.15; Stacks 099N
(blueprint: def-weil-pbc-completed-pullback).
Proof: restrict completed pullback by pbcQbarIntegralPull_mem and rationalize its
coefficient-linear maps. The inverse of the localized completed scalar comparison
is the beta map of this family. Its tensor-unit and associator equations give the
coherent-family equations, including repeated fields. PbcPullbackBetaSpec fixes
these components on every integral representative and rationalization fixes all
fraction arrows, so the specified finite-stage functors and beta maps are unique. -/
theorem pbcQbarPullFamily_existsUnique :
    ∃! F : StageSystem.Morphism
        (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        F.Φ E = pbcDescentPullback l Ω f (pbcQbarIntegralPull_mem l Ω f) E) ∧
      PbcPullbackBetaSpec l Ω f (pbcQbarIntegralPull_mem l Ω f) F := by
  let h := pbcQbarIntegralPull_mem l Ω f
  have hunique
      (h : ∀ E : Padic.FiniteCoefficientFields l Ω,
        ∀ K : pbcIntegralStage l Ω Y E,
          PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
            ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj))
      {F G : StageSystem.Morphism
          (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out)}
      (hF : (∀ E : Padic.FiniteCoefficientFields l Ω,
          F.Φ E = pbcDescentPullback l Ω f h E) ∧ PbcPullbackBetaSpec l Ω f h F)
      (hG : (∀ E : Padic.FiniteCoefficientFields l Ω,
          G.Φ E = pbcDescentPullback l Ω f h E) ∧ PbcPullbackBetaSpec l Ω f h G) :
      F = G := by
    rcases F with ⟨Φ, β, coh⟩
    rcases G with ⟨Ψ, γ, coh'⟩
    have e : Φ = Ψ := funext fun E ↦ (hF.1 E).trans (hG.1 E).symm
    cases e
    have eβ : @β = @γ := by
      funext E F hEF
      apply Iso.ext_inv
      apply NatTrans.ext
      funext K
      rcases K with ⟨K⟩
      have e₁ := hF.2 hEF (hF.1 E) (hF.1 F) K
      have e₂ := hG.2 hEF (hF.1 E) (hF.1 F) K
      have ee := eq_of_heq (e₁.trans e₂.symm)
      simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.assoc] at ee
      apply (cancel_epi _).mp at ee
      apply (cancel_epi _).mp at ee
      apply (cancel_mono _).mp at ee
      exact ee
    cases eβ
    rfl
  have hid (Z : Scheme.{u}) [IsNoetherian Z]
      (hd : ∃ n : ℕ, topologicalKrullDim Z ≤ (n : WithBot ℕ∞))
      (hi : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
      (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Z E) :
      PbcIsBoundedConstructibleComplete Z (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush (𝟙 Z) (pbcStageDatum.{u} l Ω E)).obj K.obj) := by
    let := (pbcIntegralUniformComplete_isTriangulated l (pbcFiniteField.{u} l Ω E)
      Z hd hi).1
    exact ObjectProperty.prop_of_iso _
      ((pbcActualDerivedDirectIdIso (pbcStageDatum.{u} l Ω E) Z).app K.obj).symm
      K.property
  let sq : ChosenCartesianSquare f (𝟙 X) (𝟙 Y) f :=
    { w := by simp
      isoPullback := (asIso (pullback.snd (𝟙 Y) f)).symm
      hom_fst := by simp
      hom_snd := by simp }
  obtain ⟨Rf, Rf', Lg, Lg', hRf, hRf', hLg, hLg', hβRf, hβRf', hβLg, rest⟩ :=
    pbcDescentOperations l Ω Y Y X X (𝟙 Y) (𝟙 X) f f sq
      (hid Y dY.out iY.out) (hid X dX.out iX.out) h h
  refine ⟨Lg.base, ⟨hLg, hβLg⟩, ?_⟩
  intro G hG
  exact hunique h hG ⟨hLg, hβLg⟩

/-- The unique normalized common-stage family of actual completed pullbacks.
Source: BS Remark 6.8.15 (blueprint: def-weil-pbc-completed-pullback). -/
def pbcQbarPullFamily : StageSystem.Morphism
    (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out) :=
  (pbcQbarPullFamily_existsUnique l Ω f).exists.choose

/-- The pair-category pullback: (E,K) goes to (E,Lf*K), and a common-stage arrow
is mapped by the normalized beta, actual pullback, inverse beta formula.
Source: BS Remark 6.8.15 (blueprint: def-weil-pbc-completed-pullback). -/
def pbcQbarCompletedPull : pbcQbarCategory l Ω Y ⥤ pbcQbarCategory l Ω X :=
  (pbcQbarPullFamily l Ω f).functor

end AlgebraicGeometry.Scheme
