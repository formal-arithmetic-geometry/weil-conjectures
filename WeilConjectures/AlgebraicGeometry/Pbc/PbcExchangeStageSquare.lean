/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces

/-! # Scalar square for the prescribed finite-stage exchange

Source: blueprint main-20261015, proper base change, order 1312, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

/-- `pbcExchangeStageSquare` on integral objects, with the composite comparisons of
`StageSystem.Morphism.comp` expanded.
Source: blueprint main-20261015, order 1312, final exchange sentence and the
scalar exchange equation of order 1307
(blueprint: lem-weil-pbc-exchange-stage-square).
Proof plan (the reduction steps below are not yet formalized): destruct the four family
records and substitute `Φ` by `funext hRf` etc. Then turn the four BetaSpec identities
and `hτ` into equations of morphisms in the rational stage categories. Use naturality of
`τ F` along `pbcScalarIntegralComparison` and of `pbcScalarIntegralComparison` along the
integral exchange. What remains is the localization of the ambient scalar exchange
equation, which has no Lean statement yet:
`T_{Y'}(Ex_E K) ≫ D_{f'} ≫ Rf'_F(C_{g'}⁻¹) = C_g⁻¹ ≫ Lg_F(D_f) ≫ Ex_F(T_X K)`, with
`D = pbcScalarDirectImageIso`, `C = pbcScalarCompletedPullIso` and
`Ex = pbcActualCompletedExchange`.
Obstacles: the BetaSpec and `pbcScalar*_rational` identities are heterogeneous
equalities. Their sides have different types: `pbcScalarExtension` against
`pbcRationalScalarExtension`, which agree only for `E ≠ F` and only through `choose_spec`,
and `pbcIntegralScalarExtension` against `pbcEmbeddingIntegralTensor`, which agree by the
private `pbcIntegralScalarExtension_eq`. Making them homogeneous needs these functor
equalities as transports, with `E = F` treated separately.
Tried: destructing the records, substituting `Φ` and simplifying the `eqToIso rfl`
conjugations in `bRf h rfl rfl K` all elaborate. Applying `eq_of_heq` to the result
times out at `whnf` (200000 heartbeats), because the two sides do not have
definitionally equal types. -/
theorem pbcExchangeStageSquare_integral
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (Rf' : StageSystem.Morphism (pbcScalarSystem l Ω X' dX'.out iX'.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg' : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω X' dX'.out iX'.out))
    (hRf : ∀ E, Rf.Φ E = pbcDescentDirectImage l Ω f presRf E)
    (hRf' : ∀ E, Rf'.Φ E = pbcDescentDirectImage l Ω f' presRf' E)
    (hLg : ∀ E, Lg.Φ E = pbcDescentPullback l Ω g presLg E)
    (hLg' : ∀ E, Lg'.Φ E = pbcDescentPullback l Ω g' presLg' E)
    (bRf : PbcDirectImageBetaSpec l Ω f presRf Rf)
    (bRf' : PbcDirectImageBetaSpec l Ω f' presRf' Rf')
    (bLg : PbcPullbackBetaSpec l Ω g presLg Lg)
    (bLg' : PbcPullbackBetaSpec l Ω g' presLg' Lg')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (Rf.comp Lg).Φ E ⟶ (Lg'.comp Rf').Φ E)
    (hτ : ∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app
                  K.obj)))) :
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcIntegralStage l Ω X E),
      ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map
          ((τ E).app (ScalarLocalization.mk K)) ≫
          (Rf'.β h).hom.app ((Lg'.Φ E).obj (ScalarLocalization.mk K)) ≫
          (Rf'.Φ F).map ((Lg'.β h).hom.app (ScalarLocalization.mk K)) =
        (Lg.β h).hom.app ((Rf.Φ E).obj (ScalarLocalization.mk K)) ≫
          (Lg.Φ F).map ((Rf.β h).hom.app (ScalarLocalization.mk K)) ≫
          (τ F).app
            (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj (ScalarLocalization.mk K)) := by
  sorry

/-- The prescribed localized actual exchange components satisfy the scalar
square for already given normalized stage families. Existence and naturality of
the stage transformations are supplied separately.
Source: blueprint main-20261015, order 1312, final exchange sentence and the
scalar exchange equation of order 1307
(blueprint: lem-weil-pbc-exchange-stage-square).

Proof: fix E ≤ F and an integral representative K. Destruct the four family
records and substitute the functor-family equalities obtained from hRf, hRf',
hLg and hLg' by function extensionality. Thus every stage operation is the
specified actual rational operation; proof irrelevance removes the remaining
identity conjugations. Expanding Morphism.comp leaves the equation
T.map (τ_E K) ≫ β_Rf' (Lg'_E K) ≫ Rf'_F.map (β_Lg' K) =
β_Lg (Rf_E K) ≫ Lg_F.map (β_Rf K) ≫ τ_F (T_X K). Conjugate by the scalar/integral
comparison isomorphisms at its source and target. The direct-image BetaSpec
identities identify the two direct-image comparisons with their localized ambient
mates. The pullback BetaSpec identities identify the inverses of the two pullback
comparisons; multiply by their invertible components to obtain the required
orientation. Use naturality of pbcScalarIntegralComparison on the integral exchange arrow
to move scalar extension past its localized component. For the F-component use
naturality of τ_F at the source comparison
T_X(Q_X K) ⟶ Q_X(I_X K); this replaces evaluation at T_X(Q_X K) by evaluation
at the localized integral scalar extension. Substitute hτ at K and at I_X K. Functoriality of
localization combines adjacent factors and
cancels the inverse scalar/integral comparisons. The remaining equality is the
localization of pbcScalarCompletedExchange at K.obj. Every rational stage object
is an integral representative, so this proves the square for all objects.
Repeated coefficient fields obey the same equations and require no strict unit
identification. -/
theorem pbcExchangeStageSquare
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (Rf' : StageSystem.Morphism (pbcScalarSystem l Ω X' dX'.out iX'.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg' : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω X' dX'.out iX'.out))
    (hRf : ∀ E, Rf.Φ E = pbcDescentDirectImage l Ω f presRf E)
    (hRf' : ∀ E, Rf'.Φ E = pbcDescentDirectImage l Ω f' presRf' E)
    (hLg : ∀ E, Lg.Φ E = pbcDescentPullback l Ω g presLg E)
    (hLg' : ∀ E, Lg'.Φ E = pbcDescentPullback l Ω g' presLg' E)
    (bRf : PbcDirectImageBetaSpec l Ω f presRf Rf)
    (bRf' : PbcDirectImageBetaSpec l Ω f' presRf' Rf')
    (bLg : PbcPullbackBetaSpec l Ω g presLg Lg)
    (bLg' : PbcPullbackBetaSpec l Ω g' presLg' Lg')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (Rf.comp Lg).Φ E ⟶ (Lg'.comp Rf').Φ E)
    (hτ : ∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app
                  K.obj)))) :
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcStageCategory l Ω X E),
      ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map ((τ E).app K) ≫
          ((Lg'.comp Rf').β h).hom.app K =
        ((Rf.comp Lg).β h).hom.app K ≫
          (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj K) := by
  intro E F h K
  obtain ⟨K⟩ := K
  simp only [StageSystem.Morphism.comp, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  exact pbcExchangeStageSquare_integral l Ω X Y X' Y' f f' g g' sq presRf presRf' presLg presLg'
    Rf Rf' Lg Lg' hRf hRf' hLg hLg' bRf bRf' bLg bLg' τ hτ h K

end AlgebraicGeometry.Scheme
