/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

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

section ScalarTransport
variable (T : Scheme.{u}) [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
  {E F : Padic.FiniteCoefficientFields l Ω}

/-- Integral scalar extension of the stages is the embedding tensor of the small fields. -/
theorem pbcIntegralScalarExtension_eq_tensor (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T hdim hl :=
  pbcIntegralScalarExtension_eq l Ω T hdim hl h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] ULift.module in
/-- The rational embedding tensor is compatible with localization, objectwise literally. -/
theorem pbcStageLocalization_comp_rationalScalarExtension (h : E ≤ F) :
    pbcStageLocalization l Ω T E ⋙ pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl =
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙ pbcStageLocalization l Ω T F := by
  rw [pbcIntegralScalarExtension_eq l Ω T hdim hl h]
  refine CategoryTheory.Functor.ext
    (F := pbcStageLocalization l Ω T E ⋙ pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl)
    (G := pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl ⋙
        pbcStageLocalization l Ω T F) (fun _ ↦ rfl) ?_
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change pbcRationalScalarHom l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
    (pbcFiniteFieldInclusion l Ω h) T hdim hl K L (1 ⊗ₜ[_] f) = _
  rw [pbcRationalScalarHom_tmul]
  simp only [map_one]
  rfl

/-- For distinct stages the chosen scalar extension is the rational embedding tensor. -/
theorem pbcScalarExtension_eq_rational (h : E ≤ F) (hEF : E ≠ F) :
    pbcScalarExtension l Ω T hdim hl h =
      pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T hdim hl := by
  have hs : pbcScalarExtension l Ω T hdim hl h =
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
    simp [pbcScalarExtension, hEF]
  rw [hs]
  exact (pbcRationalScalarExtension_exists l Ω T hdim hl h).unique
    (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec
    (pbcStageLocalization_comp_rationalScalarExtension l Ω T hdim hl h)

/-- For distinct stages the scalar/integral comparison is the identity-component
isomorphism given by the defining functor equality. -/
theorem pbcScalarIntegralComparison_ne (h : E ≤ F) (hEF : E ≠ F) :
    HEq (pbcScalarIntegralComparison l Ω T hdim hl h)
      (eqToIso (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec) :=
  (pbcScalarIntegralComparison_exists l Ω T hdim hl h).exists.choose_spec.2 hEF

end ScalarTransport

section GenericTransport

/-- A heterogeneous equality of comparisons `Q ⋙ S ≅ I ⋙ Q'`, over an equality of the
middle functors, gives their components up to the induced `eqToHom`. -/
theorem iso_app_of_heq_functor {A B C : Type*} [Category A] [Category B] [Category C]
    (Q : A ⥤ B) (Q' : A ⥤ C) {S S' : B ⥤ C} (hS : S = S')
    {c : Q ⋙ S ≅ Q'} {c' : Q ⋙ S' ≅ Q'} (h : HEq c c') (K : A) :
    c.hom.app K = eqToHom (by rw [hS]) ≫ c'.hom.app K := by
  subst hS
  rw [eq_of_heq h]
  simp

/-- Solve `u₁ ≫ b ≫ u₃ = X` for the middle factor when the outer factors are invertible. -/
theorem eq_inv_comp_comp_inv {C : Type*} [Category C] {s t r v : C} (u₁ : s ≅ t)
    (b : t ⟶ r) (u₃ : r ≅ v) (X : s ⟶ v) (h : u₁.hom ≫ b ≫ u₃.hom = X) :
    b = u₁.inv ≫ X ≫ u₃.inv := by
  rw [← h]
  simp

/-- Move two invertible end factors across an equation. -/
theorem comp_comp_hom_eq_hom_comp {C : Type*} [Category C] {a b c c' d e : C} (p : a ≅ b)
    (q : c ≅ d) (A : a ⟶ c') (B : c' ⟶ c) (R : b ⟶ e) (T : e ⟶ d)
    (h : p.inv ≫ A ≫ B = R ≫ T ≫ q.inv) : A ≫ B ≫ q.hom = p.hom ≫ R ≫ T := by
  rw [← cancel_epi p.inv, ← cancel_mono q.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact h

/-- A heterogeneous equality of morphisms over equalities of their endpoints. -/
theorem hom_eq_of_heq_objects {C : Type*} [Category C] {x x' y y' : C}
    (hx : x = x') (hy : y = y') {a : x ⟶ y} {b : x' ⟶ y'} (h : HEq a b) :
    a = eqToHom hx ≫ b ≫ eqToHom hy.symm := by
  subst hx hy
  simp [eq_of_heq h]

end GenericTransport

section ScalarExchange
variable (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The ambient scalar exchange equation: scalar extension along `i` carries the completed
exchange at `E` to the completed exchange at `F`, through the scalar direct-image and
completed-pullback comparisons.
Source: blueprint main-20261015, order 1307 (scalar exchange equation)
(blueprint: lem-weil-pbc-exchange-stage-square).
Proof plan (not yet formalized): both exchanges are the completions of mates of the
pullback squares `pbcActualCompletedPullSquareIso`. `pbcScalarDirectImageIso` is the mate of the
inverse of the ordinary scalar/pullback comparison, and `pbcScalarCompletedPullIso` is that
comparison followed by completion. By mate pasting, the equation reduces to the
compatibility of the ordinary scalar/pullback comparison with
`pbcActualDerivedPullCompIso`, plus the commutation of scalar extension with completion. -/
theorem pbcScalarCompletedExchange (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i Y').map
        ((pbcActualCompletedExchange (pbcIntegralDatum l E) sq).app K) ≫
      (pbcScalarDirectImageIso l E F i f').hom.app
        ((pbcActualCompletedPull g' (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPush f' (pbcIntegralDatum l F)).map
        ((pbcScalarCompletedPullIso l E F i g').inv.app K) =
    (pbcScalarCompletedPullIso l E F i g).inv.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualCompletedPull g (pbcIntegralDatum l F)).map
        ((pbcScalarDirectImageIso l E F i f).hom.app K) ≫
      (pbcActualCompletedExchange (pbcIntegralDatum l F) sq).app
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) := by
  sorry

end ScalarExchange

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

set_option maxHeartbeats 1000000 in
-- the restated goal unfolds the concrete stage functors
/-- `pbcExchangeStageSquare` on integral objects, with the composite comparisons of
`StageSystem.Morphism.comp` expanded.
Source: blueprint main-20261015, order 1312, final exchange sentence and the
scalar exchange equation of order 1307
(blueprint: lem-weil-pbc-exchange-stage-square).
Proof plan: destruct the four family records and substitute `Φ` by `funext hRf` etc.
Then turn the four BetaSpec identities and `hτ` into equations of morphisms in the
rational stage categories, as below. Use naturality of `τ F` along
`pbcScalarIntegralComparison`, and of `pbcScalarIntegralComparison` along the integral
exchange. What remains is the localization of `pbcScalarCompletedExchange` (stated
above, not yet proved).
Formalized below (before the `sorry`):
* The records are destructed and `Φ` substituted.
* The four BetaSpec identities are made homogeneous by `hom_eq_of_heq_objects`. The
  endpoint goals close by `pbcIntegralScalarExtension_eq_tensor`.
* The four `pbcScalar*_rational` specs and `hτ E K` are made homogeneous with `rfl`
  endpoints and substituted into them.
* The direct-image equations are solved for `β ≫ Rf_F.map SIC` by `Iso.inv_comp_eq`.
* The pullback equations are solved for `β.inv` by `eq_inv_comp_comp_inv`, with the outer
  isomorphisms passed explicitly. A direct `rw` with `Functor.mapIso_inv` timed out.
The goal is now restated by `show` (it needs `maxHeartbeats 1000000`) and flipped by
`comp_comp_hom_eq_hom_comp`, so the two pullback comparisons appear as `β.inv`.
Their solved forms `βLg_inv` and `βLg'_inv` are substituted by `erw`. Next: in the
goal, `βRf.hom` (under `Lg_F.map`) and `βRf'.hom` are not followed by
`Rf_F.map SIC.hom`. So multiply by the comparisons (as in `eq_inv_comp_comp_inv`) before
using `eRf` and `eRf'`.
Earlier attempt, before `show`: moving `Lg.β` and `Rf'_F.map Lg'.β` across the goal with a generic two-sided
lemma (`p.inv ≫ A ≫ B = R ≫ T ≫ q.inv → A ≫ B ≫ q.hom = p.hom ≫ R ≫ T`), applied by `refine`
with `p`, `q` given explicitly. Unifying it with the goal times out at `whnf`, even after
`dsimp only`. The goal should first be restated with `show` in the substituted form.
Still to do:
* For `E ≠ F`, rewrite the comparison components as `eqToHom`s with
  `pbcScalarIntegralComparison_ne`, `iso_app_of_heq_functor` and
  `pbcScalarExtension_eq_rational`. `E = F` needs `pbcIntegralScalarUnit` instead.
* Move `τ F` along the comparison by naturality and use `hτ F` at the integral scalar
  extension.
* Cancel the `eqToHom`s and conclude from `pbcScalarCompletedExchange`. -/
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
  intro E F h K
  obtain ⟨ΦRf, βRf, cohRf⟩ := Rf
  obtain ⟨ΦRf', βRf', cohRf'⟩ := Rf'
  obtain ⟨ΦLg, βLg, cohLg⟩ := Lg
  obtain ⟨ΦLg', βLg', cohLg'⟩ := Lg'
  obtain rfl : ΦRf = _ := funext hRf
  obtain rfl : ΦRf' = _ := funext hRf'
  obtain rfl : ΦLg = _ := funext hLg
  obtain rfl : ΦLg' = _ := funext hLg'
  -- The four BetaSpec identities, transported to homogeneous equations.
  have bRf₀ := bRf h rfl rfl K
  have bRf'₀ := bRf' h rfl rfl ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K)
  have bLg₀ := bLg h rfl rfl ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)
  have bLg'₀ := bLg' h rfl rfl K
  simp only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_trans, Iso.trans_refl] at bRf₀ bRf'₀ bLg₀ bLg'₀
  have eRf := hom_eq_of_heq_objects ?x₁ ?y₁ bRf₀
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  have eRf' := hom_eq_of_heq_objects ?x₂ ?y₂ bRf'₀
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  have eLg := hom_eq_of_heq_objects ?x₃ ?y₃ bLg₀
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  have eLg' := hom_eq_of_heq_objects ?x₄ ?y₄ bLg'₀
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  -- The localized ambient comparisons characterizing the four chosen rational ones.
  have rRf := (pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f
    dX.out dY.out iX.out iY.out (presRf E) (presRf F)).exists.choose_spec ⟨K⟩
  have rRf' := (pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f'
    dX'.out dY'.out iX'.out iY'.out (presRf' E) (presRf' F)).exists.choose_spec
      ⟨(pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K⟩
  have rLg := (pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) g
    dY'.out dY.out iY'.out iY.out (presLg E) (presLg F)).exists.choose_spec
      ⟨(pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K⟩
  have rLg' := (pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) g'
    dX'.out dX.out iX'.out iX.out (presLg' E) (presLg' F)).exists.choose_spec ⟨K⟩
  have hτE := hτ E K
  have rRf₁ := hom_eq_of_heq_objects rfl rfl rRf
  have rRf'₁ := hom_eq_of_heq_objects rfl rfl rRf'
  have rLg₁ := hom_eq_of_heq_objects rfl rfl rLg
  have rLg'₁ := hom_eq_of_heq_objects rfl rfl rLg'
  have hτE₁ := hom_eq_of_heq_objects rfl rfl hτE
  simp only [eqToHom_refl, Category.id_comp] at rRf₁ rRf'₁ rLg₁ rLg'₁ hτE₁
  rw [rRf₁] at eRf
  rw [rRf'₁] at eRf'
  rw [rLg₁] at eLg
  rw [rLg'₁] at eLg'
  rw [← Iso.app_inv, Iso.inv_comp_eq] at eRf eRf'
  have βLg_inv := eq_inv_comp_comp_inv
    ((pbcDescentPullback l Ω g presLg F).mapIso
      ((pbcScalarIntegralComparison l Ω Y dY.out iY.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)).symm) _
    ((pbcScalarIntegralComparison l Ω Y' dY'.out iY'.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
          (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))) _ eLg
  have βLg'_inv := eq_inv_comp_comp_inv
    ((pbcDescentPullback l Ω g' presLg' F).mapIso
      ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).app K).symm) _
    ((pbcScalarIntegralComparison l Ω X' dX'.out iX'.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K)) _ eLg'
  show ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map ((τ E).app ⟨K⟩) ≫
      (βRf' h).hom.app ((pbcDescentPullback l Ω g' presLg' E).obj ⟨K⟩) ≫
      (pbcDescentDirectImage l Ω f' presRf' F).map ((βLg' h).hom.app ⟨K⟩) =
    (βLg h).hom.app ((pbcDescentDirectImage l Ω f presRf E).obj ⟨K⟩) ≫
      (pbcDescentPullback l Ω g presLg F).map ((βRf h).hom.app ⟨K⟩) ≫
      (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj ⟨K⟩)
  refine comp_comp_hom_eq_hom_comp
    ((βLg h).app ((pbcDescentDirectImage l Ω f presRf E).obj ⟨K⟩))
    ((pbcDescentDirectImage l Ω f' presRf' F).mapIso ((βLg' h).app ⟨K⟩)) _ _ _ _ ?_
  simp only [Iso.app_inv, Functor.mapIso_inv]
  erw [βLg_inv, βLg'_inv]
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
