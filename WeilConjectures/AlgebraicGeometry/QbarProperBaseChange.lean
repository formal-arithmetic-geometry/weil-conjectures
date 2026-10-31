/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import WeilConjectures.AlgebraicGeometry.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.FiniteStagePairCategory
public import WeilConjectures.AlgebraicGeometry.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.FibreDimension
import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
import all WeilConjectures.AlgebraicGeometry.CompletedConstructiblePreservation
import WeilConjectures.AlgebraicGeometry.PbcActualCompletedExchangeTransport
import WeilConjectures.AlgebraicGeometry.CompleteProetale

/-! # Proper base change with Qbar_l coefficients

Source: Weil blueprint main-20261015, proper base change, order 1419
(blueprint: thm-weil-pbc-qbar).

The presentation below records the canonical operations and exchange of the descent
proposition. It introduces no new coefficient category or exchange construction.
The theorem supplies this presentation, rather than assuming preservation or an
unspecified family of functors. Its exchange is defined by the actual descent formula.

## Main definitions

* `PbcQbarExchangePresentation`: the canonically specified descent witnesses.
* `PbcQbarExchangePresentation.exchange`: their descended exchange.
* `PbcQbarExchangePresentation.atStage`: its finite-overfield representative.

## Main statements

* `qbar_properBaseChange`: invertibility, the stage formula and representative independence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory
attribute [local instance 30000] DivisionSemiring.to_moduleIsTorsionFree

attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.Limits.limit
  pbcFiniteField pbcIntegralDatum pbcUniformizer
  pbcScalarExtension pbcScalarAssociator

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y X' Y' : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : ChosenCartesianSquare g' f' f g)

/-- The witnesses of prop-weil-pbc-descent-functors, with the actual finite-stage
operations, all four canonical beta specifications and the actual localized completed
exchange. These are presentation data for that existing construction, not additional
hypotheses of proper base change. No object is chosen from an existence assertion.
Source: blueprint main-20261015, order 1419, descended exchange
(blueprint: thm-weil-pbc-qbar). -/
structure PbcQbarExchangePresentation where
  presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
      ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X' E),
    PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
      ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω Y E),
    PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
      ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
      ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj)
  Rf : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out)
    (pbcScalarSystem l Ω Y dY.out iY.out)
  Rf' : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X' dX'.out iX'.out)
    (pbcScalarSystem l Ω Y' dY'.out iY'.out)
  Lg : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω Y dY.out iY.out)
    (pbcScalarSystem l Ω Y' dY'.out iY'.out)
  Lg' : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out)
    (pbcScalarSystem l Ω X' dX'.out iX'.out)
  Rf_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Rf.base.Φ E = pbcDescentDirectImage l Ω f presRf E
  Rf_beta : PbcDirectImageBetaSpec l Ω f presRf Rf.base
  Rf'_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Rf'.base.Φ E = pbcDescentDirectImage l Ω f' presRf' E
  Rf'_beta : PbcDirectImageBetaSpec l Ω f' presRf' Rf'.base
  Lg_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Lg.base.Φ E = pbcDescentPullback l Ω g presLg E
  Lg_beta : PbcPullbackBetaSpec l Ω g presLg Lg.base
  Lg'_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Lg'.base.Φ E = pbcDescentPullback l Ω g' presLg' E
  Lg'_beta : PbcPullbackBetaSpec l Ω g' presLg' Lg'.base
  Ex : StageSystem.Morphism.Hom (Rf.base.comp Lg.base) (Lg'.base.comp Rf'.base)
  exchange_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X E),
    HEq ((Ex.τ E).app (ScalarLocalization.mk K))
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
          ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app K.obj)))

/-- The composition-normalized exchange for four generic stage-system morphisms.
Source: descent of exchange (blueprint: thm-weil-pbc-qbar). -/
def pbcExchangeOfStageSystems
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J)) :
    F.functor ⋙ G.functor ⟶ H.functor ⋙ J.functor :=
  (StageSystem.Morphism.functorCompIso F G).inv ≫
    StageSystem.Morphism.descNatTrans τ ≫
    (StageSystem.Morphism.functorCompIso H J).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The representative of a generic exchange at a specified common overfield.
Source: descent of exchange (blueprint: thm-weil-pbc-qbar). -/
def pbcExchangeAtStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J))
    (K : S.PairCategory) (M : I) (h : K.stage ≤ M) :
    (F.functor ⋙ G.functor).obj K ⟶ (H.functor ⋙ J.functor).obj K :=
  StageSystem.PairCategory.mkHom M h h
    (((F.comp G).β h).hom.app K.obj ≫ (τ.τ M).app ((S.T h).obj K.obj) ≫
      ((H.comp J).β h).inv.app K.obj)

namespace PbcQbarExchangePresentation

variable (P : PbcQbarExchangePresentation l Ω sq)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exchange descended by prop-weil-pbc-descent-functors, with its specified
composition comparisons. Source: blueprint main-20261015, order 1419
(blueprint: thm-weil-pbc-qbar). -/
def exchange : P.Rf.base.functor ⋙ P.Lg.base.functor ⟶
    P.Lg'.base.functor ⋙ P.Rf'.base.functor :=
  pbcExchangeOfStageSystems P.Rf.base P.Lg.base P.Lg'.base P.Rf'.base P.Ex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite-overfield exchange representative, conjugated by precisely the scalar
comparisons of the descended composite families. In particular M may equal K.stage.
Source: blueprint main-20261015, order 1419, finite-stage representation
(blueprint: thm-weil-pbc-qbar). -/
def atStage (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
    (h : K.stage ≤ M) :
    (P.Rf.base.functor ⋙ P.Lg.base.functor).obj K ⟶
      (P.Lg'.base.functor ⋙ P.Rf'.base.functor).obj K :=
  pbcExchangeAtStage P.Rf.base P.Lg.base P.Lg'.base P.Rf'.base P.Ex K M h

end PbcQbarExchangePresentation





private theorem isIso_of_heq {C : Type*} [Category C] {A B A' B' : C}
    {a : A ⟶ B} {b : A' ⟶ B'} (hA : A = A') (hB : B = B')
    (h : HEq a b) [IsIso b] : IsIso a := by
  cases hA
  cases hB
  cases eq_of_heq h
  infer_instance

private theorem isIso_of_iso_square {C : Type*} [Category C] {A B A' B' : C}
    {a : A ⟶ B} {b : A' ⟶ B'} (s : A ≅ A') (t : B ≅ B')
    (h : a ≫ t.hom = s.hom ≫ b) (hb : IsIso b) : IsIso a := by
  let := hb
  have : IsIso (a ≫ t.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right a t.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stageExchange_atStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F G : StageSystem.Morphism S T)
    (τ : StageSystem.Morphism.Hom F G) (K : S.PairCategory) (M : I) (h : K.stage ≤ M) :
    (T.ι K.stage).map ((τ.τ K.stage).app K.obj) =
      StageSystem.PairCategory.mkHom (X := F.functor.obj K) (Y := G.functor.obj K) M h h
        ((F.β h).hom.app K.obj ≫ (τ.τ M).app ((S.T h).obj K.obj) ≫
          (G.β h).inv.app K.obj) := by
  rw [StageSystem.ι_map_eq h]
  congr 1
  exact ((Iso.eq_comp_inv ((G.β h).app K.obj)).2 (τ.comm h K.obj)).trans
    (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem descendedComp_isIso
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J))
    (K : S.PairCategory) (hi : IsIso ((τ.τ K.stage).app K.obj)) :
    IsIso (((StageSystem.Morphism.functorCompIso F G).inv ≫
      StageSystem.Morphism.descNatTrans τ ≫
      (StageSystem.Morphism.functorCompIso H J).hom).app K) := by
  let := StageSystem.Morphism.isIso_descNatTrans_app τ K hi
  simp only [NatTrans.comp_app]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem descendedComp_atStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J))
    (K : S.PairCategory) (M : I) (h : K.stage ≤ M) :
    ((StageSystem.Morphism.functorCompIso F G).inv ≫
      StageSystem.Morphism.descNatTrans τ ≫
      (StageSystem.Morphism.functorCompIso H J).hom).app K =
        StageSystem.PairCategory.mkHom
          (X := (F.functor ⋙ G.functor).obj K)
          (Y := (H.functor ⋙ J.functor).obj K) M h h
          (((F.comp G).β h).hom.app K.obj ≫ (τ.τ M).app ((S.T h).obj K.obj) ≫
            ((H.comp J).β h).inv.app K.obj) := by
  simp only [NatTrans.comp_app, StageSystem.Morphism.functorCompIso_inv_app,
    StageSystem.Morphism.functorCompIso_hom_app, StageSystem.Morphism.descNatTrans_app]
  erw [Category.id_comp, Category.comp_id]
  exact stageExchange_atStage (F.comp G) (H.comp J) τ K M h

private theorem descendedComp_properties
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J))
    (hi : ∀ i (K : C i), IsIso ((τ.τ i).app K)) :
    let ex := pbcExchangeOfStageSystems F G H J τ
    (∀ K : S.PairCategory, IsIso (ex.app K)) ∧
    (∀ i (K : C i), IsIso ((τ.τ i).app K)) ∧
    (∀ (K : S.PairCategory) (M : I) (h : K.stage ≤ M),
      ex.app K = pbcExchangeAtStage F G H J τ K M h) ∧
    (∀ (K L : S.PairCategory) (h : K ≅ L),
      (F.functor ⋙ G.functor).map h.hom ≫ ex.app L =
        ex.app K ≫ (H.functor ⋙ J.functor).map h.hom) := by
  dsimp only [pbcExchangeOfStageSystems, pbcExchangeAtStage]
  refine ⟨fun K ↦ descendedComp_isIso F G H J τ K (hi K.stage K.obj), hi,
    fun K M h ↦ descendedComp_atStage F G H J τ K M h, ?_⟩
  intro K L h
  exact NatTrans.naturality _ h.hom

private theorem localizedSquare_isIso
    {R : Type*} [CommRing R] {p : R}
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive B]
    [Linear R C] [Linear R D] [Linear R E] [Linear R B]
    {F : C ⥤ D} {G : D ⥤ B} {H : C ⥤ E} {J : E ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [F.Linear R] [G.Linear R] [H.Linear R] [J.Linear R]
    {F' : ScalarLocalization R C p ⥤ ScalarLocalization R D p}
    {G' : ScalarLocalization R D p ⥤ ScalarLocalization R B p}
    {H' : ScalarLocalization R C p ⥤ ScalarLocalization R E p}
    {J' : ScalarLocalization R E p ⥤ ScalarLocalization R B p}
    (hF : F' = ScalarLocalization.transport R p F)
    (hG : G' = ScalarLocalization.transport R p G)
    (hH : H' = ScalarLocalization.transport R p H)
    (hJ : J' = ScalarLocalization.transport R p J)
    (τ : F' ⋙ G' ⟶ H' ⋙ J') (K : C) (a : G.obj (F.obj K) ⟶ J.obj (H.obj K))
    (hτ : HEq (τ.app (ScalarLocalization.mk K))
      ((ScalarLocalization.localization R B p).map a)) (ha : IsIso a) :
    IsIso (τ.app (ScalarLocalization.mk K)) := by
  subst F'
  subst G'
  subst H'
  subst J'
  let := ha
  have hb : IsIso ((ScalarLocalization.localization R B p).map a) :=
    Functor.map_isIso _ a
  exact @isIso_of_heq _ _ _ _ _ _ (τ.app (ScalarLocalization.mk K))
    ((ScalarLocalization.localization R B p).map a) rfl rfl hτ hb

private theorem actualExchange_isIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {S T S' T' : Scheme.{u}} {v : S ⟶ T} {v' : S' ⟶ T'}
    {q : T' ⟶ T} {q' : S' ⟶ S} (square : ChosenCartesianSquare q' v' v q)
    [IsProper v] (K : PbcBoundedConstructibleComplete S d) :
    IsIso ((pbcActualCompletedExchange d square).app K.obj) := by
  obtain ⟨s, t, ht⟩ := pbcActualCompletedExchange_transport d square K.obj K.property.1
  exact isIso_of_iso_square s t ht
    (completeProetale_isIso d square K.obj K.property.1 K.property.2.2)

private theorem integralAnnihilator (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (l : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal) = 0 := by
  unfold pbcIntegralDatum
  have hd := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hl : (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
    rw [hgen]
    apply (hd.2.1 _).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  change (l : PbcIntegralRing l E) ∈ Ideal.span {pbcUniformizer l E}
  rw [Ideal.mem_span_singleton] at hl ⊢
  have h := map_dvd ULift.ringEquiv.symm hl
  change ULift.up (Padic.coefficientExtensionUniformizer l E) ∣ (l : PbcIntegralRing l E) at h
  unfold pbcUniformizer
  exact h

omit [IsAlgClosure ℚ_[l] Ω] in
private theorem integralPush_mem
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (hS : ∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))
    (hT : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
    (iS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    (iT : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (v : S ⟶ T) [IsProper v] (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω S E) :
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)
      ((pbcActualDerivedPush v (pbcStageDatum.{u} l Ω E)).obj K.obj) := by
  have unit (Z : Scheme.{u}) (h : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z)) :
      IsUnit (l : Γ(Z, ⊤)) := by
    apply Z.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    simpa only [map_natCast] using h z
  let sqv : ChosenCartesianSquare (𝟙 S) v v (𝟙 T) :=
    { w := by simp
      isoPullback := (asIso (pullback.fst v (𝟙 T))).symm
      hom_fst := by simp
      hom_snd := by simp }
  obtain ⟨e, he⟩ := exists_topologicalKrullDim_le_of_isPullback_of_compactSpace v
  have hp := (pbcStageDatum.{u} l Ω E).constructible_preservation sqv hS hT hS hT
    l (Fact.out : l.Prime).pos (integralAnnihilator l (pbcFiniteField.{u} l Ω E))
    (unit S iS) (unit T iT) (unit S iS) (unit T iT) e
    (fun L _ _ y ↦ he L y _ _ (IsPullback.of_hasPullback v y)) K.obj K.property
  rw [datumPush_eq_actualPush] at hp
  exact hp.1

section

attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

attribute [local irreducible] pbcActualCompletion pbcActualCompletedExchange
  pbcActualDirectCompletionIso pbcConditionalRational
  PbcDirectImageBetaSpec PbcPullbackBetaSpec
  StageSystem.Morphism.functorCompIso StageSystem.Morphism.descNatTrans

private theorem presentation_stage_isIso [IsProper f]
    (P : PbcQbarExchangePresentation l Ω sq) (M : Padic.FiniteCoefficientFields l Ω)
    (K : pbcStageCategory l Ω X M) : IsIso ((P.Ex.τ M).app K) := by
  rcases K with ⟨K⟩
  let a := ObjectProperty.homMk
    (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω M)
      (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω M)) (P.presLg M)).obj
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω M)
          (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω M)) (P.presRf M)).obj K))
    (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω M)
      (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω M)) (P.presRf' M)).obj
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω M)
          (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω M)) (P.presLg' M)).obj K))
    ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω M) sq).app K.obj)
  have hactual := actualExchange_isIso (pbcStageDatum.{u} l Ω M) sq K
  have ha : IsIso a := (ObjectProperty.isIso_hom_iff a).mp hactual
  have eF := P.Rf_eq M
  unfold pbcDescentDirectImage pbcConditionalRational at eF
  have eG := P.Lg_eq M
  unfold pbcDescentPullback pbcConditionalRational at eG
  have eH := P.Lg'_eq M
  unfold pbcDescentPullback pbcConditionalRational at eH
  have eJ := P.Rf'_eq M
  unfold pbcDescentDirectImage pbcConditionalRational at eJ
  let ht : P.Rf.base.Φ M ⋙ P.Lg.base.Φ M ⟶ P.Lg'.base.Φ M ⋙ P.Rf'.base.Φ M := P.Ex.τ M
  have he : HEq (ht.app (ScalarLocalization.mk K))
      ((pbcStageLocalization l Ω Y' M).map a) := P.exchange_eq M K
  have hi := localizedSquare_isIso eF eG eH eJ ht K a he ha
  exact hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presentation_exists [IsProper f] :
    Nonempty (PbcQbarExchangePresentation l Ω sq) := by
  classical
  have hf' : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
    inferInstance
  have presRf := integralPush_mem l Ω dX.out dY.out iX.out iY.out f
  have presRf' := integralPush_mem l Ω dX'.out dY'.out iX'.out iY'.out f'
  have presLg := pbcQbarIntegralPull_mem l Ω g
  have presLg' := pbcQbarIntegralPull_mem l Ω g'
  obtain ⟨Rf, Rf', Lg, Lg', hRf, hRf', hLg, hLg', bRf, bRf', bLg, bLg',
    _, _, _, _, Ex, hEx, ExQ, hExQ, hExQapp⟩ :=
    pbcDescentOperations l Ω X Y X' Y' f f' g g' sq presRf presRf' presLg presLg'
  let P : PbcQbarExchangePresentation l Ω sq :=
    ⟨presRf, presRf', presLg, presLg', Rf, Rf', Lg, Lg', hRf, bRf, hRf', bRf',
      hLg, bLg, hLg', bLg', Ex, hEx⟩
  exact ⟨P⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper base change in the actual Qbar_l coefficient pair categories.
The only geometric extra condition is properness of f; g is arbitrary. The scheme
hypotheses are exactly those required to form the four recorded coefficient categories.
The existential presentation supplies the actual operations and their canonical
normalizations, without asking for preservation as a hypothesis. Every finite-overfield
exchange component is invertible; its class is the descended component. The formula for
every M gives independence of overfield. The final equation identifies the arrows for any
two isomorphic pair representatives, using their actual induced source and target maps.
Since these functors act on quotient Homs, the equation is independent of the morphism
representative of h as well.
Source: blueprint main-20261015, proper base change, order 1419
(blueprint: thm-weil-pbc-qbar).

Proof:
1. Properness is stable under the chosen Cartesian base change. Apply actual-coefficient
constructible preservation to identity-horizontal squares for each proper direct image.
The noetherian finite-dimensional hypotheses give the uniform geometric fiber bound;
the canonical uniformizer implies that l is zero in the first coefficient quotient.
The existing integral pullback preservation theorem supplies the other two witnesses.
2. pbcDescentOperations assembles the four preserving operations into canonically
normalized coherent families and their compatible localized actual exchange. These
are exactly the fields of PbcQbarExchangePresentation.
3. The unit-normalized actual/strict completed-exchange comparison identifies the actual
exchange with the one in completeProetale_isIso. Each integral-stage input carries
intrinsic completeness and compatible etale origins, so that theorem makes the strict
exchange invertible. The full-subcategory inclusion reflects isomorphisms and the
localization functor preserves them. The four finite-stage functor equalities and
exchange_eq identify this with every finite-stage component in the presentation.
4. The generic stage-system component formula and preservation of isomorphisms by
stage inclusions make each descended component invertible. The
stage-inclusion formula and Ex.comm give
the representative at every overfield. Finally naturality is precisely the stated
independence equation for an isomorphism of pair representatives. -/
theorem qbar_properBaseChange [IsProper f] :
    ∃ P : PbcQbarExchangePresentation l Ω sq,
      (∀ K : pbcQbarCategory l Ω X, IsIso ((P.exchange).app K)) ∧
      (∀ (M : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X M),
        IsIso ((P.Ex.τ M).app K)) ∧
      (∀ (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (h : K.stage ≤ M),
        (P.exchange).app K = PbcQbarExchangePresentation.atStage l Ω sq P K M h) ∧
      (∀ (K L : pbcQbarCategory l Ω X) (h : K ≅ L),
        (P.Rf.base.functor ⋙ P.Lg.base.functor).map h.hom ≫ (P.exchange).app L =
          (P.exchange).app K ≫
            (P.Lg'.base.functor ⋙ P.Rf'.base.functor).map h.hom) := by
  classical
  obtain ⟨P⟩ := presentation_exists l Ω sq
  refine ⟨P, ?_⟩
  dsimp only [PbcQbarExchangePresentation.exchange, PbcQbarExchangePresentation.atStage]
  exact descendedComp_properties
    (C := fun M ↦ pbcStageCategory l Ω X M)
    (D := fun M ↦ pbcStageCategory l Ω Y M)
    (E := fun M ↦ pbcStageCategory l Ω X' M)
    (B := fun M ↦ pbcStageCategory l Ω Y' M)
    (S := pbcScalarSystem l Ω X dX.out iX.out)
    (T := pbcScalarSystem l Ω Y dY.out iY.out)
    (U := pbcScalarSystem l Ω X' dX'.out iX'.out)
    (V := pbcScalarSystem l Ω Y' dY'.out iY'.out)
    P.Rf.base P.Lg.base P.Lg'.base P.Rf'.base P.Ex (presentation_stage_isIso l Ω sq P)

end

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

end AlgebraicGeometry.Scheme
