/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismCoefficientInclusions
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismPullbackScalarIntegralShift

/-! # A step of coherent isomorphism pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open TensorProduct
namespace WeilConjectures
attribute [local irreducible] rationalDerivedPullback
  integralDerivedPullback sfRationalTriangulationDatum sfRationalScalarExtension
  rationalPullbackScalarComparison sfIntegralScalarComp sfIntegralScalarUnit
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

private theorem commShiftCore_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (n : ℤ) (h : NatTrans.CommShiftCore τ n) :
    NatTrans.CommShiftCore τ (-n) := by
  constructor
  ext X
  apply (shiftFunctor D n).map_injective
  have hz : NatTrans.CommShiftCore τ (-n + n) := by
    simpa only [neg_add_cancel] using NatTrans.CommShiftCore.zero (τ := τ) ℤ
  have hs := hz.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Category.assoc] at hs
  rw [← NatTrans.naturality_assoc] at hs
  have hD := (shiftFunctorAdd D (-n) n).inv.naturality (τ.app X)
  dsimp only [Functor.comp_map] at hD
  rw [← hD] at hs
  apply (cancel_epi (F.map ((shiftFunctorAdd C (-n) n).hom.app X) ≫
    (F.commShiftIso n).hom.app (X⟦-n⟧))).mp
  apply (cancel_mono ((shiftFunctorAdd D (-n) n).inv.app (G.obj X))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, h.shift_app_comm_assoc τ] using hs

private theorem commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (h : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn := commShiftCore_neg τ 1 h
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero (τ := τ) ℤ
  | @succ n ih => exact ih.add h
  | @pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

private theorem map_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem dependent_app_heq {A : Sort*} {B : A → Sort*}
    (f : (a : A) → B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem localization_shift_map (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) {J J' : sfIntegralConstructibleCategory l E W} (f : J ⟶ J') :
    HEq (((sfRationalConstructibleLocalization l E W).map f)⟦(1 : ℤ)⟧')
      ((sfRationalConstructibleLocalization l E W).map (f⟦(1 : ℤ)⟧')) := by
  have hshift := (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1
  refine (Functor.hcongr_hom hshift
    ((sfRationalConstructibleLocalization l E W).map f)).trans ?_
  apply heq_of_eq
  change ScalarLocalization.mapHom _ _ _ (shiftFunctor _ (1 : ℤ)) _ _ (1 ⊗ₜ f) = _
  simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
  rfl

private theorem localization_shift_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (J : sfRationalConstructibleCategory l E W) :
    J⟦(1 : ℤ)⟧ = (sfRationalConstructibleLocalization l E W).obj (J.obj⟦(1 : ℤ)⟧) :=
  Functor.congr_obj (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1 J

set_option maxHeartbeats 800000 in
-- The four normalized localization squares require explicit heterogeneous transports.
/-- The specified scalar comparison preserves the normalized integral and rational shifts.
Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-constructible-truncations.proof.md, final automorphism sentence;
steps 4, 5 and 7 of lem-pod-isomorphism-pullback-texact-coefficients.
(blueprint: lem-pod-isomorphism-pullback-scalar-shift).

Proof: identify each ordinary-to-completed scalar comparison with scalarCompletionIso
using its normalization. Its shift equation is exactly the defining normalization of
the integral scalar transition. The derived sectionwise inverse-image tensor comparison
preserves the termwise shifts. The published inverse-image scalar compatibility square
expresses the specified alpha as the conjugate of these shift-compatible maps through
eE and eL. Whisker with the fully faithful constructible inclusion and cancel to get
the integral shift square. The specified rational comparison has components Q_L(alpha).
The given degree-one normalizations of rational pullback and the corresponding fixed
normalization of rational scalar extension transfer the integral shift square through
localization. Its degree-one equation implies the equations for every integer shift:
iterate for positive shifts and use inverses for negative shifts. No new comparison or
shift is selected, and all morphisms in the raw rationalized categories are retained. -/
theorem isomorphismPullbackScalarShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (E L : Index l Ω) (h : E ≤ L)
    (sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ)
    (rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ)
    (eE : (sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙ inverseImageIntegralDerived
      l (Coefficient.{u} l Ω E) g ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g) ⋙ (sfIntegralConstructible l
      (Coefficient.{u} l Ω E) X).ι)
    (heE : ∀ K, HEq (eE.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω E) g hX hY K.obj))
    (hsE : (fun [_s : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ] ↦
      NatTrans.CommShift eE.hom ℤ) (_s := sE))
    (hrE : ∀ K, HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).commShiftIso (self
      := rE) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).map
      (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).commShiftIso (self := sE) (1
      : ℤ)).hom.app K)))
    (sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ)
    (rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ)
    (eL : (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι ⋙ inverseImageIntegralDerived
      l (Coefficient.{u} l Ω L) g ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) ⋙ (sfIntegralConstructible l
      (Coefficient.{u} l Ω L) X).ι)
    (heL : ∀ K, HEq (eL.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω L) g hX hY K.obj))
    (hsL : (fun [_s : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      NatTrans.CommShift eL.hom ℤ) (_s := sL))
    (hrL : ∀ K, HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω L) g).commShiftIso (self
      := rL) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
      (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).commShiftIso (self := sL) (1
      : ℤ)).hom.app K)))
    (α : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g) ⋙
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h) ≅
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h) ⋙
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g))
    (hα : ∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g K) :
    (fun [_sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      NatTrans.CommShift α.hom ℤ) (_sE := sE) (_sL := sL) ∧
    (fun [_rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      @NatTrans.CommShift _ _ _ _ _ _
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (isomorphismCoefficientInclusion l Ω E L h) g).hom ℤ _ _ _
        (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _
          (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h))
        (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
          (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h) _))
      (_rE := rE) (_rL := rL) := by
  dsimp only [isomorphismCoefficientInclusion,
    GeneralAlgebraicallyClosedCoefficients.stageShift,
    GeneralAlgebraicallyClosedCoefficients.stageCategory] at hα ⊢
  let := sE
  let := sL
  let := rE
  let := rL
  let (W : Scheme.{u}) : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
  have ha : NatTrans.CommShift α.hom ℤ :=
    isomorphismPullbackScalarIntegralShift l Ω g hX hY E L h sE eE heE hsE
      sL eL heL hsL α (by simpa only [isomorphismCoefficientInclusion] using hα)
  refine ⟨ha, ?_⟩
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h
  change NatTrans.CommShift
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g).hom ℤ
  apply commShift_of_one
  constructor
  ext K
  let A := constructibleIntegralPullback l (Coefficient.{u} l Ω E) g
  let B := constructibleIntegralPullback l (Coefficient.{u} l Ω L) g
  let Ar := rationalDerivedPullback l (Coefficient.{u} l Ω E) g
  let Br := rationalDerivedPullback l (Coefficient.{u} l Ω L) g
  let S (W : Scheme.{u}) :=
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h
  let T (W : Scheme.{u}) := sfRationalScalarExtension l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h)
  let Q (W : Scheme.{u}) := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) W
  let QL (W : Scheme.{u}) := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) W
  let β := rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g
  have oA (J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
      Ar.obj J = (Q X).obj (A.obj J.obj) := by
    simpa only [Ar, A, Q, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l (Coefficient.{u} l Ω E) g).exists.choose_spec.2.1 J
  have oB (J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) Y) :
      Br.obj J = (QL X).obj (B.obj J.obj) := by
    simpa only [Br, B, QL, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l (Coefficient.{u} l Ω L) g).exists.choose_spec.2.1 J
  have oT (W : Scheme.{u}) (J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) W) :
      (T W).obj J = (QL W).obj ((S W).obj J.obj) := by
    simpa only [T, S, QL, GeneralAlgebraicallyClosedCoefficients.integralTransition,
      sfRationalScalarExtension, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (sfRationalScalarExtension_existsUnique l (Coefficient.{u} l Ω E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).exists.choose_spec.2.1 J
  have oF (J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
      (Ar ⋙ T X).obj J = (QL X).obj ((A ⋙ S X).obj J.obj) :=
    (congrArg (T X).obj (oA J)).trans (oT X _)
  have oG (J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
      (T Y ⋙ Br).obj J = (QL X).obj ((S Y ⋙ B).obj J.obj) :=
    (congrArg Br.obj (oT Y J)).trans (oB _)
  have mT (W : Scheme.{u}) (J J' : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W)
      (f : J ⟶ J') : HEq ((T W).map ((Q W).map f)) ((QL W).map ((S W).map f)) := by
    have hh := sfRationalScalarExtension_map_tmul l (Coefficient.{u} l Ω E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) J J' f 1
    simp only [T, Q, QL, S, GeneralAlgebraicallyClosedCoefficients.integralTransition,
      sfRationalConstructibleLocalization, ScalarLocalization.localization, map_one] at hh ⊢
    convert hh using 1
  have mB (J J' : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) Y)
      (f : J ⟶ J') : HEq (Br.map ((QL Y).map f)) ((QL X).map (B.map f)) := by
    simp only [Br, B, QL, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      (Coefficient.{u} l Ω L) g).exists.choose_spec.2.2 J J' f 1
  have cY := localization_shift_obj l (Coefficient.{u} l Ω E) Y
  have cX := localization_shift_obj l (Coefficient.{u} l Ω E) X
  have cLY := localization_shift_obj l (Coefficient.{u} l Ω L) Y
  have cLX := localization_shift_obj l (Coefficient.{u} l Ω L) X
  have cA := congrArg (fun J ↦ J.obj⟦(1 : ℤ)⟧) (oA K)
  have cT := congrArg (fun J ↦ J.obj⟦(1 : ℤ)⟧) (oT Y K)
  have srcA := (congrArg Ar.obj (cY K)).trans (oA _)
  have tgtA := (cX (Ar.obj K)).trans (congrArg (Q X).obj cA)
  have srcT := (congrArg (T Y).obj (cY K)).trans (oT Y _)
  have tgtT := (cLY ((T Y).obj K)).trans (congrArg (QL Y).obj cT)
  dsimp only [Q, QL, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    Functor.comp_obj] at srcA tgtA srcT tgtT
  have hmapA := (map_heq (T X) srcA tgtA (hrE K.obj)).trans
    (mT X _ _ ((A.commShiftIso (1 : ℤ)).hom.app K.obj))
  have hmapT := (map_heq Br srcT tgtT
    ((GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      l Ω Y E L h).exists.choose_spec K)).trans
    (mB _ _ (((S Y).commShiftIso (1 : ℤ)).hom.app K.obj))
  have hTX : HEq (((T X).commShiftIso (1 : ℤ)).hom.app (Ar.obj K))
      ((QL X).map (((S X).commShiftIso (1 : ℤ)).hom.app (A.obj K.obj))) :=
    (dependent_app_heq (fun J ↦ ((T X).commShiftIso (1 : ℤ)).hom.app J) (oA K)).trans
      ((GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
        l Ω X E L h).exists.choose_spec ((Q X).obj (A.obj K.obj)))
  have hBR : HEq ((Br.commShiftIso (1 : ℤ)).hom.app ((T Y).obj K))
      ((QL X).map ((B.commShiftIso (1 : ℤ)).hom.app ((S Y).obj K.obj))) :=
    (dependent_app_heq (fun J ↦ (Br.commShiftIso (1 : ℤ)).hom.app J) (oT Y K)).trans
      (hrL ((S Y).obj K.obj))
  have srcF := (congrArg (Ar ⋙ T X).obj (cY K)).trans (oF _)
  have srcG := (congrArg (T Y ⋙ Br).obj (cY K)).trans (oG _)
  have midF := (congrArg (T X).obj tgtA).trans (oT X _)
  have midG := (congrArg Br.obj tgtT).trans (oB _)
  have endF := (congrArg (shiftFunctor _ (1 : ℤ)).obj (oF K)).trans (cLX _)
  have endG := (congrArg (shiftFunctor _ (1 : ℤ)).obj (oG K)).trans (cLX _)
  dsimp only [Q, QL, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    Functor.comp_obj] at srcF srcG midF midG endF endG
  have hF := heq_comp srcF midF endF hmapA hTX
  have hG := heq_comp srcG midG endG hmapT hBR
  have hβ (J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
      HEq (β.hom.app J) ((QL X).map (α.hom.app J.obj)) := by
    have hh := (rationalPullbackScalarComparison_existsUnique l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g).exists.choose_spec J
    have hα' := congrArg Iso.hom (hα J.obj)
    dsimp only [β, QL]
    delta rationalPullbackScalarComparison
    simpa only [← hα', Iso.app_hom, Functor.comp_obj,
      GeneralAlgebraicallyClosedCoefficients.integralTransition] using hh
  have hn : HEq (β.hom.app (K⟦(1 : ℤ)⟧))
      ((QL X).map (α.hom.app (K.obj⟦(1 : ℤ)⟧))) :=
    (dependent_app_heq β.hom.app (cY K)).trans (hβ _)
  have hm : HEq ((β.hom.app K)⟦(1 : ℤ)⟧')
      ((QL X).map ((α.hom.app K.obj)⟦(1 : ℤ)⟧')) := by
    exact (map_heq (shiftFunctor _ (1 : ℤ)) (oF K) (oG K) (hβ K)).trans
      (localization_shift_map l (Coefficient.{u} l Ω L) X (α.hom.app K.obj))
  have hleft := heq_comp srcF endF endG hF hm
  have hright := heq_comp srcF srcG endG hn hG
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app]
  have hi := NatTrans.shift_app_comm α.hom (1 : ℤ) K.obj
  have hq := congrArg (QL X).map hi
  simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp] at hq
  apply eq_of_heq
  exact hleft.trans ((heq_of_eq hq).trans hright.symm)

end WeilConjectures
