/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismCoefficientInclusions
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Integral scalar comparison preserves the specified pullback shifts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open TensorProduct
namespace WeilConjectures
attribute [local irreducible] rationalDerivedPullback
  integralDerivedPullback sfRationalTriangulationDatum sfRationalScalarExtension
  rationalPullbackScalarComparison sfIntegralScalarComp sfIntegralScalarUnit
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

section ScalarNormalization
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})

private def ordinaryComparison :
    (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W ⋙ (sfIntegralConstructible l L W).ι :=
  sfIntegralOrdinaryComparison l E L ι W

private theorem ordinaryComparison_hom (K : sfIntegralConstructibleCategory l E W) :
    (ordinaryComparison l E L ι W).hom.app K =
      (scalarCompletion l E L ι W).app K.obj := by
  let χ := scalarCompletion l E L ι W
  let (J : sfIntegralConstructibleCategory l E W) : IsIso (χ.app J.obj) :=
    (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.2 J.obj J.property.1
  let e : (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (sfIntegralConstructible l E W).ι ⋙ integralScalarExtension l E L ι W :=
    NatIso.ofComponents (fun J ↦ asIso (χ.app J.obj)) (fun f ↦ χ.naturality f.hom)
  have he : e = sfIntegralOrdinaryComparison l E L ι W := by
    apply (sfIntegralOrdinaryComparison_existsUnique l E L ι W).unique
    · intro P hP
      exact (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P
    · exact (sfIntegralOrdinaryComparison_existsUnique l E L ι W).exists.choose_spec
  exact (congrArg (fun a ↦ a.hom.app K) he).symm

private theorem scalar_restrict_obj (K : sfIntegralConstructibleCategory l E W) :
    ((sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K).obj =
      (integralScalarExtension l E L ι W).obj K.obj := rfl

end ScalarNormalization

private theorem pullback_restrict_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    ((constructibleIntegralPullback l E f).obj K).obj =
      (integralDerivedPullback l E f).obj K.obj := rfl

private theorem ordinaryComparison_shift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    letI : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
    NatTrans.CommShift (ordinaryComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom ℤ := by
  constructor
  intro n
  ext K
  have hn := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W).exists.choose_spec n K
  have hn' := eq_of_heq hn
  change _ = (ordinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).inv.app (K⟦n⟧) ≫
      (((sfIntegralConstructible l (Coefficient.{u} l Ω E) W).ι ⋙
        integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).commShiftIso n).hom.app K ≫
      (shiftFunctor (DerivedCategory (integralTowerModules l (Coefficient.{u} l Ω L) W)) n).map
        ((ordinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).hom.app K) at hn'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc, ObjectProperty.ι_map]
  change _ = (ordinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom.app (K⟦n⟧) ≫ _
  rw [← Category.assoc, hn']
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]

private theorem scalar_conjugation
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) (τ : F ⟶ G)
    {A B : C} (e : A ≅ B) (cA : F.obj A ≅ G.obj A) (cB : F.obj B ≅ G.obj B)
    (hA : cA.hom = τ.app A) (hB : cB.hom = τ.app B)
    {Z : D} (a : G.obj B ⟶ Z) (b : F.obj A ⟶ Z)
    (h : G.map e.hom ≫ a = cA.inv ≫ b) :
    a = cB.inv ≫ F.map e.inv ≫ b := by
  have hn : F.map e.hom ≫ cB.hom = cA.hom ≫ G.map e.hom := by
    rw [hA, hB]
    exact τ.naturality e.hom
  apply (cancel_epi (G.map e.hom)).mp
  rw [h]
  apply (cancel_epi cA.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hn]
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, Category.id_comp]
  rw [F.map_id, Category.id_comp]

set_option maxHeartbeats 400000 in
-- The conjugation contains several derived-functor comparison isomorphisms.
-- The `CommShift` instance for the twelve-step composite `δ` needs a larger typeclass budget.
set_option synthInstance.maxHeartbeats 40000 in
/-- The integral scalar comparison preserves the supplied integral pullback shifts.
Source: the final automorphism sentence in the current blueprint proof of constructible
truncations, and steps 1--2 of `lem-pod-isomorphism-pullback-scalar-shift`.
(blueprint: lem-pod-isomorphism-pullback-scalar-integral-shift).

Proof: uniqueness identifies the restricted ordinary-to-completed scalar comparison with
scalarCompletion. The normalization of integral scalar shifts gives its shift equation.
The ordinary derived inverse-image tensor comparison commutes with shifts. Conjugate it
by the supplied eE and eL and the ordinary-to-completed comparisons. The existing scalar
compatibility square and naturality of scalarCompletion identify the result with alpha
on underlying derived objects. Faithfulness of the constructible inclusion reflects the
shift equation. All shifts and components remain the ones supplied in the statement. -/
theorem isomorphismPullbackScalarIntegralShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (E L : Index l Ω) (h : E ≤ L)
    (sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ)
    (eE : (sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙ inverseImageIntegralDerived
      l (Coefficient.{u} l Ω E) g ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g) ⋙ (sfIntegralConstructible l
      (Coefficient.{u} l Ω E) X).ι)
    (heE : ∀ K, HEq (eE.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω E) g hX hY K.obj))
    (hsE : (fun [_s : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ] ↦
      NatTrans.CommShift eE.hom ℤ) (_s := sE))
    (sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ)
    (eL : (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι ⋙ inverseImageIntegralDerived
      l (Coefficient.{u} l Ω L) g ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) ⋙ (sfIntegralConstructible l
      (Coefficient.{u} l Ω L) X).ι)
    (heL : ∀ K, HEq (eL.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω L) g hX hY K.obj))
    (hsL : (fun [_s : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      NatTrans.CommShift eL.hom ℤ) (_s := sL))
    (α : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g) ⋙
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h) ≅
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h) ⋙
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g))
    (hα : ∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g K) :
    (fun [_sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      NatTrans.CommShift α.hom ℤ) (_sE := sE) (_sL := sL) := by
  dsimp only [isomorphismCoefficientInclusion] at hα ⊢
  let := sE
  let := sL
  let := hsE
  let := hsL
  let (W : Scheme.{u}) : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
  let χX := ordinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X
  let χY := ordinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
  have : NatTrans.CommShift χX.hom ℤ := ordinaryComparison_shift l Ω X E L h
  have : NatTrans.CommShift χY.hom ℤ := ordinaryComparison_shift l Ω Y E L h
  let b := isomorphismScalarTensorDerived l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g
  have : NatTrans.CommShift b.hom ℤ := by
    dsimp only [b, isomorphismScalarTensorDerived, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let δ : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h) ⋙
        (sfIntegralConstructible l (Coefficient.{u} l Ω L) X).ι ≅
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) ⋙
          (sfIntegralConstructible l (Coefficient.{u} l Ω L) X).ι :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ χX.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eE.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ b ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight χY _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eL ≪≫
      (Functor.associator _ _ _).symm
  have : NatTrans.CommShift δ.hom ℤ := by
    simp only [δ, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have hd : Functor.whiskerRight α.hom
      (sfIntegralConstructible l (Coefficient.{u} l Ω L) X).ι = δ.hom := by
    ext K
    let FE := integralDerivedPullback l (Coefficient.{u} l Ω E) g
    let FL := integralDerivedPullback l (Coefficient.{u} l Ω L) g
    let GE := inverseImageIntegralDerived l (Coefficient.{u} l Ω E) g
    let invL := inverseImageIntegralDerived l (Coefficient.{u} l Ω L) g
    let OX := integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X
    let SX := integralScalarExtension l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X
    let SY := integralScalarExtension l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
    let κE : GE.obj K.obj ≅ FE.obj K.obj := eE.app K
    let κL : invL.obj (SY.obj K.obj) ≅ FL.obj (SY.obj K.obj) :=
      eL.app ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).obj K)
    let χG := scalarCompletionIso l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) X (GE.obj K.obj)
      (isomorphismComparisonInputs_constructible l (Coefficient.{u} l Ω E)
        g hX hY K.obj K.property).1.1
    let χF : OX.obj (FE.obj K.obj) ≅ SX.obj (FE.obj K.obj) :=
      χX.app ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K)
    have hkE : κE.hom = inverseImagePullbackComparisonDerived
        l (Coefficient.{u} l Ω E) g hX hY K.obj := eq_of_heq (heE K)
    have hkL : κL.hom = inverseImagePullbackComparisonDerived
        l (Coefficient.{u} l Ω L) g hX hY (SY.obj K.obj) :=
      eq_of_heq (heL
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).obj K))
    have hαK : (α.hom.app K).hom = isomorphismComparisonScalarAlpha l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g hX hY K.obj K.property :=
      congrArg (fun e ↦ e.hom.hom) (hα K)
    have hc := isomorphismComparison_scalarExtension l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)
      g hX hY K.obj K.property
    rw [← hαK, ← hkE, ← hkL] at hc
    have hf : χF.hom = (scalarCompletion l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X).app (FE.obj K.obj) :=
      ordinaryComparison_hom l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) X _
    have hy : χY.hom.app K = (scalarCompletion l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).app K.obj :=
      ordinaryComparison_hom l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) Y K
    have H := scalar_conjugation OX SX
      (scalarCompletion l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) X) κE χG χF rfl hf (α.hom.app K).hom
      (b.hom.app K.obj ≫ invL.map (χY.hom.app K) ≫ κL.hom) (by
        simp only [isomorphismComparisonScalarBeta, Category.assoc,
          ← hy, SX, χG, GE, b, invL, Functor.comp_obj,
          GeneralAlgebraicallyClosedCoefficients.integralTransition,
          scalar_restrict_obj, pullback_restrict_obj] at hc ⊢
        convert hc using 1)
    simp only [δ, χF, κE, κL, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
      Iso.app_hom, Iso.app_inv, OX, invL, ObjectProperty.ι_map,
      Category.id_comp, SX, FE,
      GeneralAlgebraicallyClosedCoefficients.integralTransition, ObjectProperty.ι_obj,
      scalar_restrict_obj, pullback_restrict_obj] at H ⊢
    erw [Category.comp_id]
    convert H using 1
  have ha : NatTrans.CommShift α.hom ℤ := by
    have : NatTrans.CommShift (Functor.whiskerRight α.hom
        (sfIntegralConstructible l (Coefficient.{u} l Ω L) X).ι) ℤ := by
      rw [hd]
      infer_instance
    exact NatTrans.CommShift.of_whiskerRight α.hom
      (sfIntegralConstructible l (Coefficient.{u} l Ω L) X).ι
  exact ha

end WeilConjectures
