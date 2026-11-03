/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackRoosFiniteTower
import WeilConjectures.ProperBaseChange.IntegralStrictModelMatchingExists
import WeilConjectures.ProperBaseChange.IntegralPullbackIdentificationExists
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackSignedShift
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.StrictIntegralRoosTransportProjections
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.StrictIntegralRoosTransportShifts
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparison
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts

/-! # Coefficient transport before the completeness restriction

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-strict-integral-coefficient-tower-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

private instance limitAdditive : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

private noncomputable def termwiseLimitIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
    HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩

private theorem termwiseAugmentation (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    RoosConeCalculus.augmentation (HomologicalComplex.coneOfHasLimitEval I.asFunctor) =
      (termwiseLimitIso I).inv ≫ roosι I := by
  rw [RoosConeCalculus.augmentation, roosAugment_eq]
  congr 1

private theorem termwiseAugmentation_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    (termwiseLimitIso (I⟦r⟧)).inv ≫ roosι (I⟦r⟧) ≫
        (Functor.commShiftIso roosF (self := RoosConeCalculus.roosCommShift) r).hom.app I =
      (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I ≫
        ((termwiseLimitIso I).inv ≫ roosι I)⟦r⟧' := by
  rw [← Category.assoc, ← termwiseAugmentation, ← termwiseAugmentation]
  apply RoosConeCalculus.shift_augmentation I
    (HomologicalComplex.coneOfHasLimitEval I.asFunctor) r
    (HomologicalComplex.coneOfHasLimitEval (I⟦r⟧).asFunctor) _
  intro q n
  simp only [HomologicalComplex.coneOfHasLimitEval,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id, Category.id_comp, Category.id_comp]
  rfl

private theorem normalized_roos_commShift
    (e : roosF (A := A) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (he : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.map (roosι I) ≫ e.hom.app I =
        DerivedCategory.Q.map (termwiseLimitIso I).hom ≫
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ I) :
    letI := RoosConeCalculus.roosCommShift (A := A)
    NatTrans.CommShift e.hom ℤ := by
  let := RoosConeCalculus.roosCommShift (A := A)
  let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  let η := SequenceKInjectiveComparison.unitQNat L
  have : NatTrans.CommShift η ℤ := SequenceKInjectiveComparison.unitQNat_shift L
  have hnorm (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map ((termwiseLimitIso I).inv ≫ roosι I) ≫ e.hom.app I =
        η.app I := by
    simp only [Functor.map_comp, Category.assoc, he]
    rw [← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id]
    erw [DerivedCategory.Q.map_id, Category.id_comp]
    rfl
  have hinv (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      η.app I ≫ e.inv.app I =
        DerivedCategory.Q.map ((termwiseLimitIso I).inv ≫ roosι I) := by
    rw [← hnorm, Category.assoc, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  have hsymm : NatTrans.CommShift e.symm.hom ℤ := by
    apply shift_of_kinjective _ _ e.symm
    · intro C I q hq
      exact inferInstanceAs (IsIso (L.rightDerivedFunctor.map (DerivedCategory.Q.map q)))
    · intro I hI r
      have : IsIso (η.app (I⟦r⟧)) := by
        change IsIso (L.rightDerivedFunctorUnitQ (I⟦r⟧))
        rw [Functor.rightDerivedFunctorUnitQ_eq]
        infer_instance
      apply (cancel_epi (η.app (I⟦r⟧))).mp
      have hη := NatTrans.shift_app_comm η r I
      rw [← Category.assoc, ← hη]
      simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp, hinv]
      simp only [Functor.commShiftIso_comp_hom_app]
      rw [Category.assoc, ← DerivedCategory.Q.commShiftIso_hom_naturality,
        ← DerivedCategory.Q.map_comp_assoc, ← termwiseAugmentation_shift,
        DerivedCategory.Q.map_comp]
      simp only [← Category.assoc, hinv]
      simp only [Functor.map_comp, Category.assoc]
  have := hsymm
  exact NatTrans.CommShift.of_iso_symm e.symm ℤ

private theorem comparison_shift_pasting
    {C T H : Type*} [Category C] [Category T] [Category H]
    [HasShift C ℤ] [HasShift T ℤ] [HasShift H ℤ]
    (B : C ⥤ T) [B.CommShift ℤ] (D : C ⥤ H) [D.CommShift ℤ]
    (R : T ⥤ H) [R.CommShift ℤ] (b : D ≅ B ⋙ R)
    (P Ps : C) (r : ℤ) (q : P⟦r⟧ ⟶ Ps)
    (T₀ Ts : T) (ε : B.obj P ⟶ T₀) [IsIso ε] (εs : B.obj Ps ⟶ Ts)
    (σ : Ts ⟶ T₀⟦r⟧) (H₀ Hs : H)
    (a : D.obj P ⟶ H₀) (as' : D.obj Ps ⟶ Hs)
    (e : H₀ ⟶ R.obj T₀) (es : Hs ⟶ R.obj Ts) (γ : Hs ⟶ H₀⟦r⟧)
    (hb : b.hom.app P ≫ R.map ε = a ≫ e)
    (hbs : b.hom.app Ps ≫ R.map εs = as' ≫ es)
    (hfinite : (B.commShiftIso r).hom.app P ≫ ε⟦r⟧' = B.map q ≫ εs ≫ σ)
    (hD : (D.commShiftIso r).hom.app P ≫ a⟦r⟧' = D.map q ≫ as' ≫ γ)
    (hE : γ ≫ e⟦r⟧' = es ≫ R.map σ ≫ (R.commShiftIso r).hom.app T₀) :
    (D.commShiftIso r).hom.app P ≫ (b.hom.app P)⟦r⟧' =
      b.hom.app (P⟦r⟧) ≫
        (Functor.commShiftIso (B ⋙ R) (self := Functor.CommShift.comp B R) r).hom.app P := by
  have hcomp :
      (Functor.commShiftIso (B ⋙ R) (self := Functor.CommShift.comp B R) r).hom.app P ≫
          (R.map ε)⟦r⟧' =
        R.map (B.map q) ≫ R.map εs ≫ R.map σ ≫ (R.commShiftIso r).hom.app T₀ := by
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
    rw [← R.commShiftIso_hom_naturality, ← R.map_comp_assoc, hfinite]
    simp only [Functor.map_comp, Category.assoc]
  apply (cancel_mono ((R.map ε)⟦r⟧')).mp
  calc
    _ = (D.commShiftIso r).hom.app P ≫ a⟦r⟧' ≫ e⟦r⟧' := by
      rw [Category.assoc, ← Functor.map_comp, hb, Functor.map_comp]
    _ = D.map q ≫ as' ≫ γ ≫ e⟦r⟧' := by
      rw [← Category.assoc, hD]
      simp only [Category.assoc]
    _ = D.map q ≫ as' ≫ es ≫ R.map σ ≫ (R.commShiftIso r).hom.app T₀ := by
      rw [hE]
    _ = D.map q ≫ b.hom.app Ps ≫ R.map εs ≫ R.map σ ≫
        (R.commShiftIso r).hom.app T₀ := by
      rw [← Category.assoc as' es, ← hbs]
      simp only [Category.assoc]
    _ = _ := by
      rw [Category.assoc, hcomp]
      rw [← Category.assoc (D.map q) (b.hom.app Ps), b.hom.naturality q]
      simp only [Functor.comp_map, Category.assoc]

/-- Shift square on good representatives for the normalized integral Roos comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 0941, shifted K-injective computation.
(blueprint: lem-a1-integral-roos-finite-tower-shift-good).
-/
theorem integralRoosFiniteTower_commShift_good
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : roosF (A := integralTowerModules.{u, u} l E X) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙
        completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))
    (he : ∀ I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules.{u, u} l E X) ℤ,
      DerivedCategory.Q.map (roosι I) ≫ e.hom.app I =
        DerivedCategory.Q.map
            ((limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).hom) ≫
          (completedTowerLimit X
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).rightDerivedFunctorUnitQ I)
    (b : integralDerivedPullback.{u, u} l E g ≅ C.B.functor ⋙
      completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))
    (hb : ∀ (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ)
      (hP : integralOperationsGoodComplex.{u, u} l E Y P),
      b.hom.app (DerivedCategory.Q.obj P) ≫
          (completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).map
            (C.B.counit.app P) =
        (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨P, hP⟩ ≫
          e.hom.app ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj P))
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ)
    (hd : ShiftDescent l E g c d) :
    letI := C.finiteShift
    ∀ (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ)
      (hP : integralOperationsGoodComplex.{u, u} l E Y P) (r : ℤ),
      (Functor.commShiftIso (integralDerivedPullback.{u, u} l E g)
          (self := d) r).hom.app (DerivedCategory.Q.obj P) ≫
        (b.hom.app (DerivedCategory.Q.obj P))⟦r⟧' =
      b.hom.app ((DerivedCategory.Q.obj P)⟦r⟧) ≫
        (Functor.commShiftIso (C.B.functor ⋙
          completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))
          (self := Functor.CommShift.comp C.B.functor
            (completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))) r).hom.app
          (DerivedCategory.Q.obj P) := by
  let := completedAbelian l E X
  let := completedAbelian l E Y
  let := C.finiteShift
  let := d
  let R := completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
  let S := FinitePullbackStrictTower.finiteComplex.{u, u} l E g
  let D := integralDerivedPullback.{u, u} l E g
  let : HasCountableProducts (integralTowerModules.{u, u} l E X) := products l E X
  let := RoosConeCalculus.roosCommShift.{u + 2, u + 1}
    (A := integralTowerModules.{u, u} l E X)
  have : IsGrothendieckAbelian.{u + 1} (integralTowerModules.{u, u} l E X) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).1
  have : IsGrothendieckAbelian.{u + 1}
      (ℕᵒᵖ ⥤ integralTowerModules.{u, u} l E X) := inferInstance
  have : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ integralTowerModules.{u, u} l E X) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  have : NatTrans.CommShift e.hom ℤ := normalized_roos_commShift e he
  intro P hP r
  obtain ⟨hPs, hds⟩ := hd ⟨P, hP⟩ r
  have := C.B.computes P hP
  have hfinite :
      (Functor.commShiftIso C.B.functor (self := C.finiteShift) r).hom.app
          (DerivedCategory.Q.obj P) ≫ (C.B.counit.app P)⟦r⟧' =
        C.B.functor.map ((DerivedCategory.Q.commShiftIso r).inv.app P) ≫
          C.B.counit.app (P⟦r⟧) ≫
          DerivedCategory.Q.map ((Functor.commShiftIso S
            (self := C.finiteChainShift) r).hom.app P) ≫
          (DerivedCategory.Q.commShiftIso r).hom.app (S.obj P) := by
    apply (cancel_epi (C.B.functor.map ((DerivedCategory.Q.commShiftIso r).hom.app P))).mp
    erw [C.finiteShift_descent P r]
    simp only [← C.B.functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [C.B.functor.map_id, Category.id_comp]
  let σ := DerivedCategory.Q.map ((Functor.commShiftIso S
      (self := C.finiteChainShift) r).hom.app P) ≫
    (DerivedCategory.Q.commShiftIso r).hom.app (S.obj P)
  let γ := DerivedCategory.Q.map
      ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor l E g)
        (self := c) r).hom.app P) ≫
    (DerivedCategory.Q.commShiftIso r).hom.app (roosF.obj (S.obj P))
  have eshift := NatTrans.shift_app_comm e.hom r (S.obj P)
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at eshift
  have enat := e.hom.naturality
    ((Functor.commShiftIso S (self := C.finiteChainShift) r).hom.app P)
  dsimp only [Functor.comp_map] at enat
  refine comparison_shift_pasting C.B.functor D R b
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj (P⟦r⟧)) r
    ((DerivedCategory.Q.commShiftIso r).inv.app P)
    (DerivedCategory.Q.obj (S.obj P)) (DerivedCategory.Q.obj (S.obj (P⟦r⟧)))
    (C.B.counit.app P) (C.B.counit.app (P⟦r⟧)) σ
    (DerivedCategory.Q.obj (roosF.obj (S.obj P)))
    (DerivedCategory.Q.obj (roosF.obj (S.obj (P⟦r⟧))))
    ((integralDerivedPullbackComparison l E g).hom.app ⟨P, hP⟩)
    ((integralDerivedPullbackComparison l E g).hom.app ⟨P⟦r⟧, hPs⟩)
    (e.hom.app (S.obj P)) (e.hom.app (S.obj (P⟦r⟧))) γ
    (hb P hP) (hb (P⟦r⟧) hPs) hfinite hds ?_
  dsimp only [γ, σ]
  erw [finite_roos_chain_shift l E g C c hc P r, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  erw [eshift, reassoc_of% enat]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem finite_roos_chain_shift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) :
    (Functor.commShiftIso (integralOperationsPullbackComplexFunctor l E g)
        (self := c) r).hom.app P =
      (roosF (A := integralTowerModules.{u, u} l E X)).map
        ((Functor.commShiftIso (FinitePullbackStrictTower.finiteComplex l E g)
        (self := C.finiteChainShift) r).hom.app P) ≫
      (Functor.commShiftIso (roosF (A := integralTowerModules.{u, u} l E X))
        (self := RoosConeCalculus.roosCommShift) r).hom.app
        ((FinitePullbackStrictTower.finiteComplex l E g).obj P) := by
  let N := (FinitePullbackStrictTower.finiteComplex l E g).obj P
  let f := (Functor.commShiftIso (FinitePullbackStrictTower.finiteComplex l E g)
    (self := C.finiteChainShift) r).hom.app P
  ext j : 1
  apply SignedCoconeShift.cocone_ext_from (roosEnd l E g (P⟦r⟧)) j
  · erw [(hc P r).1 j]
    simp only [HomologicalComplex.comp_f]
    erw [roos_map_inl_assoc f j, ← RoosConeCalculus.roosShiftMap_eq N r,
      RoosConeCalculus.roosShift_inl N r j]
    erw [← Category.assoc ((roosPmap f).f j)
      (RoosConeCalculus.productShiftComponent N r j), finite_product_shift l E g C P r j]
    rfl
  · have hj : j - 1 + 1 = j := by omega
    apply ((hc P r).2 (j - 1) j hj).trans
    simp only [HomologicalComplex.comp_f]
    erw [roos_map_inr_assoc f (j - 1) j hj,
      ← RoosConeCalculus.roosShiftMap_eq N r,
      RoosConeCalculus.roosShift_inr N r (j - 1) j hj, Linear.comp_units_smul]
    erw [← Category.assoc ((roosPmap f).f (j - 1))
      (RoosConeCalculus.productShiftComponent N r (j - 1)),
      finite_product_shift l E g C P r (j - 1)]
    rfl

@[reassoc]
private theorem roos_map_inr
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {N M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ M) (i j : ℤ) (h : i + 1 = j) :
    (CochainComplex.mappingCocone.inr (roosU N)).1.v i j h ≫
        (roosF.map f).f j =
      (roosPmap f).f i ≫ (CochainComplex.mappingCocone.inr (roosU M)).1.v i j h := by
  have he : roosF.map f = SignedCoconeShift.coconeMap (roosU N) (roosU M)
      (Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm) := by
    exact congrArg ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
      (RoosConeCalculus.cofiberMap_eq_coneMap (roosU N) (roosU M)
        (roosPmap f) (roosPmap f) (roosU_natural f)).symm
  rw [he]
  exact SignedCoconeShift.coconeMap_inr _ _ _ i j h

@[reassoc]
private theorem roos_map_inl
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {N M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ M) (j : ℤ) :
    (CochainComplex.mappingCocone.inl (roosU N)).v j j (add_zero j) ≫
        (roosF.map f).f j =
      (roosPmap f).f j ≫ (CochainComplex.mappingCocone.inl (roosU M)).v j j
        (add_zero j) := by
  have he : roosF.map f = SignedCoconeShift.coconeMap (roosU N) (roosU M)
      (Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm) := by
    exact congrArg ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
      (RoosConeCalculus.cofiberMap_eq_coneMap (roosU N) (roosU M)
        (roosPmap f) (roosPmap f) (roosU_natural f)).symm
  rw [he]
  exact SignedCoconeShift.coconeMap_inl _ _ _ j

private theorem finite_product_shift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r i : ℤ) :
    (roosPmap ((Functor.commShiftIso (FinitePullbackStrictTower.finiteComplex l E g)
        (self := C.finiteChainShift) r).hom.app P)).f i ≫
      RoosConeCalculus.productShiftComponent
        ((FinitePullbackStrictTower.finiteComplex l E g).obj P) r i =
      (productShift l E g P r).hom.f i := by
  let N := (FinitePullbackStrictTower.finiteComplex l E g).obj P
  apply RoosConeCalculus.product_ext N (i + r)
  intro n
  erw [Category.assoc, RoosConeCalculus.productShift_π]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  have hm := congrArg (fun f ↦ f.f i)
    (Pi.map_π (fun n : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((Functor.commShiftIso (FinitePullbackStrictTower.finiteComplex l E g)
          (self := C.finiteChainShift) r).hom.app P)).app (op n)) n)
  simp only [HomologicalComplex.comp_f] at hm
  erw [hm]
  have hn := C.finiteChainShift_normalization P r i n
  change _ ≫ (((Functor.commShiftIso (FinitePullbackStrictTower.finiteComplex l E g)
    (self := C.finiteChainShift) r).hom.app P).f i).app (op n) = _
  erw [hn]
  have hp : (productShift l E g P r).hom ≫
      (Pi.π (fun n : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op n)) n)⟦r⟧' =
      Pi.π (fun n : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E g).obj (P⟦r⟧)).obj (op n)) n ≫
        (levelShift l E g P r n).hom := by
    dsimp only [productShift, Iso.trans_hom, Iso.symm_hom]
    erw [Category.assoc, product_iso_inv_π, Pi.mapIso_hom_π]
  have hpf := congrArg (fun f ↦ f.f i) hp
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at hpf
  exact hpf.symm

private instance (priority := 7000) completedProducts (W : Scheme.{u}) :
    HasCountableProducts (CompletedTowerIndependent.Modules.{u, u} l E W) :=
  products l E W

private instance (priority := 7000) completedAbelian (W : Scheme.{u}) :
    Abelian (integralTowerModules.{u, u} l E W) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

private theorem product_iso_inv_π
    {V W : Type*} [Category V] [Category W]
    [HasCountableProducts V] [HasCountableProducts W]
    (F : V ⥤ W) [PreservesLimitsOfShape (Discrete ℕ) F] (p : ℕ → V) (n : ℕ) :
    (PreservesProduct.iso F p).inv ≫ F.map (Pi.π p n) =
      Pi.π (fun n ↦ F.obj (p n)) n := by
  apply (cancel_epi (PreservesProduct.iso F p).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (piComparison_comp_π F p n).symm

namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

-- The existential projection property retains the named goodness hypothesis,
-- although its displayed equality does not depend on the proof of goodness.
set_option linter.unusedVariables false in
end WeilConjectures.IntegralCompletedComparison
