/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictIntegralRoosTransport
import all WeilConjectures.AlgebraicGeometry.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.AlgebraicGeometry.CompletedScalarShiftDescent
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.IntegralCompletionMatchingOnGood
import all WeilConjectures.AlgebraicGeometry.RingedCoefficientPullbackShifts
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
import all WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackComparison

/-! # Signed shifts of the recoded strict Roos comparison

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-strict-integral-roos-transport-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.inferInstanceAs.wrap false in
private instance detailedTransportShift (W : Scheme.{u}) :
    (integralDetailedTransport W l E).CommShift ℤ := by
  let := (integralDetailedCoefficientRestriction_exact W l E).1
  let := (integralDetailedCoefficientRestriction_exact W l E).2
  exact inferInstanceAs
    ((pbcIntegralTransportModules W l E).mapDerivedCategory.CommShift ℤ)

private theorem detailedFactors_shift (W : Scheme.{u}) :
    NatTrans.CommShift (pbcIntegralDetailedTransportFactors W l E).hom ℤ := by
  let := (integralDetailedCoefficientRestriction_exact W l E).1
  let := (integralDetailedCoefficientRestriction_exact W l E).2
  dsimp only [pbcIntegralDetailedTransportFactors]
  infer_instance

set_option backward.inferInstanceAs.wrap false in
private instance ordinaryComplexShift : (ordinaryIntegralPullComplex l E g).CommShift ℤ :=
  inferInstanceAs
    (((ordinaryIntegralModulePull l E g).mapHomologicalComplex (.up ℤ)).CommShift ℤ)

private theorem quotientAugmentation_shift
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) (n : ℕ) :
    (((ordinaryIntegralModulePull l E g).mapCochainComplexShiftIso r).hom.app P) ≫
        (((ordinaryIntegralQuotientAugmentation l E g).app P).app (op n))⟦r⟧' =
      ((ordinaryIntegralQuotientAugmentation l E g).app (P⟦r⟧)).app (op n) ≫
        (levelShift l E g P r n).hom := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    levelShift, Iso.app_hom, Functor.mapCochainComplexShiftIso_hom_app_f]
  change (((ordinaryIntegralQuotientAugmentation l E g).app P).app (op n)).f
      (j + r) =
    (((ordinaryIntegralQuotientAugmentation l E g).app (P⟦r⟧)).app (op n)).f j
  apply ((ordinaryIntegralModuleAdjunction l E g).homEquiv _ _).injective
  ext V x
  change ((((ordinaryIntegralQuotientAugmentation l E g).app P).app (op n)).f
      (j + r)).val.app (op ((proEtaleBaseChange g).obj V.unop))
      (((ordinaryIntegralModuleAdjunction l E g).unit.app (P.X (j + r))).val.app V x) = _
  exact ((ordinaryIntegralQuotientAugmentation_existsUnique l E g).exists.choose_spec
    P n (j + r) V.unop x).trans
    ((ordinaryIntegralQuotientAugmentation_existsUnique l E g).exists.choose_spec
      (P⟦r⟧) n j V.unop x).symm

private theorem productShift_projection
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) (n : ℕ) :
    (productShift l E g P r).hom ≫
      (Pi.π (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
        (op n)) n)⟦r⟧' =
    Pi.π (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E g).obj
      (P⟦r⟧)).obj (op n)) n ≫ (levelShift l E g P r n).hom := by
  rw [← piComparison_comp_π (shiftFunctor _ r)
    (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op n)) n]
  simp only [productShift, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc]
  exact Pi.mapIso_hom_π (fun n ↦ levelShift l E g P r n) n

private theorem completionChain_zeroSecond
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (j : ℤ) :
    (ordinaryIntegralCompletionChain l E g P).f j ≫
      (CochainComplex.mappingCocone.snd (roosEnd l E g P)).v j (j - 1) (by omega) = 0 := by
  unfold ordinaryIntegralCompletionChain
  rw [CochainComplex.mappingCocone.lift_f_snd_v]
  rfl

private theorem completionChain_first
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) :
    ordinaryIntegralCompletionChain l E g P ≫
        CochainComplex.mappingCocone.fst (roosEnd l E g P) =
      ordinaryIntegralProductAugmentation l E g P := by
  unfold ordinaryIntegralCompletionChain
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

private theorem cocone_zeroSecond
    {A : Type*} [Category A] [Abelian A] {M K L : CochainComplex A ℤ}
    (f : K ⟶ L) (b : M ⟶ CochainComplex.mappingCocone f) (j : ℤ)
    (hz : b.f j ≫ (CochainComplex.mappingCocone.snd f).v j (j - 1) (by omega) = 0) :
    b.f j = (b ≫ CochainComplex.mappingCocone.fst f).f j ≫
      (CochainComplex.mappingCocone.inl f).v j j (by omega) := by
  have h := congrArg (fun z ↦ b.f j ≫ z)
    (CochainComplex.mappingCocone.id_X f j (j - 1) (by omega))
  simpa only [Preadditive.comp_add, ← Category.assoc, hz, zero_comp, add_zero,
    Category.comp_id, HomologicalComplex.comp_f] using h.symm

private theorem completionChain_component
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (j : ℤ) :
    (ordinaryIntegralCompletionChain l E g P).f j =
      (ordinaryIntegralProductAugmentation l E g P).f j ≫
        (CochainComplex.mappingCocone.inl (roosEnd l E g P)).v j j (by omega) := by
  have h := cocone_zeroSecond (roosEnd l E g P)
    (ordinaryIntegralCompletionChain l E g P) j (completionChain_zeroSecond l E g P j)
  simpa only [completionChain_first] using h

private theorem complexMap_shift
    {C : Type*} [Category C] [Preadditive C]
    {M₀ M₁ K₀ K₁ R₀ R₁ : CochainComplex C ℤ} {r : ℤ}
    (b₀ : M₀ ⟶ R₀) (b₁ : M₁ ⟶ R₁) (a₀ : M₀ ⟶ K₀) (a₁ : M₁ ⟶ K₁)
    (k₀ : ∀ j, K₀.X j ⟶ R₀.X j) (k₁ : ∀ j, K₁.X j ⟶ R₁.X j)
    (m : M₁ ⟶ M₀⟦r⟧) (k : K₁ ⟶ K₀⟦r⟧) (s : R₁ ⟶ R₀⟦r⟧)
    (h₀ : ∀ j, b₀.f j = a₀.f j ≫ k₀ j)
    (h₁ : ∀ j, b₁.f j = a₁.f j ≫ k₁ j)
    (hk : ∀ j, k₁ j ≫ s.f j = k.f j ≫ k₀ (j + r) ≫
      (CochainComplex.shiftFunctorObjXIso R₀ r j (j + r) rfl).inv)
    (hp : m ≫ a₀⟦r⟧' = a₁ ≫ k) : m ≫ b₀⟦r⟧' = b₁ ≫ s := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  rw [h₀, h₁]
  simp only [Category.assoc]
  rw [hk j]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  have h := congrArg (fun f ↦ f.f j) hp
  simpa only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Category.assoc] using congrArg (fun f ↦ f ≫ k₀ (j + r)) h

set_option maxHeartbeats 1200000 in
-- Elaborating concrete product and cocone coordinates unfolds large coefficient models.
private theorem completionChain_shift
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) :
    (((ordinaryIntegralModulePull l E g).mapCochainComplexShiftIso r).hom.app P) ≫
        (ordinaryIntegralCompletionChain l E g P)⟦r⟧' =
      ordinaryIntegralCompletionChain l E g (P⟦r⟧) ≫
        (Functor.commShiftIso (integralOperationsPullbackComplexFunctor l E g)
          (self := c) r).hom.app P := by
  have hp : (((ordinaryIntegralModulePull l E g).mapCochainComplexShiftIso r).hom.app P) ≫
        (ordinaryIntegralProductAugmentation l E g P)⟦r⟧' =
      ordinaryIntegralProductAugmentation l E g (P⟦r⟧) ≫ (productShift l E g P r).hom := by
    apply (cancel_mono (PreservesProduct.iso (shiftFunctor _ r)
      (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
        (op n))).hom).mp
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
    rw [productShift_projection]
    simp only [← Functor.map_comp]
    simp only [ordinaryIntegralProductAugmentation, Pi.lift_π, Pi.lift_π_assoc]
    exact quotientAugmentation_shift l E g P r n
  exact complexMap_shift
    (ordinaryIntegralCompletionChain l E g P)
    (ordinaryIntegralCompletionChain l E g (P⟦r⟧))
    (ordinaryIntegralProductAugmentation l E g P)
    (ordinaryIntegralProductAugmentation l E g (P⟦r⟧))
    (fun j ↦ (CochainComplex.mappingCocone.inl (roosEnd l E g P)).v j j (by omega))
    (fun j ↦ (CochainComplex.mappingCocone.inl (roosEnd l E g (P⟦r⟧))).v j j (by omega))
    (((ordinaryIntegralModulePull l E g).mapCochainComplexShiftIso r).hom.app P)
    (productShift l E g P r).hom
    ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor l E g)
      (self := c) r).hom.app P)
    (completionChain_component l E g P) (completionChain_component l E g (P⟦r⟧))
    ((hc P r).1) hp

private theorem ordinaryShift_exists :
    ∃ s : (ordinaryIntegralDerivedPull l E g).CommShift ℤ,
      let := s
      NatTrans.CommShift (ordinaryIntegralPullCounit l E g) ℤ := by
  have hleft : (ordinaryIntegralDerivedPull l E g).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E g)
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) := by
    dsimp only [ordinaryIntegralDerivedPull, ordinaryIntegralPullCounit]
    infer_instance
  let := hleft
  exact Functor.rightKanExtension_coherentShift _ DerivedCategory.Qh _ _
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)))

private def ordinaryComplexCounit :
    DerivedCategory.Q ⋙ ordinaryIntegralDerivedPull l E g ⟶
      ordinaryIntegralPullComplex l E g ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (ordinaryIntegralDerivedPull l E g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _)
      (ordinaryIntegralPullCounit l E g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((ordinaryIntegralModulePull l E g).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ordinaryIntegralPullComplex l E g)
      (DerivedCategory.quotientCompQhIso _).hom

private theorem ordinaryComplexCounit_app
    (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) :
    (ordinaryComplexCounit l E g).app P = ordinaryIntegralPullComplexCounit l E g P := by
  simp only [ordinaryComplexCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  rfl

private theorem ordinaryCounit_shift
    [s : (ordinaryIntegralDerivedPull l E g).CommShift ℤ]
    [NatTrans.CommShift (ordinaryIntegralPullCounit l E g) ℤ] :
    NatTrans.CommShift (ordinaryComplexCounit l E g) ℤ := by
  unfold ordinaryComplexCounit
  infer_instance

private def actualComplexCounit :
    DerivedCategory.Q ⋙ completedOrdinaryPullback g (pbcIntegralDatum l E) ⟶
      (completedModulePullback g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (completedOrdinaryPullback g (pbcIntegralDatum l E)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _)
      (completedOrdinaryPullbackCounit g (pbcIntegralDatum l E)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((completedModulePullback g (pbcIntegralDatum l E)).mapHomotopyCategoryFactors
        (.up ℤ)).hom DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((completedModulePullback g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

private theorem actualComplexCounit_app
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ) :
    (actualComplexCounit l E g).app P =
      completedOrdinaryPullbackComplexCounit g (pbcIntegralDatum l E) P := by
  simp only [actualComplexCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  rfl

private theorem actualComplexCounit_shift :
    NatTrans.CommShift (actualComplexCounit l E g) ℤ := by
  have : NatTrans.CommShift (pbcActualPullCounit g (pbcIntegralDatum l E)) ℤ :=
    (pbcActualPullShift_exists g (pbcIntegralDatum l E)).exists.choose_spec
  unfold actualComplexCounit
  infer_instance

private def ordinarySquare (i : PbcProperIntegralPullbackIdentification l E g) :
    ordinaryIntegralPullComplex l E g ⋙ pbcIntegralTransportComplex X l E ≅
      pbcIntegralTransportComplex Y l E ⋙
        (completedModulePullback g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso i.moduleIso (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcIntegralTransportModules Y l E ⋙
        completedModulePullback g (pbcIntegralDatum l E))) (.up ℤ)).symm

private theorem ordinarySquare_shift (i : PbcProperIntegralPullbackIdentification l E g) :
    NatTrans.CommShift (ordinarySquare l E g i).hom ℤ := by
  have := SheafOfModules.RingedCoefficientProjection.complexComp_commShift i.moduleIso
  have := SheafOfModules.RingedCoefficientProjection.complexComp_commShift
    (Iso.refl (pbcIntegralTransportModules Y l E ⋙
      completedModulePullback g (pbcIntegralDatum l E)))
  dsimp only [ordinarySquare, Iso.trans_hom, Iso.symm_hom]
  infer_instance

private def identificationTargetCounit :
    DerivedCategory.Q ⋙
      (integralDetailedTransport Y l E ⋙ completedOrdinaryPullback g (pbcIntegralDatum l E)) ⟶
    (pbcIntegralTransportComplex Y l E ⋙
      (completedModulePullback g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pbcIntegralDetailedTransportFactors Y l E).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pbcIntegralTransportComplex Y l E) (actualComplexCounit l E g) ≫
    (Functor.associator _ _ _).inv

private def identificationSourceCounit (i : PbcProperIntegralPullbackIdentification l E g) :
    DerivedCategory.Q ⋙ (ordinaryIntegralDerivedPull l E g ⋙ integralDetailedTransport X l E) ⟶
    (pbcIntegralTransportComplex Y l E ⋙
      (completedModulePullback g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (ordinaryComplexCounit l E g)
      (integralDetailedTransport X l E) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ordinaryIntegralPullComplex l E g)
      (pbcIntegralDetailedTransportFactors X l E).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (ordinarySquare l E g i).hom DerivedCategory.Q

private theorem identificationCounits_shift
    [s : (ordinaryIntegralDerivedPull l E g).CommShift ℤ]
    [NatTrans.CommShift (ordinaryIntegralPullCounit l E g) ℤ]
    (i : PbcProperIntegralPullbackIdentification l E g) :
    NatTrans.CommShift (identificationTargetCounit l E g) ℤ ∧
      NatTrans.CommShift (identificationSourceCounit l E g i) ℤ := by
  have := ordinaryCounit_shift l E g
  have := actualComplexCounit_shift l E g
  have := ordinarySquare_shift l E g i
  have := detailedFactors_shift l E X
  have := detailedFactors_shift l E Y
  constructor
  · dsimp only [identificationTargetCounit]
    infer_instance
  · dsimp only [identificationSourceCounit]
    infer_instance

private theorem identificationCounit_equation
    (i : PbcProperIntegralPullbackIdentification l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    i.derivedIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (identificationTargetCounit l E g).app P.obj =
        (identificationSourceCounit l E g i).app P.obj := by
  have hsquare : (ordinarySquare l E g i).hom.app P.obj =
      (NatTrans.mapHomologicalComplex i.moduleIso.hom (.up ℤ)).app P.obj := by
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  simpa only [identificationTargetCounit, identificationSourceCounit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, ordinaryComplexCounit_app,
    actualComplexCounit_app, hsquare, Category.assoc, Category.comp_id]
    using i.derived_counit P

private theorem commShift_of_precomp
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {S F H : C ⥤ D} [S.CommShift ℤ] [F.CommShift ℤ] [H.CommShift ℤ]
    (t : S ⟶ F) (b : F ⟶ H)
    [NatTrans.CommShift t ℤ] [NatTrans.CommShift (t ≫ b) ℤ]
    (hinj : ∀ (K : C) (r : ℤ), Function.Injective
      (fun f : F.obj (K⟦r⟧) ⟶ (H.obj K)⟦r⟧ ↦ t.app (K⟦r⟧) ≫ f)) :
    NatTrans.CommShift b ℤ := by
  constructor
  intro r
  apply NatTrans.ext
  funext K
  apply hinj K r
  change t.app (K⟦r⟧) ≫ _ ≫ _ = t.app (K⟦r⟧) ≫ _ ≫ _
  have h := NatTrans.shift_app_comm (t ≫ b) r K
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc] at h
  rw [← NatTrans.shift_app_comm_assoc t r K]
  exact h

private theorem commShift_of_eq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F H : C ⥤ D} [F.CommShift ℤ] [H.CommShift ℤ]
    {t t' : F ⟶ H} [NatTrans.CommShift t' ℤ] (h : t = t') :
    NatTrans.CommShift t ℤ := by
  cases h
  infer_instance

private theorem commShift_of_comp_iso
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F H K : C ⥤ D} [F.CommShift ℤ] [H.CommShift ℤ] [K.CommShift ℤ]
    (t : F ⟶ H) (a : H ⟶ K) (b : F ⟶ K) [IsIso a]
    [NatTrans.CommShift a ℤ] [NatTrans.CommShift b ℤ] (h : t ≫ a = b) :
    NatTrans.CommShift t ℤ := by
  have : NatTrans.CommShift (inv a) ℤ := NatTrans.CommShift.of_isIso a ℤ
  have ht : t = b ≫ inv a := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact commShift_of_eq ht

private theorem comparison_shift_of_coordinates
    {C D B A : Type*} [Category C] [Category D] [Category B] [Category A]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ] [HasShift A ℤ]
    (G : ObjectProperty C) [G.IsStableUnderShift ℤ]
    (Q : C ⥤ D) (T : C ⥤ B) (R : B ⥤ A) (F : D ⥤ A)
    [Q.CommShift ℤ] [T.CommShift ℤ] [R.CommShift ℤ] [F.CommShift ℤ]
    (e : (G.ι ⋙ Q) ⋙ F ≅ G.ι ⋙ T ⋙ R)
    (h : ∀ (P : G.FullSubcategory) (r : ℤ), ∃ hP : G (P.obj⟦r⟧),
      (F.commShiftIso r).hom.app (Q.obj P.obj) ≫ (e.hom.app P)⟦r⟧' =
        F.map ((Q.commShiftIso r).inv.app P.obj) ≫ e.hom.app ⟨P.obj⟦r⟧, hP⟩ ≫
          R.map ((T.commShiftIso r).hom.app P.obj) ≫
            (R.commShiftIso r).hom.app (T.obj P.obj)) :
    let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
      (fun P ↦ G.le_shift n _ P.property)
    let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
      (fun P ↦ G.le_shift n _ P.property)
    let := G.fullyFaithfulι.hasShift sh shi
    let : G.ι.CommShift ℤ :=
      Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
    NatTrans.CommShift e.hom ℤ := by
  let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let := G.fullyFaithfulι.hasShift sh shi
  let : G.ι.CommShift ℤ :=
    Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
  constructor
  intro r
  ext P
  obtain ⟨hP, hP_eq⟩ := h P r
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app]
  rw [Functor.shiftFunctorIso_ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi r]
  simp only [shi, ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app]
  erw [Q.map_id]
  erw [(T ⋙ R).map_id]
  simp only [Category.id_comp, Functor.comp_obj, ObjectProperty.ι_obj]
  apply (cancel_epi (F.map ((Q.commShiftIso r).inv.app P.obj))).1
  simp only [Functor.comp_obj, Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [F.map_id, Category.id_comp]
  exact hP_eq

set_option maxHeartbeats 1200000 in
-- Several derived localization comparisons share large concrete coefficient presentations.
private theorem actualComparison_shift
    (i : PbcProperIntegralPullbackIdentification l E g)
    (q : integralDerivedPullback l E g ⋙ integralDetailedTransport X l E ≅
      integralDetailedTransport Y l E ⋙ completedReductionTower Y (pbcIntegralDatum l E) ⋙
        completedTowerPullback g (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) X)
    (hq : PbcProperIntegralModelMatching l E g i q)
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ)
    (hd : ShiftDescent l E g c d)
    (a : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E))
    (ha : ∀ K : PbcCompletedDerived Y (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K ≫ a.hom.app K =
        (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K) :
    let := d
    NatTrans.CommShift
      (q ≪≫ Functor.isoWhiskerLeft (integralDetailedTransport Y l E)
        (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
          (completedTowerPullback g (pbcIntegralDatum l E))
          (completedTowerRlim (pbcIntegralDatum l E) X)).symm ≪≫
        Functor.isoWhiskerLeft (integralDetailedTransport Y l E) a).hom ℤ := by
  let := c
  let := d
  obtain ⟨s, hs⟩ := ordinaryShift_exists l E g
  let := s
  let := hs
  let := good_stable l E Y
  let G := integralOperationsGoodComplex l E Y
  let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
    (fun P ↦ G.le_shift n _ P.property)
  let := G.fullyFaithfulι.hasShift sh shi
  let : G.ι.CommShift ℤ :=
    Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
  let : (integralOperationsGoodLocalization l E Y).CommShift ℤ := by
    change (G.ι ⋙ DerivedCategory.Q).CommShift ℤ
    infer_instance
  have : (G.ι ⋙ DerivedCategory.Q).EssSurj := goodLocalization_essSurj l E Y
  let : (integralOperationsPullbackOnGood l E g).CommShift ℤ := by
    change (G.ι ⋙ integralOperationsPullbackComplexFunctor l E g ⋙
      DerivedCategory.Q).CommShift ℤ
    infer_instance
  have descend (F H : DerivedCategory (integralTowerModules l E Y) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E))
      [F.CommShift ℤ] [H.CommShift ℤ] (t : F ⟶ H)
      [NatTrans.CommShift (Functor.whiskerLeft (G.ι ⋙ DerivedCategory.Q) t) ℤ] :
      NatTrans.CommShift t ℤ := by
    apply NatTrans.CommShift.of_whiskerLeft t (G.ι ⋙ DerivedCategory.Q)
    intro K
    exact ⟨(G.ι ⋙ DerivedCategory.Q).objPreimage K,
      ((G.ι ⋙ DerivedCategory.Q).objObjPreimageIso K).inv, by infer_instance⟩
  have hi : NatTrans.CommShift i.derivedIso.hom ℤ := by
    obtain ⟨hα, hβ⟩ := identificationCounits_shift l E g i
    let := hα
    let := hβ
    let α := (Functor.associator G.ι DerivedCategory.Q
      (integralDetailedTransport Y l E ⋙
        completedOrdinaryPullback g (pbcIntegralDatum l E))).hom ≫
      Functor.whiskerLeft G.ι (identificationTargetCounit l E g)
    let β := (Functor.associator G.ι DerivedCategory.Q
      (ordinaryIntegralDerivedPull l E g ⋙ integralDetailedTransport X l E)).hom ≫
      Functor.whiskerLeft G.ι (identificationSourceCounit l E g i)
    have heq : Functor.whiskerLeft (G.ι ⋙ DerivedCategory.Q) i.derivedIso.hom ≫ α = β := by
      ext P
      simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp, Functor.comp_obj,
        ObjectProperty.ι_obj] using
        identificationCounit_equation l E g i P
    have hβ (P : G.FullSubcategory) : IsIso (β.app P) := by
      have : IsIso (ordinaryIntegralPullComplexCounit l E g P.obj) :=
        ordinaryIntegralPullComplexCounit_isIso l E g P
      dsimp only [β, Functor.whiskerLeft_app, identificationSourceCounit,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Functor.associator_hom_app]
      simp only [Category.id_comp, ObjectProperty.ι_obj]
      rw [ordinaryComplexCounit_app]
      infer_instance
    let : ∀ P, IsIso (β.app P) := hβ
    let : IsIso β := NatIso.isIso_of_isIso_app β
    have hαeq : α = Functor.whiskerLeft (G.ι ⋙ DerivedCategory.Q) i.derivedIso.inv ≫ β := by
      rw [← heq]
      simp only [← Category.assoc, ← Functor.whiskerLeft_comp,
        Iso.inv_hom_id, Functor.whiskerLeft_id', Category.id_comp]
    let : IsIso α := by rw [hαeq]; infer_instance
    have : NatTrans.CommShift α ℤ := by dsimp only [α]; infer_instance
    have : NatTrans.CommShift β ℤ := by dsimp only [β]; infer_instance
    have : NatTrans.CommShift
        (Functor.whiskerLeft (G.ι ⋙ DerivedCategory.Q) i.derivedIso.hom) ℤ :=
      commShift_of_comp_iso _ α β heq
    exact descend _ _ i.derivedIso.hom
  have he : NatTrans.CommShift (integralDerivedPullbackComparison l E g).hom ℤ := by
    exact comparison_shift_of_coordinates G DerivedCategory.Q
      (integralOperationsPullbackComplexFunctor l E g) DerivedCategory.Q
      (integralDerivedPullback l E g) (integralDerivedPullbackComparison l E g) hd
  have hchain : NatTrans.CommShift (ordinaryIntegralCompletionNat l E g) ℤ := by
    constructor
    intro r
    apply NatTrans.ext
    funext P
    exact completionChain_shift l E g c hc P r
  have hη : NatTrans.CommShift (ordinaryIntegralCompletionComparison l E g) ℤ := by
    have hcounit := ordinaryCounit_shift l E g
    let := hcounit
    let := hchain
    let := he
    let β := (Functor.associator G.ι DerivedCategory.Q
      (ordinaryIntegralDerivedPull l E g)).hom ≫
      Functor.whiskerLeft G.ι (ordinaryComplexCounit l E g) ≫
      Functor.whiskerLeft G.ι
        (Functor.whiskerRight (ordinaryIntegralCompletionNat l E g) DerivedCategory.Q)
    have heq : Functor.whiskerLeft (G.ι ⋙ DerivedCategory.Q)
        (ordinaryIntegralCompletionComparison l E g) ≫
        (integralDerivedPullbackComparison l E g).hom = β := by
      ext P
      simpa only [β, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app, Category.id_comp,
        ordinaryComplexCounit_app, ordinaryIntegralCompletionNat_app,
        Functor.comp_obj, ObjectProperty.ι_obj, ordinaryIntegralCompletionComparison] using
        (ordinaryIntegralCompletionComparison_existsUnique l E g).exists.choose_spec P
    have : NatTrans.CommShift β ℤ := by dsimp only [β]; infer_instance
    have : NatTrans.CommShift
        (Functor.whiskerLeft (G.ι ⋙ DerivedCategory.Q)
          (ordinaryIntegralCompletionComparison l E g)) ℤ :=
      commShift_of_comp_iso _ (integralDerivedPullbackComparison l E g).hom β heq
    -- Descent is independent of the completed-coefficient target category.
    apply NatTrans.CommShift.of_whiskerLeft (ordinaryIntegralCompletionComparison l E g)
      (G.ι ⋙ DerivedCategory.Q)
    intro K
    exact ⟨(G.ι ⋙ DerivedCategory.Q).objPreimage K,
      ((G.ι ⋙ DerivedCategory.Q).objObjPreimageIso K).inv, by infer_instance⟩
  let b := q ≪≫ Functor.isoWhiskerLeft (integralDetailedTransport Y l E)
    (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
      (completedTowerPullback g (pbcIntegralDatum l E))
      (completedTowerRlim (pbcIntegralDatum l E) X)).symm ≪≫
    Functor.isoWhiskerLeft (integralDetailedTransport Y l E) a
  let t := i.derivedIso.inv ≫
    Functor.whiskerRight (ordinaryIntegralCompletionComparison l E g)
      (integralDetailedTransport X l E)
  have hunit : t ≫ b.hom = Functor.whiskerLeft (integralDetailedTransport Y l E)
      (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)) := by
    have hmatch : Functor.whiskerRight (ordinaryIntegralCompletionComparison l E g)
        (integralDetailedTransport X l E) ≫ q.hom =
        i.derivedIso.hom ≫ Functor.whiskerLeft (integralDetailedTransport Y l E)
          (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g) := by
      let ff := Classical.choice (good_whisker_fullyFaithful l E Y
        (PbcCompletedDerived X (pbcIntegralDatum l E)))
      apply ff.map_injective
      ext P
      change (integralDetailedTransport X l E).map
          ((ordinaryIntegralCompletionComparison l E g).app (DerivedCategory.Q.obj P.obj)) ≫
          q.hom.app (DerivedCategory.Q.obj P.obj) =
        i.derivedIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app
            ((integralDetailedTransport Y l E).obj (DerivedCategory.Q.obj P.obj))
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
        pbcActualStrictCompletedPullUnit, completedPullbackComparison,
        Functor.rightUnitor_inv_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id]
        using pbc_integral_completion_matching_on_good l E g i q hq P
    ext K
    have hm := congrArg (fun z ↦ z.app K) hmatch
    change (integralDetailedTransport X l E).map
        ((ordinaryIntegralCompletionComparison l E g).app K) ≫ q.hom.app K =
        i.derivedIso.hom.app K ≫ (pbcActualStrictCompletedPullUnit
          (pbcIntegralDatum l E) g).app ((integralDetailedTransport Y l E).obj K) at hm
    dsimp only [t, b, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app]
    simp only [Category.assoc]
    rw [← Category.assoc _ (q.hom.app K), hm]
    erw [Category.id_comp]
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, Category.comp_id]
      using ha ((integralDetailedTransport Y l E).obj K)
  let := hi
  let := hη
  have ht : NatTrans.CommShift t ℤ := by dsimp only [t]; infer_instance
  let := ht
  have hu : NatTrans.CommShift (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)) ℤ := by
    have : NatTrans.CommShift (pbcActualCompletionUnit (pbcIntegralDatum l E) X) ℤ :=
      (pbcActualCompletionShift_exists (pbcIntegralDatum l E) X).exists.choose_spec
    have heq : pbcActualCompletedPullUnit g (pbcIntegralDatum l E) =
        (pbcActualDerivedPull g (pbcIntegralDatum l E)).rightUnitor.inv ≫
          Functor.whiskerLeft (pbcActualDerivedPull g (pbcIntegralDatum l E))
            (pbcActualCompletionUnit (pbcIntegralDatum l E) X) := by
      ext K
      simp only [pbcActualCompletedPullUnit, NatTrans.comp_app,
        Functor.rightUnitor_inv_app, Category.id_comp]
    exact commShift_of_eq heq
  let := hu
  have : NatTrans.CommShift (t ≫ b.hom) ℤ := commShift_of_eq hunit
  apply commShift_of_precomp t b.hom
  intro K r f f' h
  apply (cancel_epi (b.inv.app (K⟦r⟧))).1
  apply (actualReflection (pbcIntegralDatum l E) X _ _
    (actualComplete_shift X (pbcIntegralDatum l E) _
      (pbcActualCompletedPull_isComplete g (pbcIntegralDatum l E)
        ((integralDetailedTransport Y l E).obj K)) r)).injective
  have huK := congrArg (fun z ↦ z.app (K⟦r⟧)) hunit
  change t.app (K⟦r⟧) ≫ b.hom.app (K⟦r⟧) =
    (pbcActualCompletionUnit (pbcIntegralDatum l E) X).app
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
        ((integralDetailedTransport Y l E).obj (K⟦r⟧))) at huK
  change _ ≫ b.inv.app (K⟦r⟧) ≫ f = _ ≫ b.inv.app (K⟦r⟧) ≫ f'
  rw [← huK]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h

set_option backward.inferInstanceAs.wrap false in
private instance coefficientFunctorShift (W : Scheme.{u}) :
    (purCoefficientModel l E W).functor.CommShift ℤ :=
  inferInstanceAs
    (((pbcRestrict (purCoefficientIso l E W).inv).mapDerivedCategory).CommShift ℤ)

set_option backward.inferInstanceAs.wrap false in
private instance coefficientInverseShift (W : Scheme.{u}) :
    (purCoefficientModel l E W).inverse.CommShift ℤ :=
  inferInstanceAs ((integralDetailedTransport W l E).CommShift ℤ)

-- Transport both the functors and their specified coherent shift structures.
private theorem transport_heq
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (P P' : C ⥤ D) (Q Q' : C' ⥤ D')
    [sP : P.CommShift ℤ] [sP' : P'.CommShift ℤ]
    [sQ : Q.CommShift ℤ] [sQ' : Q'.CommShift ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] (A S T : C ⥤ C') [A.CommShift ℤ]
    (hP : P = P') (hQ : Q = Q') (hsP : HEq sP sP') (hsQ : HEq sQ sQ')
    (a : A ≅ S) (b : S ≅ T) (z : T ⋙ Q ≅ P ⋙ F)
    (h : NatTrans.CommShift
      (Functor.isoWhiskerRight a Q ≪≫ (Functor.isoWhiskerRight b Q ≪≫ z)).hom ℤ)
    (z' : T ⋙ Q' ≅ P' ⋙ F) (hz : HEq z' z) :
    NatTrans.CommShift
      (Functor.isoWhiskerRight a Q' ≪≫ (Functor.isoWhiskerRight b Q' ≪≫ z')).hom ℤ := by
  subst P'
  subst Q'
  cases eq_of_heq hsP
  cases eq_of_heq hsQ
  cases eq_of_heq hz
  exact h

-- The canonical exact-restriction shift is the same dependent function of the ring iso.
private theorem coefficientShift_heq (W : Scheme.{u}) :
    HEq (coefficientFunctorShift l E W) (derived_commShift l E W) := by
  let σ (ρ : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E W) :
      (pbcRestrict ρ.inv).mapDerivedCategory.CommShift ℤ := inferInstance
  change HEq (σ (purCoefficientIso l E W))
    (σ (ImmersionCompletedPullback.completedRingIso l E W))
  have same (ρ τ : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E W) (h : ρ = τ) :
      HEq (σ ρ) (σ τ) := by
    cases h
    rfl
  exact same _ _ (ImmersionCompletedPullback.completedRingIso_eq l E W).symm


private theorem changedEquivalence_unit
    {C D : Type*} [Category C] [Category D] (H : C ≌ D)
    (F : D ⥤ C) (r : F ⋙ H.functor ≅ 𝟭 D) :
    (H.symm.changeFunctor ((Iso.isoCompInverse (H := H) r ≪≫
      Functor.leftUnitor H.inverse).symm)).unitIso.inv = r.hom := by
  ext K
  simp only [Equivalence.changeFunctor, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Iso.trans_hom, Iso.isoCompInverse,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  change H.functor.map (H.unitIso.hom.app (F.obj K)) ≫
    H.functor.map (H.inverse.map (r.hom.app K)) ≫ H.functor.map (𝟙 _) ≫
      H.counit.app K = r.hom.app K
  erw [H.functor.map_id, Category.id_comp]
  have hn := H.counit.naturality (r.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn, ← Category.assoc]
  change (H.functor.map (H.unitIso.hom.app (F.obj K)) ≫
    H.counitIso.hom.app (H.functor.obj (F.obj K))) ≫ r.hom.app K = r.hom.app K
  exact (congrArg (fun f ↦ f ≫ r.hom.app K)
    (H.functor_unitIso_comp (F.obj K))).trans (Category.id_comp _)

private theorem coefficientUnit (W : Scheme.{u}) :
    (purCoefficientModel l E W).unitIso.inv =
      (purDerivedCoefficientRoundTrip l E W).hom :=
  changedEquivalence_unit (integralDetailedTransport W l E).asEquivalence _ _

section
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem coefficientRoundTrip_shift (W : Scheme.{u}) :
    NatTrans.CommShift (purDerivedCoefficientRoundTrip l E W).hom ℤ := by
  let := (integralDetailedCoefficientRestriction_exact W l E).1
  let := (integralDetailedCoefficientRestriction_exact W l E).2
  have := Functor.commShift_mapDerivedCategoryCompIso_hom
    (purOrdinaryCoefficientModel l E W) (pbcIntegralTransportModules W l E)
  have := Functor.commShift_mapDerivedCategoryNatIso_hom
    (purOrdinaryCoefficientRoundTrip l E W)
  have := Functor.commShift_mapDerivedCategoryIdIso_hom
    (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
  change NatTrans.CommShift
    ((Functor.mapDerivedCategoryCompIso (purOrdinaryCoefficientModel l E W)
      (pbcIntegralTransportModules W l E)).inv ≫
      (Functor.mapDerivedCategoryNatIso (purOrdinaryCoefficientRoundTrip l E W)).hom ≫
        (Functor.mapDerivedCategoryIdIso _).hom) ℤ
  infer_instance

end

private theorem coefficientModel_shift (W : Scheme.{u}) :
    (purCoefficientModel l E W).CommShift ℤ := by
  have : NatTrans.CommShift (purCoefficientModel l E W).unitIso.inv ℤ := by
    rw [coefficientUnit]
    exact coefficientRoundTrip_shift l E W
  apply Equivalence.CommShift.mk' _ ℤ
  have : NatTrans.CommShift (purCoefficientModel l E W).unitIso.symm.hom ℤ := by
    assumption
  exact NatTrans.CommShift.of_iso_inv (purCoefficientModel l E W).unitIso.symm ℤ

private def recode
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ D) (E' : C' ≌ D') (F : D ⥤ D') (S : C ⥤ C')
    (q : F ⋙ E'.inverse ≅ E.inverse ⋙ S) :
    S ⋙ E'.functor ≅ E.functor ⋙ F :=
  Iso.compInverseIso (H := E'.symm)
    (Iso.isoInverseComp (G := E.symm) q.symm ≪≫
      (Functor.associator E.functor F E'.inverse).symm)

private theorem recode_literal
    (T : PbcCompletedDerived Y (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E))
    (q : integralDerivedPullback l E g ⋙ integralDetailedTransport X l E ≅
      integralDetailedTransport Y l E ⋙ T) :
    recode (purCoefficientModel l E Y) (purCoefficientModel l E X)
        (integralDerivedPullback l E g) T q =
      Iso.compInverseIso (H := (purCoefficientModel l E X).symm)
        (Iso.isoInverseComp (G := (purCoefficientModel l E Y).symm) q.symm ≪≫
          (Functor.associator (purCoefficientModel l E Y).functor
            (integralDerivedPullback l E g) (integralDetailedTransport X l E)).symm) := by
  ext K
  simp only [recode, Iso.compInverseIso, Iso.isoInverseComp, Iso.trans_hom,
    Iso.symm_hom, Equivalence.symm_inverse,
    Equivalence.symm_functor, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.map_comp,
    Category.assoc, Category.id_comp, Category.comp_id]

private theorem recode_shift
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (E : C ≌ D) (E' : C' ≌ D') [E.functor.CommShift ℤ] [E.inverse.CommShift ℤ]
    [E'.functor.CommShift ℤ] [E'.inverse.CommShift ℤ]
    [E.CommShift ℤ] [E'.CommShift ℤ]
    (F : D ⥤ D') (S : C ⥤ C') [F.CommShift ℤ] [S.CommShift ℤ]
    (q : F ⋙ E'.inverse ≅ E.inverse ⋙ S) [hq : NatTrans.CommShift q.hom ℤ] :
    NatTrans.CommShift (recode E E' F S q).hom ℤ := by
  dsimp only [recode, Iso.compInverseIso, Iso.isoInverseComp,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

-- Prove reassociation before specializing to the concrete completed-pullback functors.
private theorem recode_assoc
    {C D C' D' M N : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Category M] [Category N]
    (E : C ≌ D) (E' : C' ≌ D') (F : D ⥤ D')
    (S : C ⥤ M) (T : M ⥤ N) (U : N ⥤ C')
    (q : F ⋙ E'.inverse ≅ E.inverse ⋙ S ⋙ T ⋙ U) :
    recode E E' F ((S ⋙ T) ⋙ U)
        (q ≪≫ Functor.isoWhiskerLeft E.inverse (Functor.associator S T U).symm) =
      Functor.isoWhiskerRight (Functor.associator S T U) E'.functor ≪≫
        recode E E' F (S ⋙ T ⋙ U) q := by
  ext K
  simp only [recode, Iso.compInverseIso, Iso.isoInverseComp, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Equivalence.symm_inverse,
    Equivalence.symm_functor, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.assoc, Category.id_comp, Category.comp_id]

private theorem recode_comp
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ D) (E' : C' ≌ D') (F : D ⥤ D') (S A : C ⥤ C')
    (q : F ⋙ E'.inverse ≅ E.inverse ⋙ S) (a : S ≅ A) :
    recode E E' F A (q ≪≫ Functor.isoWhiskerLeft E.inverse a) =
      Functor.isoWhiskerRight a.symm E'.functor ≪≫ recode E E' F S q := by
  ext K
  simp only [recode, Iso.compInverseIso, Iso.isoInverseComp, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.map_comp,
    Category.id_comp, Category.assoc]
  simp only [Equivalence.symm_inverse, Equivalence.symm_functor]
  have hn := a.inv.naturality (E.symm.counitIso.inv.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj, Equivalence.symm_inverse,
    Equivalence.symm_functor] at hn
  rw [← E'.functor.map_comp_assoc, hn]
  simp only [Functor.map_comp, Category.assoc]

-- Equality isomorphisms implement the same dependent transport as a type cast.
private theorem moveIso_heq
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P P' : C ⥤ D) (Q Q' : C' ⥤ D') (F : D ⥤ D') (T : C ⥤ C')
    (hP : P = P') (hQ : Q = Q') (z : T ⋙ Q ≅ P ⋙ F) :
    HEq (Functor.isoWhiskerLeft T (eqToIso hQ.symm) ≪≫ z ≪≫
      Functor.isoWhiskerRight (eqToIso hP) F) z := by
  subst P'
  subst Q'
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl,
    Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl]
  rfl

set_option maxHeartbeats 1200000 in
-- Recoding compares two concrete presentations of the same exact coefficient restriction.
/-- The recoded strict Roos comparison respects the independently specified signed
Roos shift and the unit-normalized actual completed-pullback shift.
Source: Stacks 014E and 0941, 099N(2),(5); Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-a1-strict-integral-roos-transport-shifts).

Proof: the quotient augmentation commutes with termwise shifts, as is checked
on adjunction-unit generators in degree j+r. Product projections give the same
identity for its product lift. The ordinary completion chain has this product
augmentation in its first coordinate and zero in its second coordinate. The
first coordinate equation of hc therefore proves its signed shift square.
The universal ordinary derived counit fixes the ordinary pullback shift. The
counit normalization of i identifies its shift square on good representatives;
their resolving localization descends it. Likewise hd and the defining equation
of ordinaryIntegralCompletionComparison descend the augmentation shift square.
Model matching gives equality with the strict completion unit on good objects,
and faithfulness of the same localization gives that equality on all objects.
After composing with a, ha identifies this augmentation with the actual
completion unit. Both the augmentation and this unit commute with shifts.
Maps from a completed object to a complete shifted output are determined by
precomposition with the completion unit. This injectivity proves the shift
square for the composite of q and a, without a separate calculation of shifts
on resolved towers. The coefficient equivalence's inverse unit is the normalized
exact-restriction round trip, so its unit and counit commute with shifts.
Recoding the inverse composite across these equivalences gives the required
comparison; naturality moves a inverse across the coefficient unit. Every step
holds for all integer shifts, including zero and negative shifts. No detection
of morphisms by finite evaluations is used. -/
theorem strictIntegralRoosTransport_shifts
    (i : PbcProperIntegralPullbackIdentification l E g)
    (q : integralDerivedPullback l E g ⋙ integralDetailedTransport X l E ≅
      integralDetailedTransport Y l E ⋙ completedReductionTower Y (pbcIntegralDatum l E) ⋙
        completedTowerPullback g (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) X)
    (hq : PbcProperIntegralModelMatching l E g i q)
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ)
    (hd : ShiftDescent l E g c d)
    (a : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E))
    (ha : ∀ K : PbcCompletedDerived Y (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K ≫ a.hom.app K =
        (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K) :
    (fun [_d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ] ↦
      NatTrans.CommShift (Functor.isoWhiskerRight a.symm (derived l E X) ≪≫
        strictIntegralRoosTransport l E g q).hom ℤ) (_d := d) := by
  let := d
  let := coefficientModel_shift l E X
  let := coefficientModel_shift l E Y
  let q₀ := q ≪≫ Functor.isoWhiskerLeft (integralDetailedTransport Y l E)
    (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
      (completedTowerPullback g (pbcIntegralDatum l E))
      (completedTowerRlim (pbcIntegralDatum l E) X)).symm
  let b := q₀ ≪≫ Functor.isoWhiskerLeft (integralDetailedTransport Y l E) a
  have hb : NatTrans.CommShift b.hom ℤ := by
    simpa only [b, q₀, Iso.trans_hom, Category.assoc] using
      actualComparison_shift l E g i q hq c hc d hd a ha
  let := hb
  have hz : NatTrans.CommShift
      (recode (purCoefficientModel l E Y) (purCoefficientModel l E X)
        (integralDerivedPullback l E g) (pbcActualCompletedPull g (pbcIntegralDatum l E)) b).hom
      ℤ := by
    exact recode_shift (purCoefficientModel l E Y) (purCoefficientModel l E X)
      (integralDerivedPullback l E g) (pbcActualCompletedPull g (pbcIntegralDatum l E)) b
      (hq := hb)
  dsimp only [b] at hz
  have hr := recode_comp (purCoefficientModel l E Y) (purCoefficientModel l E X)
    (integralDerivedPullback l E g) (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g)
    (pbcActualCompletedPull g (pbcIntegralDatum l E)) q₀ a
  erw [hr] at hz
  let T := completedReductionTower Y (pbcIntegralDatum l E) ⋙
    completedTowerPullback g (pbcIntegralDatum l E) ⋙ completedTowerRlim (pbcIntegralDatum l E) X
  let z := Iso.compInverseIso (H := (purCoefficientModel l E X).symm)
    (Iso.isoInverseComp (G := (purCoefficientModel l E Y).symm) q.symm ≪≫
      (Functor.associator (purCoefficientModel l E Y).functor
        (integralDerivedPullback l E g) (integralDetailedTransport X l E)).symm)
  let j (w : T ⋙ derived l E X ≅ integral l E g) :=
    Functor.isoWhiskerRight a.symm (derived l E X) ≪≫
      (Functor.isoWhiskerRight
        (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
          (completedTowerPullback g (pbcIntegralDatum l E))
          (completedTowerRlim (pbcIntegralDatum l E) X)) (derived l E X) ≪≫ w)
  have hr₀ : recode (purCoefficientModel l E Y) (purCoefficientModel l E X)
      (integralDerivedPullback l E g)
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) q₀ =
      Functor.isoWhiskerRight
        (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
          (completedTowerPullback g (pbcIntegralDatum l E))
          (completedTowerRlim (pbcIntegralDatum l E) X))
        (purCoefficientModel l E X).functor ≪≫ z := by
    have h := recode_assoc (purCoefficientModel l E Y) (purCoefficientModel l E X)
      (integralDerivedPullback l E g) (completedReductionTower Y (pbcIntegralDatum l E))
      (completedTowerPullback g (pbcIntegralDatum l E))
      (completedTowerRlim (pbcIntegralDatum l E) X) q
    conv_rhs at h => rw [recode_literal l E g T q]
    exact h
  have hJ : NatTrans.CommShift
      (Functor.isoWhiskerRight a.symm (purCoefficientModel l E X).functor ≪≫
        (Functor.isoWhiskerRight
          (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
            (completedTowerPullback g (pbcIntegralDatum l E))
            (completedTowerRlim (pbcIntegralDatum l E) X))
          (purCoefficientModel l E X).functor ≪≫ z)).hom ℤ := by
    rw [hr₀] at hz
    exact hz
  have H (w : T ⋙ derived l E X ≅ integral l E g) (hw : HEq w z) :
      NatTrans.CommShift (j w).hom ℤ := by
    exact transport_heq (purCoefficientModel l E Y).functor (derived l E Y)
      (purCoefficientModel l E X).functor (derived l E X)
      (sP := coefficientFunctorShift l E Y) (sP' := derived_commShift l E Y)
      (sQ := coefficientFunctorShift l E X) (sQ' := derived_commShift l E X)
      (integralDerivedPullback l E g) (pbcActualCompletedPull g (pbcIntegralDatum l E))
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) T
      (strictIntegralCoefficientModel_eq l E Y) (strictIntegralCoefficientModel_eq l E X)
      (coefficientShift_heq l E Y) (coefficientShift_heq l E X) a.symm
      (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
        (completedTowerPullback g (pbcIntegralDatum l E))
        (completedTowerRlim (pbcIntegralDatum l E) X)) z hJ w hw
  let w := Functor.isoWhiskerLeft T
      (eqToIso (strictIntegralCoefficientModel_eq l E X).symm) ≪≫ z ≪≫
    Functor.isoWhiskerRight (eqToIso (strictIntegralCoefficientModel_eq l E Y))
      (integralDerivedPullback l E g)
  have hw : HEq w z := moveIso_heq (purCoefficientModel l E Y).functor (derived l E Y)
    (purCoefficientModel l E X).functor (derived l E X) (integralDerivedPullback l E g) T
    (strictIntegralCoefficientModel_eq l E Y) (strictIntegralCoefficientModel_eq l E X) z
  have hh := H w hw
  simpa only [strictIntegralRoosTransport, j, w, z, T] using hh


end WeilConjectures.IntegralCompletedComparison
