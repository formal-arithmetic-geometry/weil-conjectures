/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import all WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import all WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransportNatural
import all WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransport
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # One-step point transport on the finite regular coefficient unit

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
step 4 (blueprint: lem-zl-finite-point-transport-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantGeometricStalkUnit

attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  coefficientComplexModuleDerived pointScalarModuleDerived pointCompletedSheafDerived
  pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits in
private theorem unit_generator {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (m : ℕ) (V : Y.ProEt)
    (a : (integralCoefficientSheaf l E Y m).obj.obj (op V)) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (((inverseImageFiniteIntrinsicPullbackComparison g
      (Padic.coefficientExtensionRing l E (m + 1))).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E g m).val.app (op ((proEtaleBaseChange g).obj V)))
        (integralOperationsPullbackGenerator l E g m
          (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) V a) =
      (coefficientProEtaleDirectRingMap.{u, u} g (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).hom.app (op V) a := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} g (CommRingCat.of
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))
  let adj₂ := sfIntrinsicConstantModuleAdjunction g
    (Padic.coefficientExtensionRing l E (m + 1))
  have h := adj₁.unit_leftAdjointUniq_hom_app adj₂
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))
  have hv := congrArg (fun z ↦ z.val.app (op V) a) h
  change (finiteUnitHom l E g m).val.app _
    (((adj₁.leftAdjointUniq adj₂).hom.app
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app _
      ((adj₁.unit.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
        (op V) a)) = _
  change (((adj₁.leftAdjointUniq adj₂).hom.app
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
    (op ((proEtaleBaseChange g).obj V)))
      ((adj₁.unit.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
        (op V) a) =
        (adj₂.unit.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
          (op V) a at hv
  exact (congrArg ((finiteUnitHom l E g m).val.app _) hv).trans
    (finiteUnitHom_generator l E g m V a)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  coefficientComplexModuleDerived pointScalarModuleDerived pointCompletedSheafDerived
  pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits in
private theorem comparison_unit_apply {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (m : ℕ) (U : X.ProEt)
    (x : (integralCoefficientSheaf l E Y m).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U))) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    let M := SheafOfModules.unit (integralCoefficientSheaf l E Y m)
    let β := (inverseImageFiniteIntrinsicPullbackComparison g
      (Padic.coefficientExtensionRing l E (m + 1))).hom.app M ≫ finiteUnitHom l E g m
    (β.val.app (op U)) (((finiteModuleComparison l E g m).app M).val.app (op U) x) =
      (inverseImageFiniteCoefficientMap l E g m).hom.app (op U) x := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let M := SheafOfModules.unit (integralCoefficientSheaf l E Y m)
  let β := (inverseImageFiniteIntrinsicPullbackComparison g
    (Padic.coefficientExtensionRing l E (m + 1))).hom.app M ≫ finiteUnitHom l E g m
  have hn := PresheafOfModules.naturality_apply β.val (proEtaleIsoCommaArrow g U).op
    (integralOperationsPullbackGenerator l E g m M
      ((proEtaleIsoPostcompose g).obj U) x)
  change β.val.app (op U)
    (((integralOperationsLevelPullback l E g m).obj M).val.map
      (proEtaleIsoCommaArrow g U).op
      (integralOperationsPullbackGenerator l E g m M
        ((proEtaleIsoPostcompose g).obj U) x)) = _
  refine hn.trans ?_
  change (integralCoefficientSheaf l E X m).obj.map (proEtaleIsoCommaArrow g U).op
    (β.val.app _ (integralOperationsPullbackGenerator l E g m M
      ((proEtaleIsoPostcompose g).obj U) x)) = _
  erw [unit_generator]
  exact congrArg (fun z ↦ z.hom.app (op U) x)
    (constantRingViaUnit_eq.{u, u} g (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  coefficientComplexModuleDerived pointScalarModuleDerived pointCompletedSheafDerived
  pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits in
private theorem transport_on_complex (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (m : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) m) ℤ) :
    frobeniusPointTransportFinite.{u} D l hl E m (DerivedCategory.Q.obj K) =
      frobeniusPointTransportFiniteComplex.{u} D l hl E m K := by
  let g := (frobeniusPointIso D).hom
  let S : integralOperationsFiniteModules l E (Spec (.of D.k)) m ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) :=
    pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))
  let H := inverseImageFiniteModules.{u, u} l E g m
  letI : S.Additive := pointFiniteSectionsAdditive D.k _
  letI : PreservesFiniteLimits S := pointFibreFiniteLimits D _
  letI : PreservesFiniteColimits S := pointFibreFiniteColimits D _
  letI : IsIso (inverseImageFiniteCoefficientMap l E g m) :=
    isoSectionwiseConstantMap_isIso _ _
  letI : H.Additive := isoSectionwiseModuleInverseImage_additive _ _
  letI : PreservesFiniteLimits H := isoSectionwiseModuleInverseImage_limits _ _
  letI : PreservesFiniteColimits H := isoSectionwiseModuleInverseImage_colimits _ _
  let Sd := S.mapDerivedCategory
  let Hd := H.mapDerivedCategory
  let T := finiteDerivedPullback.{u} l E m g
  have : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let e := inverseImageFiniteIntrinsicPullbackComparison g
    (Padic.coefficientExtensionRing l E (m + 1))
  obtain ⟨σ, _, hσ⟩ := naturalFiniteSigmaDerived D l E m
  obtain ⟨κ, hk, _⟩ := inverseImagePullbackComparisonFinite_natural.{u, u, 0, 0} l E g
    (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) m
  letI : (integralOperationsLevelPullback l E g m).Additive :=
    integralOperationsLevelPullback_additive l E g m
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E g m) :=
    inverseImageFinitePullback_limits l E g m
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E g m) :=
    inverseImageFinitePullback_colimits l E g m
  letI : (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E g m
  letI : PreservesFiniteLimits (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))) :=
    inverseImageFinitePullback_limits l E g m
  letI : PreservesFiniteColimits (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))) :=
    inverseImageFinitePullback_colimits l E g m
  let κ' : Hd ⟶ T := κ ≫ (Functor.mapDerivedCategoryNatIso e).hom
  let τ : Sd ⟶ T ⋙ Sd := σ ≫ Functor.whiskerRight κ' Sd
  have hτ (L : CochainComplex
      (integralOperationsFiniteModules l E (Spec (.of D.k)) m) ℤ) :
      τ.app (DerivedCategory.Q.obj L) =
        frobeniusPointTransportFiniteComplex D l hl E m L := by
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, κ']
    rw [hσ, hk]
    simp only [frobeniusPointTransportFiniteComplex, inverseImagePullbackComparisonFiniteIntrinsic,
      Functor.map_comp, Category.assoc]
    rfl
  have h (N) : τ.app N = frobeniusPointTransportFinite D l hl E m N := by
    rw [conjugate_component τ (DerivedCategory.Q.objObjPreimageIso N), hτ]
    rfl
  exact (h _).symm.trans (hτ K)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  coefficientComplexModuleDerived pointScalarModuleDerived pointCompletedSheafDerived
  pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits in
private theorem chain_unit (D : FiniteFieldDatum.{u}) (m : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    letI := inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom m
    letI := inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom m
    let M := SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)
    let K := (CochainComplex.singleFunctor _ 0).obj M
    let L := integralOperationsLevelPullback.{u, u} l E (frobeniusPointIso D).hom m
    let β := (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
      (Padic.coefficientExtensionRing l E (m + 1))).hom.app M ≫
        finiteUnitHom l E (frobeniusPointIso D).hom m
    frobeniusPointFiniteSigma D l E m K ≫
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapHomologicalComplex (.up ℤ)).map
        (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom m K ≫
          (L.mapCochainComplexSingleFunctor 0).hom.app M ≫
            (CochainComplex.singleFunctor _ 0).map β) = 𝟙 _ := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let := inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom m
  let := inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom m
  let M := SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)
  let K := (CochainComplex.singleFunctor _ 0).obj M
  let S : integralOperationsFiniteModules l E (Spec (.of D.k)) m ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) :=
    pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))
  letI : S.Additive := pointFiniteSectionsAdditive D.k _
  letI : IsIso (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom m) :=
    isoSectionwiseConstantMap_isIso _ _
  letI : (inverseImageFiniteModules.{u, u} l E (frobeniusPointIso D).hom m).Additive :=
    isoSectionwiseModuleInverseImage_additive _ _
  have hq : inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom m K =
      ((finiteModuleComparison l E (frobeniusPointIso D).hom m).mapHomologicalComplex
        (.up ℤ)).app K := by
    apply (inverseImageFiniteComparison_existsUnique l E (frobeniusPointIso D).hom m K).unique
    · exact (inverseImageFiniteComparison_existsUnique l E
        (frobeniusPointIso D).hom m K).exists.choose_spec
    · intro i U x
      rfl
  dsimp only
  rw [hq]
  apply (cancel_epi ((S.mapCochainComplexSingleFunctor 0).inv.app M)).1
  apply HomologicalComplex.from_single_hom_ext (j := (0 : ℤ))
  simp only [Functor.map_comp, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, HomologicalComplex.id_f]
  simp only [(integralOperationsLevelPullback l E
    (frobeniusPointIso D).hom m).map_id]
  ext x
  let g := (frobeniusPointIso D).hom
  let U := ProEt.mk (𝟙 (Spec (.of D.k)))
  let β := (inverseImageFiniteIntrinsicPullbackComparison g
    (Padic.coefficientExtensionRing l E (m + 1))).hom.app M ≫ finiteUnitHom l E g m
  change β.val.app (op U)
    (((finiteModuleComparison l E g m).app M).val.app (op U)
      ((frobeniusPointFiniteSigma D l E m K).f 0 x)) = x
  have hσ := congrFun (eq_of_heq (finiteSigma_apply D l E m K 0)) x
  rw [hσ, comparison_unit_apply]
  have hs : Function.Surjective
      (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1))) :=
    (bijective_toSheafify_app_of_iso (Iso.refl (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))))).surjective
  obtain ⟨a, rfl⟩ := hs x
  exact (congrArg ((inverseImageFiniteCoefficientMap l E g m).hom.app (op U))
    (pointFiniteScalar_restriction D l E m a).symm).trans
    (congrArg (fun z ↦ z.hom.app (op U)
    (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1)) a))
      (IsIso.inv_hom_id (inverseImageFiniteCoefficientMap l E g m)))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  coefficientComplexModuleDerived pointScalarModuleDerived pointCompletedSheafDerived
  pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits in
private theorem finitePointTransport_unit_aux
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (m : ℕ) :
    frobeniusPointTransportFinite D l hl E m
        (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≫
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          (finiteUnit l E (frobeniusPointIso D).hom m).hom = 𝟙 _ := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let := inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom m
  let := inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom m
  let M := SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)
  let K := (CochainComplex.singleFunctor _ 0).obj M
  let S : integralOperationsFiniteModules l E (Spec (.of D.k)) m ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) :=
    pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))
  let H := inverseImageFiniteModules.{u, u} l E (frobeniusPointIso D).hom m
  let L := integralOperationsLevelPullback.{u, u} l E (frobeniusPointIso D).hom m
  letI : S.Additive := pointFiniteSectionsAdditive D.k _
  letI : PreservesFiniteLimits S := pointFibreFiniteLimits D _
  letI : PreservesFiniteColimits S := pointFibreFiniteColimits D _
  letI : IsIso (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom m) :=
    isoSectionwiseConstantMap_isIso _ _
  letI : H.Additive := isoSectionwiseModuleInverseImage_additive _ _
  letI : PreservesFiniteLimits H := isoSectionwiseModuleInverseImage_limits _ _
  letI : PreservesFiniteColimits H := isoSectionwiseModuleInverseImage_colimits _ _
  letI : L.Additive := integralOperationsLevelPullback_additive l E _ m
  letI : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E _ m
  letI : PreservesFiniteLimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))) :=
    inverseImageFinitePullback_limits l E _ m
  letI : PreservesFiniteColimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))) :=
    inverseImageFinitePullback_colimits l E _ m
  let e := inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
    (Padic.coefficientExtensionRing l E (m + 1))
  let β := e.hom.app M ≫ finiteUnitHom l E (frobeniusPointIso D).hom m
  let b := inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom m K ≫
    (L.mapCochainComplexSingleFunctor 0).hom.app M ≫
      (CochainComplex.singleFunctor _ 0).map β
  have hu : inverseImagePullbackComparisonFiniteIntrinsic l (frobeniusPointIso D).hom E
      (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) m K ≫
        (finiteUnit l E (frobeniusPointIso D).hom m).hom =
      H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map b := by
    dsimp only [inverseImagePullbackComparisonFiniteIntrinsic, finiteUnit]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
    erw [reassoc_of% (Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor e M)]
    simp only [inverseImagePullbackComparisonFinite, Category.assoc]
    erw [Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app_assoc
      L M]
    rw [← (DerivedCategory.singleFunctor _ 0).map_comp]
    change H.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map (inverseImageFiniteComparisonComplex l E
        (frobeniusPointIso D).hom m K) ≫
      DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app M) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map β) = _
    simp only [← Functor.map_comp, b]
  change frobeniusPointTransportFinite D l hl E m (DerivedCategory.Q.obj K) ≫
    S.mapDerivedCategory.map (finiteUnit l E (frobeniusPointIso D).hom m).hom = 𝟙 _
  rw [transport_on_complex]
  dsimp only [frobeniusPointTransportFiniteComplex]
  simp only [Category.assoc]
  change S.mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (frobeniusPointFiniteSigma D l E m K) ≫
    S.mapDerivedCategoryFactors.inv.app _ ≫
    S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.inv.app K ≫
      inverseImagePullbackComparisonFiniteIntrinsic l (frobeniusPointIso D).hom E
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) m K) ≫
      S.mapDerivedCategory.map (finiteUnit l E (frobeniusPointIso D).hom m).hom = _
  rw [← S.mapDerivedCategory.map_comp, Category.assoc, hu]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  simp only [Category.assoc]
  erw [← S.mapDerivedCategoryFactors.inv.naturality b]
  simp only [Functor.comp_map]
  erw [← Functor.map_comp_assoc]
  erw [chain_unit l E D m]
  change S.mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (𝟙 ((S.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      S.mapDerivedCategoryFactors.inv.app K = 𝟙 _
  erw [DerivedCategory.Q.map_id, Category.id_comp]
  exact S.mapDerivedCategoryFactors.hom_inv_id_app K

/-- One restriction-and-coprojection transport preserves the regular coefficient unit.
Source: current blueprint, sec-zeta-weil/sk-thm-intfactors,
`prop-every-iterate-trace.proof.md`, constant-sheaf clause, reviewed expansion step 4.
(blueprint: lem-zl-finite-point-transport-unit).

Proof: compute on a constant section a of the regular coefficient sheaf at Spec k.
Restriction along geometric Frobenius leaves the value a unchanged. The inverse-image
colimit coprojection and sheafification send it to its constant class. The tensor
comparison inserts the tensor unit, and finiteUnit multiplies back to a by the
adjunction generator formula. Thus the composite on sections is the identity.
Every section is constant by bijectivity of sheafification at the final object of
Spec k. The exact single-complex comparison gives the identity in degree zero.
Naturality of transport and its localization formula remove the chosen representative
used in its definition. The computation includes the quotient with exponent one. -/
theorem finitePointTransport_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (m : ℕ) :
    frobeniusPointTransportFinite D l hl E m
        (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≫
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          (finiteUnit l E (frobeniusPointIso D).hom m).hom = 𝟙 _ :=
  finitePointTransport_unit_aux l E D hl m

end WeilConjectures.ConstantGeometricStalkUnit
