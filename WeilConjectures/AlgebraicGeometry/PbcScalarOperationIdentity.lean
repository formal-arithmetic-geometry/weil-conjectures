/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcScalarOperationShift
import all WeilConjectures.AlgebraicGeometry.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.PbcActualScalarPullbackSupplement

/-! # Identity coherence of scalar operation comparisons

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-operation-unit-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem scalarIdentityConjugate
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {R : D ⥤ C} (adj : S ⊣ R)
    {A AR : C ⥤ C} {B BR : D ⥤ D} (adjA : A ⊣ AR) (adjB : B ⊣ BR)
    (eA : AR ≅ 𝟭 C) (eB : BR ≅ 𝟭 D) (δ : BR ⋙ R ≅ R ⋙ AR)
    (hδ : δ.hom ≫ whiskerLeft R eA.hom = whiskerRight eB.hom R) :
    let a := ((conjugateIsoEquiv adjA Adjunction.id).symm eA).symm
    let b := ((conjugateIsoEquiv adjB Adjunction.id).symm eB).symm
    let χ := ((conjugateIsoEquiv (adj.comp adjB) (adjA.comp adj)).symm δ).symm
    χ.hom ≫ whiskerRight a.hom S = whiskerLeft S b.hom := by
  dsimp only
  let a := ((conjugateIsoEquiv adjA Adjunction.id).symm eA).symm
  let b := ((conjugateIsoEquiv adjB Adjunction.id).symm eB).symm
  let χ := ((conjugateIsoEquiv (adj.comp adjB) (adjA.comp adj)).symm δ).symm
  change χ.hom ≫ whiskerRight a.hom S = whiskerLeft S b.hom
  have ha : conjugateEquiv Adjunction.id adjA a.hom = eA.inv :=
    (conjugateEquiv Adjunction.id adjA).apply_symm_apply eA.inv
  have hb : conjugateEquiv adjB Adjunction.id b.inv = eB.hom :=
    (conjugateEquiv adjB Adjunction.id).apply_symm_apply eB.hom
  have h : χ.inv = whiskerRight a.hom S ≫
      (Functor.leftUnitor S).hom ≫ (Functor.rightUnitor S).inv ≫
        whiskerLeft S b.inv := by
    apply (conjugateEquiv (adj.comp adjB) (adjA.comp adj)).injective
    change (conjugateEquiv (adj.comp adjB) (adjA.comp adj))
      ((conjugateEquiv (adj.comp adjB) (adjA.comp adj)).symm δ.hom) = _
    rw [Equiv.apply_symm_apply]
    rw [← Category.assoc, ← Category.assoc]
    rw [← conjugateEquiv_comp _ (adj.comp Adjunction.id),
      ← conjugateEquiv_comp _ adj,
      ← conjugateEquiv_comp _ (Adjunction.id.comp adj)]
    rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
      conjugateEquiv_leftUnitor_hom]
    have hr : conjugateEquiv (adj.comp Adjunction.id) adj
        (Functor.rightUnitor S).inv = (Functor.leftUnitor R).hom := by
      apply (cancel_epi (Functor.leftUnitor R).inv).1
      calc
        _ = conjugateEquiv adj adj
            ((Functor.rightUnitor S).inv ≫ (Functor.rightUnitor S).hom) := by
          rw [← conjugateEquiv_rightUnitor_hom adj, conjugateEquiv_comp]
        _ = _ := by simp only [Iso.inv_hom_id, conjugateEquiv_id]
    rw [hr, ha, hb]
    change δ.hom = whiskerRight eB.hom R ≫ _ ≫ _ ≫ whiskerLeft R eA.inv
    ext X
    have he := congrArg (fun z ↦ z.app X) hδ
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at he
    simpa using (Iso.eq_comp_inv (eA.app (R.obj X))).2 he
  apply (cancel_epi χ.inv).1
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, h]
  ext X
  simp [Category.assoc]

private theorem scalarModuleIdentity
    (W : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φ : pbcAdicCompletion W dA ⟶ pbcAdicCompletion W dB)
    (hφ : pbcActualCoefficientRingMap W φ ≫ pbcActualStructureMap (𝟙 W) dB =
      pbcActualStructureMap (𝟙 W) dA ≫
        (proEtaleSheafDirectImage (𝟙 W) RingCat.{u + 1}).map
          (pbcActualCoefficientRingMap W φ)) :
    (pbcActualScalarOrdinaryPullIso (𝟙 W) dA dB φ φ hφ).hom ≫
        whiskerRight (pbcActualModulePullIdIso dA W).hom (pbcExtend φ) =
      whiskerLeft (pbcExtend φ) (pbcActualModulePullIdIso dB W).hom := by
  apply scalarIdentityConjugate (pbcScalarAdjunction φ)
    (pbcActualModuleAdjunction (𝟙 W) dA) (pbcActualModuleAdjunction (𝟙 W) dB)
    (pbcActualModuleDirectIdIso dA W) (pbcActualModuleDirectIdIso dB W)
    (pbcActualScalarRightIso (𝟙 W) dA dB φ φ hφ)
  ext N U x
  change ((pbcActualModuleDirectIdIso dA W).hom.app _).val.app U
      (((pbcActualScalarRightIso (𝟙 W) dA dB φ φ hφ).hom.app N).val.app U x) =
    ((pbcActualModuleDirectIdIso dB W).hom.app N).val.app U x
  change ((pbcActualModulePush (𝟙 W) dB).obj N).val.obj U at x
  have hd : ((pbcActualScalarRightIso (𝟙 W) dA dB φ φ hφ).hom.app N).val.app U x = x :=
    (pbcActualScalarRightIso_exists (𝟙 W) dA dB φ φ hφ).exists.choose_spec N U x
  have he := congrArg
    (fun z ↦ ((pbcActualModuleDirectIdIso dA W).hom.app
      ((SheafOfModules.restrictScalars (pbcActualCoefficientRingMap W φ)).obj N)).val.app U z)
    hd
  refine he.trans ?_
  exact ((pbcActualModuleDirectIdIso_exists dA W).exists.choose_spec
    ((SheafOfModules.restrictScalars (pbcActualCoefficientRingMap W φ)).obj N) U.unop x).trans
    ((pbcActualModuleDirectIdIso_exists dB W).exists.choose_spec N U.unop x).symm

private theorem scalarComplexIdentity
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (S : C ⥤ D) (A : C ⥤ C) (B : D ⥤ D) [S.Additive] [A.Additive] [B.Additive]
    (a : A ≅ 𝟭 C) (b : B ≅ 𝟭 D) (χ : S ⋙ B ≅ A ⋙ S)
    (hχ : χ.hom ≫ whiskerRight a.hom S = whiskerLeft S b.hom)
    (P : CochainComplex C ℤ) :
    let χc := Functor.mapHomologicalComplexCompIso
        (F := S) (G := B) (Iso.refl _) (.up ℤ) ≪≫
      NatIso.mapHomologicalComplex χ (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (F := A) (G := S) (Iso.refl _) (.up ℤ)).symm
    let ac := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (.up ℤ)
    let bc := NatIso.mapHomologicalComplex b (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso D (.up ℤ)
    χc.hom.app P ≫ (S.mapHomologicalComplex (.up ℤ)).map (ac.hom.app P) =
      bc.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  change (𝟙 _ ≫ χ.hom.app (P.X n) ≫ 𝟙 _) ≫
      S.map (a.hom.app (P.X n) ≫ 𝟙 _) = b.hom.app (S.obj (P.X n)) ≫ 𝟙 _
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id] using
    congrArg (fun z ↦ z.app (P.X n)) hχ

private theorem scalarDerivedIdentity
    (W : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φ : pbcAdicCompletion W dA ⟶ pbcAdicCompletion W dB)
    (hφ : pbcActualCoefficientRingMap W φ ≫ pbcActualStructureMap (𝟙 W) dB =
      pbcActualStructureMap (𝟙 W) dA ≫
        (proEtaleSheafDirectImage (𝟙 W) RingCat.{u + 1}).map
          (pbcActualCoefficientRingMap W φ)) :
    (pbcActualScalarDerivedPullIso (𝟙 W) dA dB φ φ hφ).hom ≫
        whiskerRight (pbcActualDerivedPullIdIso dA W).hom (pbcDerivedExtend φ) =
      whiskerLeft (pbcDerivedExtend φ) (pbcActualDerivedPullIdIso dB W).hom := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let C := pbcDerivedExtend φ
  let S := (pbcExtend φ).mapHomologicalComplex (.up ℤ)
  let LB := pbcActualDerivedPull (𝟙 W) dB
  let GA := (pbcActualModulePull (𝟙 W) dA).mapHomologicalComplex (.up ℤ)
  let χ := (pbcActualScalarDerivedPullIso (𝟙 W) dA dB φ φ hφ).hom
  let a := (pbcActualDerivedPullIdIso dA W).hom
  let b := (pbcActualDerivedPullIdIso dB W).hom
  let s := complexCounit (pbcExtend φ) C (pbcExtensionCounit φ)
  let t := χ ≫ whiskerRight a C
  let v := whiskerLeft C b
  have good (P : CochainComplex (pbcModules W (pbcAdicCompletion W dA)) ℤ)
      (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pbcAdicCompletion W dA) (P.X n)) :
      t.app (DerivedCategory.Q.obj P) = v.app (DerivedCategory.Q.obj P) := by
    have hflat (n : ℤ) : exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory
          (pbcAdicCompletion W dA)) (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X n)) (hf n)
    have hs := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      φ P (pbcExtend φ) (pbcExtensionExistence φ).choose_spec.choose
      (pbcExtensionExistence φ).choose_spec.choose_spec.choose hp hflat
    have hsf (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pbcAdicCompletion W dB) ((S.obj P).X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ ((S.obj P).X n)).symm (hs.2 n)
    have ha := (pbcActualDerivedPullIdIso_exists dA W).exists.choose_spec P hp hf
    have hb := (pbcActualDerivedPullIdIso_exists dB W).exists.choose_spec
      (S.obj P) hs.1 hsf
    have hχ := (pbcActualScalarDerivedPullIso_exists (𝟙 W) dA dB φ φ hφ).exists.choose_spec
      P hp hf
    have hm : (pbcActualScalarOrdinaryPullComplexIso (𝟙 W) dA dB φ φ hφ).hom.app P ≫
        S.map ((pbcActualModulePullIdComplexIso dA W).hom.app P) =
      (pbcActualModulePullIdComplexIso dB W).hom.app (S.obj P) := by
      exact scalarComplexIdentity (pbcExtend φ)
        (pbcActualModulePull (𝟙 W) dA) (pbcActualModulePull (𝟙 W) dB)
        (pbcActualModulePullIdIso dA W) (pbcActualModulePullIdIso dB W)
        (pbcActualScalarOrdinaryPullIso (𝟙 W) dA dB φ φ hφ)
        (scalarModuleIdentity W dA dB φ hφ) P
    have := scalar_counit_iso W φ P hp
    apply (cancel_mono (pbcComplexCounit φ P)).1
    change (χ.app (DerivedCategory.Q.obj P) ≫ C.map (a.app _)) ≫
        pbcComplexCounit φ P = b.app (C.obj (DerivedCategory.Q.obj P)) ≫
          pbcComplexCounit φ P
    have hn := s.naturality ((pbcActualModulePullIdComplexIso dA W).hom.app P)
    change C.map (DerivedCategory.Q.map _) ≫ pbcComplexCounit φ P =
      pbcComplexCounit φ (GA.obj P) ≫ DerivedCategory.Q.map (S.map _) at hn
    calc
      _ = (χ.app (DerivedCategory.Q.obj P) ≫ C.map (pbcActualPullComplexCounit (𝟙 W) dA P) ≫
          pbcComplexCounit φ (GA.obj P)) ≫
            DerivedCategory.Q.map (S.map ((pbcActualModulePullIdComplexIso dA W).hom.app P)) := by
        rw [show a.app (DerivedCategory.Q.obj P) = _ from ha, C.map_comp]
        simp only [Category.assoc]
        rw [hn]
      _ = ((pbcActualDerivedPull (𝟙 W) dB).map (pbcComplexCounit φ P) ≫
          pbcActualPullComplexCounit (𝟙 W) dB (S.obj P) ≫
          DerivedCategory.Q.map
            ((pbcActualScalarOrdinaryPullComplexIso (𝟙 W) dA dB φ φ hφ).hom.app P)) ≫
            DerivedCategory.Q.map (S.map ((pbcActualModulePullIdComplexIso dA W).hom.app P)) :=
        congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
          (S.map ((pbcActualModulePullIdComplexIso dA W).hom.app P))) hχ
      _ = LB.map (pbcComplexCounit φ P) ≫
          (pbcActualPullComplexCounit (𝟙 W) dB (S.obj P) ≫
            DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso dB W).hom.app
              (S.obj P))) := by
        simp only [Category.assoc]
        rw [← DerivedCategory.Q.map_comp, hm]
      _ = _ := by
        rw [← hb]
        exact b.naturality (pbcComplexCounit φ P)
  ext M
  let P₀ := DerivedCategory.Q.objPreimage M
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u} P₀
  have hf' (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion W dA) (P.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ _).symm (hf n)
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  let e : DerivedCategory.Q.obj P ≅ M :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  change t.app M = v.app M
  apply (cancel_epi (((C ⋙ LB).mapIso e).hom)).1
  change (C ⋙ LB).map e.hom ≫ t.app M = (C ⋙ LB).map e.hom ≫ v.app M
  rw [t.naturality, v.naturality, good P hp hf']
  simp only [Functor.comp_map, Functor.id_map]

private theorem scalarMateIdentity
    {C D : Type*} [Category C] [Category D]
    {A AR : C ⥤ C} {B BR : D ⥤ D} (adjA : A ⊣ AR) (adjB : B ⊣ BR)
    (S : C ⥤ D) (a : A ≅ 𝟭 C) (b : B ≅ 𝟭 D)
    (χ : S ⋙ B ⟶ A ⋙ S)
    (hχ : ∀ K, χ.app K ≫ S.map (a.hom.app K) = b.hom.app (S.obj K)) (K : C) :
    (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ χ)).natTrans.app K ≫
        (conjugateEquiv adjB Adjunction.id b.inv).app (S.obj K) =
      S.map ((conjugateEquiv adjA Adjunction.id a.inv).app K) := by
  let r := conjugateEquiv adjB Adjunction.id b.inv
  have hm : (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ χ)).natTrans.app K =
      adjB.unit.app (S.obj (AR.obj K)) ≫ BR.map (χ.app (AR.obj K)) ≫
        BR.map (S.map (adjA.counit.app K)) := by
    simp [mateEquiv]
  have hu := unit_conjugateEquiv adjB Adjunction.id b.inv (S.obj (AR.obj K))
  change adjB.unit.app _ ≫ r.app _ = 𝟙 _ ≫ b.inv.app _ at hu
  rw [Category.id_comp] at hu
  have hx := hχ (AR.obj K)
  have hx' : b.inv.app (S.obj (AR.obj K)) ≫ χ.app (AR.obj K) =
      S.map (a.inv.app (AR.obj K)) := by
    apply (cancel_mono (S.map (a.hom.app (AR.obj K)))).1
    rw [Category.assoc, hx, Iso.inv_hom_id_app]
    rw [← S.map_comp, Iso.inv_hom_id_app, S.map_id]
    rfl
  have hn : BR.map (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K)) ≫
      r.app (S.obj K) = r.app (B.obj (S.obj (AR.obj K))) ≫
        (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K)) := by
    simpa only [Functor.comp_obj, Functor.id_obj, Functor.id_map] using
      r.naturality (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K))
  calc
    _ = (adjB.unit.app (S.obj (AR.obj K)) ≫
        BR.map (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K))) ≫
          r.app (S.obj K) := by
      rw [hm, BR.map_comp]
    _ = (adjB.unit.app (S.obj (AR.obj K)) ≫ r.app (B.obj (S.obj (AR.obj K)))) ≫
        (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K)) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ adjB.unit.app (S.obj (AR.obj K)) ≫ z) hn
    _ = (b.inv.app (S.obj (AR.obj K)) ≫ χ.app (AR.obj K)) ≫
        S.map (adjA.counit.app K) := by rw [hu, Category.assoc]
    _ = S.map (a.inv.app (AR.obj K)) ≫ S.map (adjA.counit.app K) := by rw [hx']
    _ = _ := by rw [← S.map_comp, conjugateEquiv_adjunction_id]

/-- The scalar comparisons respect identity scheme morphisms with their canonical units.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-unit-coherence).
Proof: the ordinary identity comparison is restriction along identity fiber-product
pasting. The coefficient square on its sections is the identity coefficient square.
Its tensor-adjunction conjugate therefore has the ordinary tensor-unit formula.
The derived counits descend that formula, and conjugacy gives the same identity
for the direct-image mate. These are precisely the two displayed equations. -/
theorem pbcScalarOperations_identity (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    ((pbcScalarDirectImageIso l E F i (𝟙 W)).hom.app K ≫
        (pbcActualDerivedDirectIdIso (pbcIntegralDatum l F) W).hom.app
          ((pbcEmbeddingAmbientTensor l E F i W).obj K) =
      (pbcEmbeddingAmbientTensor l E F i W).map
        ((pbcActualDerivedDirectIdIso (pbcIntegralDatum l E) W).hom.app K)) ∧
    ((pbcScalarOrdinaryPullIso l E F i (𝟙 W)).hom.app K ≫
        (pbcEmbeddingAmbientTensor l E F i W).map
          ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) W).hom.app K) =
      (pbcActualDerivedPullIdIso (pbcIntegralDatum l F) W).hom.app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K)) := by
  let dA := pbcIntegralDatum l E
  let dB := pbcIntegralDatum l F
  let φ := pbcScalarCoefficientMap l E F i W
  let hφ := pbcScalarCoefficientStructureSquare l E F i (𝟙 W)
  have ho := scalarDerivedIdentity W dA dB φ hφ
  constructor
  · rw [pbcScalarDirectImageIso_hom]
    unfold pbcScalarDirectImageMap pbcActualScalarDirectImageMap pbcActualDerivedDirectIdIso
    exact scalarMateIdentity (pbcActualDerivedAdjunction (𝟙 W) dA)
      (pbcActualDerivedAdjunction (𝟙 W) dB) (pbcDerivedExtend φ)
      (pbcActualDerivedPullIdIso dA W) (pbcActualDerivedPullIdIso dB W)
      (pbcActualScalarDerivedPullIso (𝟙 W) dA dB φ φ hφ).hom
      (fun M ↦ congrArg (fun z ↦ z.app M) ho) K
  · unfold pbcScalarOrdinaryPullIso
    exact congrArg (fun z ↦ z.app K) ho

/-- Pasting calculations for abstract functors before specializing completion and pullback. -/
private theorem scalarNaturalityPasting
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G)
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) {W : D} (c : G.obj Z ⟶ W) :
    F.map a ≫ η.app Y ≫ (G.map b ≫ c) =
      F.map (a ≫ b) ≫ (η.app Z ≫ c) := by
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← η.naturality_assoc b]

private theorem scalarMapTwoSquares
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z U : C} {V W V' : D}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ U} {d : U ⟶ Z}
    {v : F.obj Z ⟶ V} {w : V ⟶ W} {v' : F.obj Z ⟶ V'} {w' : V' ⟶ W}
    (hab : a ≫ b = c ≫ d) (hvw : v ≫ w = v' ≫ w') :
    F.map (a ≫ b) ≫ (v ≫ w) = F.map c ≫ F.map d ≫ v' ≫ w' := by
  rw [hab, hvw, F.map_comp]
  simp only [Category.assoc]

private theorem scalarMapThreeComposite
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₀ X₁ X₂ X₃ X₄ : C}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₄}
    {d : X₀ ⟶ X₃} {e : X₃ ⟶ X₄}
    (h : a ≫ b ≫ c = d ≫ e)
    {Y Z : D} (t : Y ⟶ Z) (v : Z ⟶ F.obj X₀) :
    (t ≫ v ≫ F.map a) ≫ F.map b ≫ F.map c =
      t ≫ v ≫ F.map d ≫ F.map e := by
  simp only [Category.assoc]
  rw [← F.map_comp, ← F.map_comp, h, F.map_comp]

private theorem scalarCompletedPasting
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F G : A ⥤ B) (η : F ⟶ G) (H : C ⥤ B)
    {X₀ X₁ X₂ X₃ : A}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₃} {t : X₀ ⟶ X₂} {c : X₂ ⟶ X₃}
    {Y₀ Y₁ Y₂ Y₃ Y₄ : C}
    {d : Y₁ ⟶ Y₄} {e : Y₀ ⟶ Y₁} {f : Y₂ ⟶ Y₀}
    {u : Y₂ ⟶ Y₃} {v : Y₃ ⟶ Y₄}
    {θ : F.obj X₃ ⟶ H.obj Y₁} {s : F.obj X₂ ⟶ H.obj Y₀}
    {Z₀ Z₁ : B} {r : F.obj X₀ ⟶ Z₀} {q : Z₀ ⟶ H.obj Y₂}
    {k : G.obj X₃ ⟶ H.obj Y₄} {ε : Z₀ ⟶ Z₁} {γ : Z₁ ⟶ H.obj Y₃}
    {eF : G.obj X₁ ⟶ Z₁}
    (hg : a ≫ b = t ≫ c) (hh : η.app X₃ ≫ k = θ ≫ H.map d)
    (hn : F.map c ≫ θ = s ≫ H.map e)
    (ho : F.map t ≫ s = r ≫ q ≫ H.map f)
    (huE : f ≫ e ≫ d = u ≫ v)
    (hhg : q ≫ H.map u = ε ≫ γ)
    (huF : F.map a ≫ η.app X₁ ≫ eF = r ≫ ε) :
    F.map a ≫ η.app X₁ ≫ (G.map b ≫ k) =
      F.map a ≫ η.app X₁ ≫ (eF ≫ γ ≫ H.map v) := by
  calc
    _ = F.map (a ≫ b) ≫ (η.app X₃ ≫ k) :=
      scalarNaturalityPasting F G η a b k
    _ = F.map t ≫ F.map c ≫ θ ≫ H.map d := scalarMapTwoSquares F hg hh
    _ = (F.map t ≫ s) ≫ H.map e ≫ H.map d := by
      simpa only [Category.assoc] using congrArg (fun z ↦ F.map t ≫ z ≫ H.map d) hn
    _ = (r ≫ q ≫ H.map f) ≫ H.map e ≫ H.map d :=
      congrArg (fun z ↦ z ≫ H.map e ≫ H.map d) ho
    _ = r ≫ q ≫ H.map u ≫ H.map v := scalarMapThreeComposite H huE r q
    _ = (r ≫ ε) ≫ γ ≫ H.map v := by
      simpa only [Category.assoc] using congrArg (fun z ↦ r ≫ z ≫ H.map v) hhg
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ γ ≫ H.map v) huF.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedComp_unit_left
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d)) :
    (pbcActualDerivedPullCompIso h g d).hom.app K.obj ≫
      (pbcActualDerivedPull h d).map ((pbcActualCompletedPullUnit g d).app K.obj) ≫
        (pbcActualCompletedPullUnit h d).app ((pbcActualCompletedPull g d).obj K.obj) =
      (pbcActualCompletedPullUnit (h ≫ g) d).app K.obj ≫
        (pbcActualCompletedPullCompIso h g d).inv.app K := by
  have he := (pbcActualCompletedPullCompIso_exists h g d).exists.choose_spec K
  change (pbcActualDerivedPullCompIso h g d).hom.app K.obj ≫ _ ≫ _ ≫
    (pbcActualCompletedPullCompIso h g d).hom.app K = _ at he
  exact (Iso.eq_comp_inv ((pbcActualCompletedPullCompIso h g d).app K)).2 (by
    simpa only [Category.assoc, Iso.app_hom] using he)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedComp_unit_right
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d)) :
    (pbcActualDerivedPull h d).map ((pbcActualCompletedPullUnit g d).app K.obj) ≫
      (pbcActualCompletedPullUnit h d).app ((pbcActualCompletedPull g d).obj K.obj) ≫
        (pbcActualCompletedPullCompIso h g d).hom.app K =
      (pbcActualDerivedPullCompIso h g d).inv.app K.obj ≫
        (pbcActualCompletedPullUnit (h ≫ g) d).app K.obj := by
  apply (Iso.eq_inv_comp ((pbcActualDerivedPullCompIso h g d).app K.obj)).2
  have he := (pbcActualCompletedPullCompIso_exists h g d).exists.choose_spec K
  change (pbcActualDerivedPullCompIso h g d).hom.app K.obj ≫ _ ≫ _ ≫
    (pbcActualCompletedPullCompIso h g d).hom.app K = _ at he
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedComp_ext
    {V W Z : Scheme.{u}} (g : W ⟶ V) (h : Z ⟶ W)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete V d))
    (L : PbcCompletedDerived Z d) (hL : PbcIsIntrinsicallyComplete Z d L)
    (a b : (pbcActualCompletedPull h d).obj ((pbcActualCompletedPull g d).obj K.obj) ⟶ L)
    (hab : (pbcActualDerivedPull h d).map ((pbcActualCompletedPullUnit g d).app K.obj) ≫
        (pbcActualCompletedPullUnit h d).app ((pbcActualCompletedPull g d).obj K.obj) ≫ a =
      (pbcActualDerivedPull h d).map ((pbcActualCompletedPullUnit g d).app K.obj) ≫
        (pbcActualCompletedPullUnit h d).app ((pbcActualCompletedPull g d).obj K.obj) ≫ b) :
    a = b := by
  let e := pbcActualCompletedPullCompIso h g d
  have he := (pbcActualCompletedPullCompIso_exists h g d).exists.choose_spec K
  change (pbcActualDerivedPullCompIso h g d).hom.app K.obj ≫ _ ≫ _ ≫
    e.hom.app K = _ at he
  have hu : (pbcActualCompletedPullUnit (h ≫ g) d).app K.obj ≫ e.inv.app K =
      (pbcActualDerivedPullCompIso h g d).hom.app K.obj ≫
        (pbcActualDerivedPull h d).map ((pbcActualCompletedPullUnit g d).app K.obj) ≫
        (pbcActualCompletedPullUnit h d).app ((pbcActualCompletedPull g d).obj K.obj) := by
    exact (Iso.comp_inv_eq (e.app K)).2 (by
      simpa only [Category.assoc, Iso.app_hom] using he.symm)
  apply (cancel_epi (e.inv.app K)).mp
  apply pbcCompletion_hom_ext Z d _ _ hL
  change (pbcActualCompletedPullUnit (h ≫ g) d).app K.obj ≫ (e.inv.app K ≫ a) =
    (pbcActualCompletedPullUnit (h ≫ g) d).app K.obj ≫ (e.inv.app K ≫ b)
  rw [← Category.assoc, ← Category.assoc, hu]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ (pbcActualDerivedPullCompIso h g d).hom.app K.obj ≫ f) hab

private theorem pbcCompletedPullId_unit (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W d)) :
    (pbcActualCompletedPullUnit (𝟙 W) d).app K.obj ≫
        (pbcActualCompletedPullIdIso d W).hom.app K =
      (pbcActualDerivedPullIdIso d W).hom.app K.obj :=
  (pbcActualCompletedPullIdIso_exists d W).exists.choose_spec K

attribute [local irreducible] pbcActualCompletedPullIdIso pbcActualDerivedPullIdIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed identity coherence uses the canonical comparison on complete objects.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-unit-coherence).
Proof: precompose both routes with the ordinary-to-completed pullback unit. The
unit-normalized scalar completion comparison reduces both routes to the ordinary
identity coherence. Both source objects are complete, so the reflector universal
property cancels this unit and gives the displayed equality. -/
theorem pbcScalarCompletedPull_identity (W : Scheme.{u})
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    (pbcScalarCompletedPullIso l E F i (𝟙 W)).hom.app K.obj ≫
        (pbcEmbeddingAmbientTensor l E F i W).map
          ((pbcActualCompletedPullIdIso (pbcIntegralDatum l E) W).hom.app K) =
      (pbcActualCompletedPullIdIso (pbcIntegralDatum l F) W).hom.app
        ⟨(pbcEmbeddingAmbientTensor l E F i W).obj K.obj,
          pbcScalarPreservesComplete l E F i W K⟩ := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let C := pbcEmbeddingAmbientTensor l E F i W
  let LE := pbcActualDerivedPull (𝟙 W) dE
  let LF := pbcActualDerivedPull (𝟙 W) dF
  let ηE := pbcActualCompletionUnit dE W
  let ηF := pbcActualCompletionUnit dF W
  let e := pbcScalarOrdinaryPullIso l E F i (𝟙 W)
  let c := pbcScalarCompletionIso l E F i W
  let idE : (pbcActualCompletion dE W).obj (LE.obj K.obj) ⟶ K.obj :=
    (pbcActualCompletedPullIdIso dE W).hom.app K
  let idF : (pbcActualCompletion dF W).obj (LF.obj (C.obj K.obj)) ⟶ C.obj K.obj :=
    (pbcActualCompletedPullIdIso dF W).hom.app
      ⟨C.obj K.obj, pbcScalarPreservesComplete l E F i W K⟩
  have hc : ηF.app (C.obj (LE.obj K.obj)) ≫ c.hom.app (LE.obj K.obj) =
      C.map (ηE.app (LE.obj K.obj)) := by
    dsimp only [c]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E F i W).exists.choose_spec (LE.obj K.obj)
  have hE : ηE.app (LE.obj K.obj) ≫
      idE =
      (pbcActualDerivedPullIdIso dE W).hom.app K.obj :=
    pbcCompletedPullId_unit W dE K
  have hF : ηF.app (LF.obj (C.obj K.obj)) ≫
      idF =
      (pbcActualDerivedPullIdIso dF W).hom.app (C.obj K.obj) :=
    pbcCompletedPullId_unit W dF
      ⟨C.obj K.obj, pbcScalarPreservesComplete l E F i W K⟩
  have ho : e.hom.app K.obj ≫ C.map
      ((pbcActualDerivedPullIdIso dE W).hom.app K.obj) =
      (pbcActualDerivedPullIdIso dF W).hom.app (C.obj K.obj) :=
    (pbcScalarOperations_identity l E F i W K.obj).2
  apply pbcCompletion_hom_ext W dF _ _ (pbcScalarPreservesComplete l E F i W K)
  rw [pbcScalarCompletedPullIso_hom]
  change ηF.app (LF.obj (C.obj K.obj)) ≫
      (((pbcActualCompletion dF W).map (e.hom.app K.obj) ≫
        c.hom.app (LE.obj K.obj)) ≫ C.map (idE)) =
    ηF.app (LF.obj (C.obj K.obj)) ≫
      idF
  have hn : ηF.app (LF.obj (C.obj K.obj)) ≫
      (pbcActualCompletion dF W).map (e.hom.app K.obj) =
      e.hom.app K.obj ≫ ηF.app (C.obj (LE.obj K.obj)) :=
    (ηF.naturality (e.hom.app K.obj)).symm
  calc
    _ = (ηF.app (LF.obj (C.obj K.obj)) ≫
        (pbcActualCompletion dF W).map (e.hom.app K.obj)) ≫
        c.hom.app (LE.obj K.obj) ≫
        C.map (idE) := by
      simp only [Category.assoc]
    _ = e.hom.app K.obj ≫
        (ηF.app (C.obj (LE.obj K.obj)) ≫ c.hom.app (LE.obj K.obj)) ≫
        C.map (idE) := by
      rw [hn]
      simp only [Category.assoc]
    _ = e.hom.app K.obj ≫ C.map (ηE.app (LE.obj K.obj)) ≫
        C.map (idE) := by rw [hc]
    _ = e.hom.app K.obj ≫ C.map (ηE.app (LE.obj K.obj) ≫
        idE) := by
      rw [CategoryTheory.Functor.map_comp]
    _ = (pbcActualDerivedPullIdIso dF W).hom.app (C.obj K.obj) := by rw [hE, ho]
    _ = _ := hF.symm



end AmbientOperations
end AlgebraicGeometry.Scheme
