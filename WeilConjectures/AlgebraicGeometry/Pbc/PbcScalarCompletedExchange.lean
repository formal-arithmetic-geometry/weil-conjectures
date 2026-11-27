/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence

/-! # Scalar extension and the completed base-change exchange

Finite scalar extension of coefficients is compatible with composition of derived pullbacks,
hence with the ambient base-change exchange (an adjunction mate of the pullback square), and
after completion with the completed base-change exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme

section PullComposition

variable {V W Z : Scheme.{u}} (k : W ⟶ V) (h : Z ⟶ W)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φ : ∀ T : Scheme.{u}, pbcAdicCompletion T dA ⟶ pbcAdicCompletion T dB)
    (sk : pbcActualCoefficientRingMap V (φ V) ≫ pbcActualStructureMap k dB =
      pbcActualStructureMap k dA ≫ (proEtaleSheafDirectImage k RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap W (φ W)))
    (sh : pbcActualCoefficientRingMap W (φ W) ≫ pbcActualStructureMap h dB =
      pbcActualStructureMap h dA ≫ (proEtaleSheafDirectImage h RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap Z (φ Z)))
    (shk : pbcActualCoefficientRingMap V (φ V) ≫ pbcActualStructureMap (h ≫ k) dB =
      pbcActualStructureMap (h ≫ k) dA ≫ (proEtaleSheafDirectImage (h ≫ k) RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap Z (φ Z)))

-- The identity-on-sections restriction/direct-image comparisons paste along composition.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarRightComp :
    pbcActualScalarRightIso (h ≫ k) dA dB (φ V) (φ Z) shk =
      isoWhiskerRight (pbcActualModuleDirectCompIso h k dB).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (pbcActualModulePush h dB)
          (pbcActualScalarRightIso k dA dB (φ V) (φ W) sk) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (pbcActualScalarRightIso h dA dB (φ W) (φ Z) sh)
          (pbcActualModulePush k dA) ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (pbcActualModuleDirectCompIso h k dA) := by
  apply (pbcActualScalarRightIso_exists (h ≫ k) dA dB (φ V) (φ Z) shk).unique
    (pbcActualScalarRightIso_exists (h ≫ k) dA dB (φ V) (φ Z) shk).exists.choose_spec
  intro N U x
  have hδk := (pbcActualScalarRightIso_exists k dA dB (φ V) (φ W) sk).exists.choose_spec
  have hδh := (pbcActualScalarRightIso_exists h dA dB (φ W) (φ Z) sh).exists.choose_spec
  have hez := (pbcActualModuleDirectCompIso_exists h k dB).exists.choose_spec N U.unop
    (((pbcActualModuleDirectCompIso h k dB).inv.app N).val.app U x)
  have hew := (pbcActualModuleDirectCompIso_exists h k dA).exists.choose_spec
    ((SheafOfModules.restrictScalars (pbcActualCoefficientRingMap Z (φ Z))).obj N) U.unop
    (((pbcActualModuleDirectCompIso h k dB).inv.app N).val.app U x)
  have hinv : ((pbcActualModuleDirectCompIso h k dB).hom.app N).val.app U
      (((pbcActualModuleDirectCompIso h k dB).inv.app N).val.app U x) = x :=
    congrArg (fun f ↦ (f.val.app U) x)
      ((pbcActualModuleDirectCompIso h k dB).inv_hom_id_app N)
  have key : ((pbcActualModuleDirectCompIso h k dA).hom.app
      ((SheafOfModules.restrictScalars (pbcActualCoefficientRingMap Z (φ Z))).obj N)).val.app U
      (((pbcActualScalarRightIso h dA dB (φ W) (φ Z) sh).hom.app N).val.app
        (Opposite.op ((proEtaleBaseChange k).obj U.unop))
        (((pbcActualScalarRightIso k dA dB (φ V) (φ W) sk).hom.app
          ((pbcActualModulePush h dB).obj N)).val.app U
          (((pbcActualModuleDirectCompIso h k dB).inv.app N).val.app U x))) = x := by
    erw [hδk, hδh]
    exact hew.trans (hez.symm.trans hinv)
  exact key

-- The ordinary scalar/pullback comparisons paste along composition of pullbacks.
private theorem scalarOrdinaryPullComp (M : pbcModules V (pbcAdicCompletion V dA)) :
    (pbcExtend (φ Z)).map ((pbcActualModulePullCompIso h k dA).hom.app M) ≫
      (pbcActualScalarOrdinaryPullIso h dA dB (φ W) (φ Z) sh).inv.app
        ((pbcActualModulePull k dA).obj M) ≫
      (pbcActualModulePull h dB).map
        ((pbcActualScalarOrdinaryPullIso k dA dB (φ V) (φ W) sk).inv.app M) =
    (pbcActualScalarOrdinaryPullIso (h ≫ k) dA dB (φ V) (φ Z) shk).inv.app M ≫
      (pbcActualModulePullCompIso h k dB).hom.app ((pbcExtend (φ V)).obj M) := by
  have ht := FiniteFreeDirectImage.Conjugation.tower
    (pbcActualModuleAdjunction k dA) (pbcActualModuleAdjunction h dA)
    (pbcActualModuleAdjunction (h ≫ k) dA)
    (pbcActualModuleAdjunction k dB) (pbcActualModuleAdjunction h dB)
    (pbcActualModuleAdjunction (h ≫ k) dB)
    (pbcScalarAdjunction (φ V)) (pbcScalarAdjunction (φ W)) (pbcScalarAdjunction (φ Z))
    (pbcActualModuleDirectCompIso h k dA) (pbcActualModuleDirectCompIso h k dB)
    (pbcActualScalarRightIso k dA dB (φ V) (φ W) sk).symm
    (pbcActualScalarRightIso h dA dB (φ W) (φ Z) sh).symm
    (pbcActualScalarRightIso (h ≫ k) dA dB (φ V) (φ Z) shk).symm (by
      rw [scalarRightComp k h dA dB φ sk sh shk]
      ext N
      simp)
  have hM := congrArg (fun e ↦ e.hom.app M) ht
  have hM' : (pbcActualScalarOrdinaryPullIso (h ≫ k) dA dB (φ V) (φ Z) shk).inv.app M =
      (pbcExtend (φ Z)).map ((pbcActualModulePullCompIso h k dA).hom.app M) ≫
        (pbcActualScalarOrdinaryPullIso h dA dB (φ W) (φ Z) sh).inv.app
          ((pbcActualModulePull k dA).obj M) ≫
        (pbcActualModulePull h dB).map
          ((pbcActualScalarOrdinaryPullIso k dA dB (φ V) (φ W) sk).inv.app M) ≫
        (pbcActualModulePullCompIso h k dB).inv.app ((pbcExtend (φ V)).obj M) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp] at hM
    with_unfolding_all exact hM
  rw [hM']
  simp

-- The same pasting degreewise on actual cochain complexes.
private theorem scalarComplexPullComp
    (P : CochainComplex (pbcModules V (pbcAdicCompletion V dA)) ℤ) :
    ((pbcExtend (φ Z)).mapHomologicalComplex (.up ℤ)).map
        ((pbcActualModulePullCompComplexIso h k dA).hom.app P) ≫
      (pbcActualScalarOrdinaryPullComplexIso h dA dB (φ W) (φ Z) sh).inv.app
        (((pbcActualModulePull k dA).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((pbcActualModulePull h dB).mapHomologicalComplex (.up ℤ)).map
        ((pbcActualScalarOrdinaryPullComplexIso k dA dB (φ V) (φ W) sk).inv.app P) =
    (pbcActualScalarOrdinaryPullComplexIso (h ≫ k) dA dB (φ V) (φ Z) shk).inv.app P ≫
      (pbcActualModulePullCompComplexIso h k dB).hom.app
        (((pbcExtend (φ V)).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro n
  simpa [pbcActualModulePullCompComplexIso, pbcActualScalarOrdinaryPullComplexIso] using
    scalarOrdinaryPullComp k h dA dB φ sk sh shk (P.X n)

-- The derived scalar/pullback comparisons paste along composition of derived pullbacks.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarDerivedPullComp (K : PbcCompletedDerived V dA) :
    (pbcActualDerivedPullCompIso h k dB).hom.app ((pbcDerivedExtend (φ V)).obj K) ≫
      (pbcActualDerivedPull h dB).map
        ((pbcActualScalarDerivedPullIso k dA dB (φ V) (φ W) sk).hom.app K) ≫
      (pbcActualScalarDerivedPullIso h dA dB (φ W) (φ Z) sh).hom.app
        ((pbcActualDerivedPull k dA).obj K) =
    (pbcActualScalarDerivedPullIso (h ≫ k) dA dB (φ V) (φ Z) shk).hom.app K ≫
      (pbcDerivedExtend (φ Z)).map ((pbcActualDerivedPullCompIso h k dA).hom.app K) := by
  let αk := pbcActualScalarDerivedPullIso k dA dB (φ V) (φ W) sk
  let αh := pbcActualScalarDerivedPullIso h dA dB (φ W) (φ Z) sh
  let αc := pbcActualScalarDerivedPullIso (h ≫ k) dA dB (φ V) (φ Z) shk
  let cA := pbcActualDerivedPullCompIso h k dA
  let cB := pbcActualDerivedPullCompIso h k dB
  let LAk := pbcActualDerivedPull k dA
  let LBh := pbcActualDerivedPull h dB
  let EV := pbcDerivedExtend (φ V)
  let EZ := pbcDerivedExtend (φ Z)
  let v : pbcActualDerivedPull (h ≫ k) dA ⋙ EZ ≅ EV ⋙ pbcActualDerivedPull (h ≫ k) dB :=
    isoWhiskerRight cA EZ ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft LAk αh.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight αk.symm LBh ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft EV cB.symm
  have hv : v.symm = αc := by
    apply (pbcActualScalarDerivedPullIso_exists (h ≫ k) dA dB (φ V) (φ Z) shk).unique ?_
      (pbcActualScalarDerivedPullIso_exists (h ≫ k) dA dB (φ V) (φ Z) shk).exists.choose_spec
    intro P hp hf
    have hflat (n : ℤ) : exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory
          (pbcAdicCompletion V dA)) (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X n)) (hf n)
    have hs := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (φ V) P (pbcExtend (φ V)) (pbcExtensionExistence (φ V)).choose_spec.choose
      (pbcExtensionExistence (φ V)).choose_spec.choose_spec.choose hp hflat
    have hsf (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pbcAdicCompletion V dB)
        ((((pbcExtend (φ V)).mapHomologicalComplex (.up ℤ)).obj P).X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ _).symm (hs.2 n)
    have hpk := pull_good k dA P hp hf
    have nk := (pbcActualScalarDerivedPullIso_exists k dA dB (φ V) (φ W) sk).exists.choose_spec
      P hp hf
    have nh := (pbcActualScalarDerivedPullIso_exists h dA dB (φ W) (φ Z) sh).exists.choose_spec
      _ hpk.1 hpk.2
    have ncA := (pbcActualDerivedPullCompIso_exists h k dA).exists.choose_spec P hp hf
    have ncB := (pbcActualDerivedPullCompIso_exists h k dB).exists.choose_spec _ hs.1 hsf
    have hcalc := scalarCompositeCounit
      (complexCounit (pbcExtend (φ V)) (pbcDerivedExtend (φ V)) (pbcExtensionCounit (φ V)))
      (complexCounit (pbcExtend (φ W)) (pbcDerivedExtend (φ W)) (pbcExtensionCounit (φ W)))
      (complexCounit (pbcExtend (φ Z)) (pbcDerivedExtend (φ Z)) (pbcExtensionCounit (φ Z)))
      (complexCounit (pbcActualModulePull k dA) (pbcActualDerivedPull k dA)
        (pbcActualPullCounit k dA))
      (complexCounit (pbcActualModulePull h dA) (pbcActualDerivedPull h dA)
        (pbcActualPullCounit h dA))
      (complexCounit (pbcActualModulePull (h ≫ k) dA) (pbcActualDerivedPull (h ≫ k) dA)
        (pbcActualPullCounit (h ≫ k) dA))
      (complexCounit (pbcActualModulePull k dB) (pbcActualDerivedPull k dB)
        (pbcActualPullCounit k dB))
      (complexCounit (pbcActualModulePull h dB) (pbcActualDerivedPull h dB)
        (pbcActualPullCounit h dB))
      (complexCounit (pbcActualModulePull (h ≫ k) dB) (pbcActualDerivedPull (h ≫ k) dB)
        (pbcActualPullCounit (h ≫ k) dB))
      αk.inv αh.inv cA cB
      (pbcActualModulePullCompComplexIso h k dA) (pbcActualModulePullCompComplexIso h k dB)
      (pbcActualScalarOrdinaryPullComplexIso k dA dB (φ V) (φ W) sk).inv
      (pbcActualScalarOrdinaryPullComplexIso h dA dB (φ W) (φ Z) sh).inv
      (pbcActualScalarOrdinaryPullComplexIso (h ≫ k) dA dB (φ V) (φ Z) shk).inv P
      (by
        have e := scalarInverseNormalization (αk.app (DerivedCategory.Q.obj P)) _
          ((pbcActualDerivedPull k dB).map (pbcComplexCounit (φ V) P) ≫
            pbcActualPullComplexCounit k dB
              (((pbcExtend (φ V)).mapHomologicalComplex (.up ℤ)).obj P))
          (DerivedCategory.Q.mapIso
            ((pbcActualScalarOrdinaryPullComplexIso k dA dB (φ V) (φ W) sk).app P))
          (by
            rw [Category.assoc]
            exact nk)
        simpa only [scalarExtensionComplexCounit_app, scalarPullComplexCounit_app,
          Category.assoc, Functor.mapIso_inv, Iso.app_inv] using e)
      (by
        have e := scalarInverseNormalization
          (αh.app (DerivedCategory.Q.obj (((pbcActualModulePull k dA).mapHomologicalComplex
            (.up ℤ)).obj P))) _
          ((pbcActualDerivedPull h dB).map (pbcComplexCounit (φ W)
              (((pbcActualModulePull k dA).mapHomologicalComplex (.up ℤ)).obj P)) ≫
            pbcActualPullComplexCounit h dB (((pbcExtend (φ W)).mapHomologicalComplex (.up ℤ)).obj
              (((pbcActualModulePull k dA).mapHomologicalComplex (.up ℤ)).obj P)))
          (DerivedCategory.Q.mapIso
            ((pbcActualScalarOrdinaryPullComplexIso h dA dB (φ W) (φ Z) sh).app
              (((pbcActualModulePull k dA).mapHomologicalComplex (.up ℤ)).obj P)))
          (by
            rw [Category.assoc]
            exact nh)
        simpa only [scalarExtensionComplexCounit_app, scalarPullComplexCounit_app,
          Category.assoc, Functor.mapIso_inv, Iso.app_inv] using e)
      (by simpa only [scalarPullComplexCounit_app, cA, pbcActualDerivedPullCompIso] using ncA)
      (by
        have e := scalarInverseNormalization
          (cB.app (DerivedCategory.Q.obj (((pbcExtend (φ V)).mapHomologicalComplex (.up ℤ)).obj P)))
          _ _ (DerivedCategory.Q.mapIso ((pbcActualModulePullCompComplexIso h k dB).app
            (((pbcExtend (φ V)).mapHomologicalComplex (.up ℤ)).obj P))) ncB
        simpa only [scalarExtensionComplexCounit_app, scalarPullComplexCounit_app,
          Category.assoc, Functor.mapIso_inv, Iso.app_inv] using e)
      (scalarComplexPullComp k h dA dB φ sk sh shk P)
    have hinv := scalarInverseNormalization (v.app (DerivedCategory.Q.obj P))
      ((pbcActualDerivedPull (h ≫ k) dB).map (pbcComplexCounit (φ V) P) ≫
        pbcActualPullComplexCounit (h ≫ k) dB
          (((pbcExtend (φ V)).mapHomologicalComplex (.up ℤ)).obj P))
      ((pbcDerivedExtend (φ Z)).map (pbcActualPullComplexCounit (h ≫ k) dA P) ≫
        pbcComplexCounit (φ Z) _)
      (DerivedCategory.Q.mapIso
        ((pbcActualScalarOrdinaryPullComplexIso (h ≫ k) dA dB (φ V) (φ Z) shk).app P)).symm
      (by
        simpa only [v, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
          isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
          Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
          Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv,
          scalarExtensionComplexCounit_app, scalarPullComplexCounit_app, EZ, LAk, LBh, EV]
          using hcalc)
    simpa only [Iso.symm_hom, Iso.app_inv, Iso.symm_inv, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using hinv
  have hK := congrArg (fun e ↦ e.hom.app K ≫ EZ.map (cA.hom.app K)) hv
  simpa [v] using hK

end PullComposition

end AlgebraicGeometry.Scheme

namespace CategoryTheory

/-- A cube of squares of functors commutes: pasting the faces `α₂`, `θ`, `γ⁻¹` agrees with
pasting the faces `β⁻¹`, `θ'`, `α₁`. -/
def MateCubeCommutes {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {L₁ : C₁ ⥤ C₂} {L₂ : C₃ ⥤ C₄} {M₁ : D₁ ⥤ D₂} {M₂ : D₃ ⥤ D₄}
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {G' : D₁ ⥤ D₃} {H' : D₂ ⥤ D₄}
    {S₁ : C₁ ⥤ D₁} {S₂ : C₂ ⥤ D₂} {S₃ : C₃ ⥤ D₃} {S₄ : C₄ ⥤ D₄}
    (θ : G ⋙ L₂ ⟶ L₁ ⋙ H) (θ' : G' ⋙ M₂ ⟶ M₁ ⋙ H')
    (α₁ : S₁ ⋙ M₁ ⟶ L₁ ⋙ S₂) (α₂ : S₃ ⋙ M₂ ⟶ L₂ ⋙ S₄)
    (β : S₁ ⋙ G' ≅ G ⋙ S₃) (γ : S₂ ⋙ H' ≅ H ⋙ S₄) : Prop :=
  whiskerLeft G α₂ ≫ (Functor.associator _ _ _).inv ≫ whiskerRight θ S₄ ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft L₁ γ.inv ≫ (Functor.associator _ _ _).inv =
    (Functor.associator _ _ _).inv ≫ whiskerRight β.inv M₂ ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft S₁ θ' ≫ (Functor.associator _ _ _).inv ≫ whiskerRight α₁ H' ≫
      (Functor.associator _ _ _).hom

/-- A cube of squares of left adjoints whose faces commute gives a commuting cube of the
mates along the two horizontal adjunctions. -/
theorem mateEquiv_cube {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {M₁ : D₁ ⥤ D₂} {N₁ : D₂ ⥤ D₁} {M₂ : D₃ ⥤ D₄} {N₂ : D₄ ⥤ D₃}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : M₁ ⊣ N₁) (b₂ : M₂ ⊣ N₂)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {G' : D₁ ⥤ D₃} {H' : D₂ ⥤ D₄}
    {S₁ : C₁ ⥤ D₁} {S₂ : C₂ ⥤ D₂} {S₃ : C₃ ⥤ D₃} {S₄ : C₄ ⥤ D₄}
    (θ : G ⋙ L₂ ⟶ L₁ ⋙ H) (θ' : G' ⋙ M₂ ⟶ M₁ ⋙ H')
    (α₁ : S₁ ⋙ M₁ ⟶ L₁ ⋙ S₂) (α₂ : S₃ ⋙ M₂ ⟶ L₂ ⋙ S₄)
    (β : S₁ ⋙ G' ≅ G ⋙ S₃) (γ : S₂ ⋙ H' ≅ H ⋙ S₄)
    (hcube : MateCubeCommutes θ θ' α₁ α₂ β γ)
    (μ : R₁ ⋙ G ⟶ H ⋙ R₂) (hμ : μ = mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ θ))
    (ν : R₂ ⋙ S₃ ⟶ S₄ ⋙ N₂) (hν : ν = mateEquiv a₂ b₂ (TwoSquare.mk _ _ _ _ α₂))
    (ρ : R₁ ⋙ S₁ ⟶ S₂ ⋙ N₁) (hρ : ρ = mateEquiv a₁ b₁ (TwoSquare.mk _ _ _ _ α₁))
    (χ : N₁ ⋙ G' ⟶ H' ⋙ N₂) (hχ : χ = mateEquiv b₁ b₂ (TwoSquare.mk _ _ _ _ θ'))
    (K : C₂) :
    S₃.map (μ.app K) ≫ ν.app (H.obj K) ≫ N₂.map (γ.inv.app K) =
      β.inv.app (R₁.obj K) ≫ G'.map (ρ.app K) ≫ χ.app (S₂.obj K) := by
  subst hμ hν hρ hχ
  unfold MateCubeCommutes at hcube
  have hm := AlgebraicGeometry.Scheme.scalarMate_coefficients a₁ a₂ b₂
    (TwoSquare.mk _ _ _ _ θ) (TwoSquare.mk _ _ _ _ α₂)
    (TwoSquare.hComp (TwoSquare.mk _ _ _ _ α₁) (TwoSquare.mk _ _ _ _ θ')) β.symm γ.symm
    (fun T ↦ by simpa [TwoSquare.hComp] using NatTrans.congr_app hcube T) K
  rw [mateEquiv_vcomp a₁ b₁ b₂] at hm
  simpa using hm

end CategoryTheory

namespace AlgebraicGeometry.Scheme

section ScalarExchange

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)

/-- The ordinary scalar/pullback comparison is compatible with the composition comparison of
derived pullbacks. -/
theorem pbcScalarOrdinaryPullIso_comp {V W Z : Scheme.{u}} (k : W ⟶ V) (h : Z ⟶ W)
    (K : PbcCompletedDerived V (pbcIntegralDatum l E)) :
    (pbcActualDerivedPullCompIso h k (pbcIntegralDatum l F)).hom.app
        ((pbcEmbeddingAmbientTensor l E F i V).obj K) ≫
      (pbcActualDerivedPull h (pbcIntegralDatum l F)).map
        ((pbcScalarOrdinaryPullIso l E F i k).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E F i h).hom.app
        ((pbcActualDerivedPull k (pbcIntegralDatum l E)).obj K) =
    (pbcScalarOrdinaryPullIso l E F i (h ≫ k)).hom.app K ≫
      (pbcEmbeddingAmbientTensor l E F i Z).map
        ((pbcActualDerivedPullCompIso h k (pbcIntegralDatum l E)).hom.app K) := by
  simpa only [pbcScalarOrdinaryPullIso, pbcEmbeddingAmbientTensor] using
    scalarDerivedPullComp k h (pbcIntegralDatum l E) (pbcIntegralDatum l F)
      (pbcScalarCoefficientMap l E F i) (pbcScalarCoefficientStructureSquare l E F i k)
      (pbcScalarCoefficientStructureSquare l E F i h)
      (pbcScalarCoefficientStructureSquare l E F i (h ≫ k)) K

-- Transport of the scalar/pullback comparison along an equality of morphisms.
private theorem scalarOrdinaryPull_eqToHom {S T : Scheme.{u}} {m₁ m₂ : S ⟶ T}
    (e : m₁ = m₂) :
    (pbcScalarOrdinaryPullIso l E F i m₁).hom ≫
        whiskerRight
          (eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a (pbcIntegralDatum l E)) e)).hom
          (pbcEmbeddingAmbientTensor l E F i S) =
      whiskerLeft (pbcEmbeddingAmbientTensor l E F i T)
          (eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a (pbcIntegralDatum l F)) e)).hom ≫
        (pbcScalarOrdinaryPullIso l E F i m₂).hom := by
  subst e
  ext K
  simp

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

omit [Fact l.Prime] in
-- The pullback square through its composition comparisons and the identification of the
-- two composite pullbacks.
private theorem pullSquare_hom {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (pbcActualCompletedPullSquareIso d sq).hom =
      (pbcActualDerivedPullCompIso f' g d).inv ≫
        (eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a d) sq.w.symm)).hom ≫
        (pbcActualDerivedPullCompIso g' f d).hom := rfl

-- The scalar direct-image comparison is the mate of the scalar/pullback comparison.
private theorem scalarDirectImageIso_hom_eq {S T : Scheme.{u}} (a : S ⟶ T) :
    (pbcScalarDirectImageIso l E F i a).hom =
      mateEquiv (pbcActualDerivedAdjunction a (pbcIntegralDatum l E))
        (pbcActualDerivedAdjunction a (pbcIntegralDatum l F))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i a).hom) := by
  rw [pbcScalarDirectImageIso_hom]
  unfold pbcScalarDirectImageMap pbcScalarOrdinaryPullIso
  rfl

omit [Fact l.Prime] in
-- The ambient exchange is the mate of the pullback square.
private theorem ambientExchange_eq {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    pbcActualCompletedAmbientExchange d sq =
      mateEquiv (pbcActualDerivedAdjunction f d) (pbcActualDerivedAdjunction f' d)
        (TwoSquare.mk _ _ _ _ (pbcActualCompletedPullSquareIso d sq).hom) := rfl

/-- The scalar/pullback comparisons form a commutative cube with the pullback squares
at both coefficient levels. -/
theorem pbcScalarOrdinaryPullIso_pullSquare :
    MateCubeCommutes (pbcActualCompletedPullSquareIso (pbcIntegralDatum l E) sq).hom
      (pbcActualCompletedPullSquareIso (pbcIntegralDatum l F) sq).hom
      (pbcScalarOrdinaryPullIso l E F i f).hom (pbcScalarOrdinaryPullIso l E F i f').hom
      (pbcScalarOrdinaryPullIso l E F i g) (pbcScalarOrdinaryPullIso l E F i g') := by
  unfold MateCubeCommutes
  have t := scalarOrdinaryPull_eqToHom l E F i sq.w.symm
  rw [pullSquare_hom, pullSquare_hom]
  generalize (eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a (pbcIntegralDatum l E))
    sq.w.symm)).hom = eE at t ⊢
  generalize (eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a (pbcIntegralDatum l F))
    sq.w.symm)).hom = eF at t ⊢
  have t2 : whiskerLeft (pbcEmbeddingAmbientTensor l E F i Y) eF =
      (pbcScalarOrdinaryPullIso l E F i (f' ≫ g)).hom ≫
        whiskerRight eE (pbcEmbeddingAmbientTensor l E F i X') ≫
        (pbcScalarOrdinaryPullIso l E F i (g' ≫ f)).inv := by
    rw [← Category.assoc, t, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [whiskerLeft_comp, whiskerLeft_comp, t2]
  ext K
  have c1 := pbcScalarOrdinaryPullIso_comp l E F i g f' K
  have c2 := pbcScalarOrdinaryPullIso_comp l E F i f g' K
  simp only [NatTrans.comp_app]
  rw [whiskerLeft_app, whiskerLeft_app, whiskerLeft_app, whiskerLeft_app, whiskerRight_app,
    whiskerRight_app, whiskerRight_app, whiskerRight_app]
  have c2' : (pbcEmbeddingAmbientTensor l E F i X').map
        ((pbcActualDerivedPullCompIso g' f (pbcIntegralDatum l E)).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E F i g').inv.app
        ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) =
      (pbcScalarOrdinaryPullIso l E F i (g' ≫ f)).inv.app K ≫
        (pbcActualDerivedPullCompIso g' f (pbcIntegralDatum l F)).hom.app
          ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
        (pbcActualDerivedPull g' (pbcIntegralDatum l F)).map
          ((pbcScalarOrdinaryPullIso l E F i f).hom.app K) := by
    rw [← cancel_epi ((pbcScalarOrdinaryPullIso l E F i (g' ≫ f)).hom.app K),
      Iso.hom_inv_id_app_assoc, ← Category.assoc, ← c2]
    simp
  simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((pbcActualDerivedPullCompIso f' g (pbcIntegralDatum l F)).hom.app
      ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
    (pbcActualDerivedPull f' (pbcIntegralDatum l F)).map
      ((pbcScalarOrdinaryPullIso l E F i g).hom.app K))]
  simp only [Category.assoc]
  rw [reassoc_of% c1, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, c2']
  simp

-- The ambient exchange square with the four mates as variables.
private theorem scalarAmbientExchange_aux
    (μ : pbcActualDerivedPush f (pbcIntegralDatum l E) ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l E) ⟶
      pbcActualDerivedPull g' (pbcIntegralDatum l E) ⋙
        pbcActualDerivedPush f' (pbcIntegralDatum l E))
    (hμ : μ = mateEquiv (pbcActualDerivedAdjunction f (pbcIntegralDatum l E))
      (pbcActualDerivedAdjunction f' (pbcIntegralDatum l E))
      (TwoSquare.mk _ _ _ _ (pbcActualCompletedPullSquareIso (pbcIntegralDatum l E) sq).hom))
    (ν : pbcActualDerivedPush f' (pbcIntegralDatum l E) ⋙ pbcEmbeddingAmbientTensor l E F i Y' ⟶
      pbcEmbeddingAmbientTensor l E F i X' ⋙ pbcActualDerivedPush f' (pbcIntegralDatum l F))
    (hν : ν = mateEquiv (pbcActualDerivedAdjunction f' (pbcIntegralDatum l E))
      (pbcActualDerivedAdjunction f' (pbcIntegralDatum l F))
      (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i f').hom))
    (ρ : pbcActualDerivedPush f (pbcIntegralDatum l E) ⋙ pbcEmbeddingAmbientTensor l E F i Y ⟶
      pbcEmbeddingAmbientTensor l E F i X ⋙ pbcActualDerivedPush f (pbcIntegralDatum l F))
    (hρ : ρ = mateEquiv (pbcActualDerivedAdjunction f (pbcIntegralDatum l E))
      (pbcActualDerivedAdjunction f (pbcIntegralDatum l F))
      (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i f).hom))
    (χ : pbcActualDerivedPush f (pbcIntegralDatum l F) ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l F) ⟶
      pbcActualDerivedPull g' (pbcIntegralDatum l F) ⋙
        pbcActualDerivedPush f' (pbcIntegralDatum l F))
    (hχ : χ = mateEquiv (pbcActualDerivedAdjunction f (pbcIntegralDatum l F))
      (pbcActualDerivedAdjunction f' (pbcIntegralDatum l F))
      (TwoSquare.mk _ _ _ _ (pbcActualCompletedPullSquareIso (pbcIntegralDatum l F) sq).hom))
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i Y').map (μ.app K) ≫
      ν.app ((pbcActualDerivedPull g' (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPush f' (pbcIntegralDatum l F)).map
        ((pbcScalarOrdinaryPullIso l E F i g').inv.app K) =
    (pbcScalarOrdinaryPullIso l E F i g).inv.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPull g (pbcIntegralDatum l F)).map (ρ.app K) ≫
      χ.app ((pbcEmbeddingAmbientTensor l E F i X).obj K) :=
  mateEquiv_cube
    (pbcActualDerivedAdjunction f (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction f' (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction f (pbcIntegralDatum l F))
    (pbcActualDerivedAdjunction f' (pbcIntegralDatum l F))
    (pbcActualCompletedPullSquareIso (pbcIntegralDatum l E) sq).hom
    (pbcActualCompletedPullSquareIso (pbcIntegralDatum l F) sq).hom
    (pbcScalarOrdinaryPullIso l E F i f).hom (pbcScalarOrdinaryPullIso l E F i f').hom
    (pbcScalarOrdinaryPullIso l E F i g) (pbcScalarOrdinaryPullIso l E F i g')
    (pbcScalarOrdinaryPullIso_pullSquare l E F i sq) μ hμ ν hν ρ hρ χ hχ K

/-- Scalar extension carries the ambient exchange at the source coefficients to the ambient
exchange at the target coefficients, through the scalar direct-image and pullback
comparisons. -/
theorem pbcScalarAmbientExchange (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i Y').map
        ((pbcActualCompletedAmbientExchange (pbcIntegralDatum l E) sq).app K) ≫
      (pbcScalarDirectImageIso l E F i f').hom.app
        ((pbcActualDerivedPull g' (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPush f' (pbcIntegralDatum l F)).map
        ((pbcScalarOrdinaryPullIso l E F i g').inv.app K) =
    (pbcScalarOrdinaryPullIso l E F i g).inv.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPull g (pbcIntegralDatum l F)).map
        ((pbcScalarDirectImageIso l E F i f).hom.app K) ≫
      (pbcActualCompletedAmbientExchange (pbcIntegralDatum l F) sq).app
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) :=
  scalarAmbientExchange_aux l E F i sq _ (ambientExchange_eq sq _) _
    (scalarDirectImageIso_hom_eq l E F i f') _ (scalarDirectImageIso_hom_eq l E F i f) _
    (ambientExchange_eq sq _) K

/-- The completion unit followed by the completed exchange is the ambient exchange followed
by the direct image of the completion unit. -/
theorem pbcActualCompletedExchange_unit {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : PbcCompletedDerived X d) :
    (pbcActualCompletionUnit d Y').app
        ((pbcActualDerivedPull g d).obj ((pbcActualDerivedPush f d).obj K)) ≫
      (pbcActualCompletedExchange d sq).app K =
    (pbcActualCompletedAmbientExchange d sq).app K ≫
      (pbcActualDerivedPush f' d).map
        ((pbcActualCompletionUnit d X').app ((pbcActualDerivedPull g' d).obj K)) := by
  have hn := (pbcActualCompletionUnit d Y').naturality
    ((pbcActualCompletedAmbientExchange d sq).app K)
  have hd : (pbcActualCompletionUnit d Y').app
        ((pbcActualDerivedPush f' d).obj ((pbcActualDerivedPull g' d).obj K)) ≫
        (pbcActualDirectCompletionIso f' d).hom.app ((pbcActualDerivedPull g' d).obj K) =
      (pbcActualDerivedPush f' d).map
        ((pbcActualCompletionUnit d X').app ((pbcActualDerivedPull g' d).obj K)) :=
    (pbcActualDirectCompletionIso_exists f' d).exists.choose_spec _
  have happ : (pbcActualCompletedExchange d sq).app K =
      (pbcActualCompletion d Y').map ((pbcActualCompletedAmbientExchange d sq).app K) ≫
        (pbcActualDirectCompletionIso f' d).hom.app ((pbcActualDerivedPull g' d).obj K) := by
    dsimp only [pbcActualCompletedExchange, pbcActualCompletedPull]
    simp
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [happ]
  exact ((reassoc_of% hn) _).symm.trans (congrArg (_ ≫ ·) hd)

-- The completion unit followed by the inverse completed scalar/pullback comparison.
private theorem scalarCompletedPull_unit {S T : Scheme.{u}} (a : S ⟶ T)
    (M : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i S).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l E) S).app
          ((pbcActualDerivedPull a (pbcIntegralDatum l E)).obj M)) ≫
      (pbcScalarCompletedPullIso l E F i a).inv.app M =
    (pbcScalarOrdinaryPullIso l E F i a).inv.app M ≫
      (pbcActualCompletionUnit (pbcIntegralDatum l F) S).app
        ((pbcActualDerivedPull a (pbcIntegralDatum l F)).obj
          ((pbcEmbeddingAmbientTensor l E F i T).obj M)) := by
  have hk : (pbcActualCompletionUnit (pbcIntegralDatum l F) S).app
        ((pbcEmbeddingAmbientTensor l E F i S).obj
          ((pbcActualDerivedPull a (pbcIntegralDatum l E)).obj M)) ≫
      (pbcScalarCompletionIso l E F i S).hom.app
        ((pbcActualDerivedPull a (pbcIntegralDatum l E)).obj M) =
      (pbcEmbeddingAmbientTensor l E F i S).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l E) S).app
          ((pbcActualDerivedPull a (pbcIntegralDatum l E)).obj M)) := by
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E F i S).exists.choose_spec _
  have hn := (pbcActualCompletionUnit (pbcIntegralDatum l F) S).naturality
    ((pbcScalarOrdinaryPullIso l E F i a).hom.app M)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  have key : ((pbcScalarOrdinaryPullIso l E F i a).inv.app M ≫
      (pbcActualCompletionUnit (pbcIntegralDatum l F) S).app
        ((pbcActualDerivedPull a (pbcIntegralDatum l F)).obj
          ((pbcEmbeddingAmbientTensor l E F i T).obj M))) ≫
      (pbcScalarCompletedPullIso l E F i a).hom.app M =
      (pbcEmbeddingAmbientTensor l E F i S).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l E) S).app
          ((pbcActualDerivedPull a (pbcIntegralDatum l E)).obj M)) := by
    rw [pbcScalarCompletedPullIso_hom]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((reassoc_of% hn) _).symm).trans
      ((Iso.inv_hom_id_app_assoc _ _ _).trans hk))
  exact (Iso.comp_inv_eq ((pbcScalarCompletedPullIso l E F i a).app M)).mpr key.symm

-- Maps out of a scalar-extended completion into a complete object are determined by the
-- scalar extension of the completion unit.
private theorem scalarCompletion_hom_ext (T : Scheme.{u})
    (N : PbcCompletedDerived T (pbcIntegralDatum l E))
    (L : PbcCompletedDerived T (pbcIntegralDatum l F))
    (hL : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l F) L)
    (a b : (pbcEmbeddingAmbientTensor l E F i T).obj
      ((pbcActualCompletion (pbcIntegralDatum l E) T).obj N) ⟶ L)
    (hab : (pbcEmbeddingAmbientTensor l E F i T).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l E) T).app N) ≫ a =
      (pbcEmbeddingAmbientTensor l E F i T).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l E) T).app N) ≫ b) : a = b := by
  have hk := (pbcScalarCompletionIso_exists l E F i T).exists.choose_spec N
  rw [← cancel_epi ((pbcScalarCompletionIso_exists l E F i T).exists.choose.hom.app N)]
  apply pbcCompletion_hom_ext T (pbcIntegralDatum l F) _ _ hL
  rw [← Category.assoc, hk, ← Category.assoc, hk, hab]

/-- Scalar extension along `i` carries the completed exchange at `E` to the completed exchange
at `F`, through the scalar direct-image and completed-pullback comparisons. -/
theorem pbcActualCompletedExchange_scalarExtension
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
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
  have := pbcComplete_iso Y' (pbcIntegralDatum l F)
  have hT : PbcIsIntrinsicallyComplete Y' (pbcIntegralDatum l F)
      ((pbcActualDerivedPush f' (pbcIntegralDatum l F)).obj
        ((pbcActualCompletedPull g' (pbcIntegralDatum l F)).obj
          ((pbcEmbeddingAmbientTensor l E F i X).obj K))) :=
    ObjectProperty.prop_of_iso _ ((pbcActualDirectCompletionIso f' (pbcIntegralDatum l F)).app
      ((pbcActualDerivedPull g' (pbcIntegralDatum l F)).obj
        ((pbcEmbeddingAmbientTensor l E F i X).obj K)))
      ((ObjectProperty.ι (PbcIsIntrinsicallyComplete Y' (pbcIntegralDatum l F))).leftAdjoint.obj
        _).property
  apply scalarCompletion_hom_ext l E F i Y' _ _ hT
  have hE := pbcActualCompletedExchange_unit sq (pbcIntegralDatum l E) K
  have hF := pbcActualCompletedExchange_unit sq (pbcIntegralDatum l F)
    ((pbcEmbeddingAmbientTensor l E F i X).obj K)
  have hσ := (pbcScalarDirectImageIso l E F i f').hom.naturality
    ((pbcActualCompletionUnit (pbcIntegralDatum l E) X').app
      ((pbcActualDerivedPull g' (pbcIntegralDatum l E)).obj K))
  have hn := (pbcActualCompletionUnit (pbcIntegralDatum l F) Y').naturality
    ((pbcActualDerivedPull g (pbcIntegralDatum l F)).map
      ((pbcScalarDirectImageIso l E F i f).hom.app K))
  have hA := pbcScalarAmbientExchange l E F i sq K
  have hu₁ := scalarCompletedPull_unit l E F i g' K
  have hu₂ := scalarCompletedPull_unit l E F i g
    ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hσ hn
  refine (Functor.map_comp_assoc _ _ _ _).symm.trans ?_
  refine (congrArg (fun y ↦ (pbcEmbeddingAmbientTensor l E F i Y').map y ≫ _) hE).trans ?_
  refine (Functor.map_comp_assoc _ _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((reassoc_of% hσ) _)).trans ?_
  refine (congrArg (fun y ↦ _ ≫ _ ≫ y) (Functor.map_comp _ _ _).symm).trans ?_
  refine (congrArg (fun y ↦ _ ≫ _ ≫ (pbcActualDerivedPush f' (pbcIntegralDatum l F)).map y)
    hu₁).trans ?_
  refine (congrArg (fun y ↦ _ ≫ _ ≫ y) (Functor.map_comp _ _ _)).trans ?_
  refine ((reassoc_of% hA) _).trans ?_
  refine (congrArg (fun y ↦ _ ≫ _ ≫ y) hF.symm).trans ?_
  refine (congrArg (_ ≫ ·) ((reassoc_of% hn) _)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((eq_whisker hu₂ _).symm.trans (Category.assoc _ _ _))

end ScalarExchange

end AlgebraicGeometry.Scheme
