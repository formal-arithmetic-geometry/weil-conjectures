/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneLocalData
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.AlgebraicGeometry.Sites.GmTransport
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-! # The normalized finite-coefficient Kummer generator -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  HomologicalComplex.homologyFunctor Scheme.kummerSequence


private noncomputable def restrictionRepresentingUnit
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenComparison.integerSheaf U ⟶ (Scheme.etaleRestriction j).obj
      ((EtaleOpenComparison.freeSheaf X).obj (Scheme.Etale.mk j)) :=
  (EtaleOpenComparison.restrictedSectionsEquiv j _).symm
    (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) _ (𝟙 _))

private theorem restrictionRepresentingUnit_comp
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (EtaleOpenComparison.freeSheaf X).obj (Scheme.Etale.mk j) ⟶ G) :
    restrictionRepresentingUnit j ≫ (Scheme.etaleRestriction j).map f =
      (EtaleOpenComparison.restrictedSectionsEquiv j G).symm
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G f) := by
  apply (EtaleOpenComparison.restrictedSectionsEquiv j G).injective
  erw [EtaleOpenComparison.restrictedSectionsEquiv_naturality]
  dsimp only [restrictionRepresentingUnit]
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simpa only [Category.id_comp] using
    (EtaleOpenComparison.sectionsEquiv_naturality X.smallEtaleTopology
      (Scheme.Etale.mk j) f (𝟙 _)).symm

private theorem restrictionExt_bijective
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective ((Scheme.etaleRestriction j).mapExtPrecomp
      (restrictionRepresentingUnit j) G q) := by
  let R := Scheme.etaleRestriction j
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j)
  apply R.mapExtPrecomp_bijective
  · intro I hI
    have := hI
    infer_instance
  · intro B
    let e := (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
      (Scheme.Etale.mk j) B).trans (EtaleOpenComparison.restrictedSectionsEquiv j B).symm
    have he : (fun f ↦ restrictionRepresentingUnit j ≫ R.map f) = e := by
      funext f
      exact restrictionRepresentingUnit_comp j B f
    rw [he]
    exact e.bijective

private theorem restrictionExt_boundary
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (f : (EtaleOpenComparison.freeSheaf X).obj (Scheme.Etale.mk j) ⟶ S.X₃) :
    (Scheme.etaleRestriction j).mapExtPrecomp (restrictionRepresentingUnit j) S.X₁ 1
        ((Abelian.Ext.mk₀ f).comp hS.extClass (zero_add 1)) =
      (Abelian.Ext.mk₀ ((EtaleOpenComparison.restrictedSectionsEquiv j S.X₃).symm
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) S.X₃ f))).comp
          (hS.map_of_exact (Scheme.etaleRestriction j)).extClass (zero_add 1) := by
  rw [Functor.mapExtPrecomp_comp_extClass, Functor.mapExtPrecomp_mk₀,
    restrictionRepresentingUnit_comp]

private theorem restrictedSectionsEquiv_unit
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (v : Γ(U, ⊤)ˣ) :
    (EtaleOpenComparison.restrictedSectionsEquiv j X.gmSheaf).symm
        (ULift.up (Additive.ofMul v)) =
      (U.constantSheafULiftIntIso).hom ≫ Scheme.unitToGmSheaf v := by
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale U
  have h := (Scheme.equiv₀_mk₀_unitToGmSheaf U hT v).trans
    (Scheme.gmSheaf_map_gmSection U v)
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homAddEquiv _ _
      (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ _))) = _ at h
  erw [← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply] at h
  apply (EtaleOpenComparison.restrictedSectionsEquiv j X.gmSheaf).injective
  rw [AddEquiv.apply_symm_apply]
  dsimp only [EtaleOpenComparison.restrictedSectionsEquiv, AddEquiv.trans_apply]
  erw [h]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change (v : Γ(U, ⊤)) = (𝟙 U : U ⟶ U).appTop (v : Γ(U, ⊤))
  rfl

private theorem restrictionExt_kummer
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (m : ℕ)
    (hmX : IsUnit (m : Γ(X, ⊤))) (hmU : IsUnit (m : Γ(U, ⊤))) (v : Γ(U, ⊤)ˣ) :
    ((Scheme.etaleRestriction j).mapExtPrecomp (restrictionRepresentingUnit j)
        (X.rootsOfUnitySheaf m) 1
        ((Abelian.Ext.mk₀ ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
          (Scheme.Etale.mk j) X.gmSheaf).symm (ULift.up (Additive.ofMul v)))).comp
            (X.kummerSequence_shortExact m hmX).extClass (zero_add 1))).comp
        (Abelian.Ext.mk₀ (Scheme.rootsOfUnityRestrictionIso j m).hom) (add_zero 1) =
      U.kummerδ₀ m hmU (Additive.ofMul v) := by
  have hb := restrictionExt_boundary j (X.kummerSequence_shortExact m hmX)
    ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
      (Scheme.Etale.mk j) X.gmSheaf).symm (ULift.up (Additive.ofMul v)))
  have hs := restrictedSectionsEquiv_unit j v
  have hsec := (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
    (Scheme.Etale.mk j) X.gmSheaf).apply_symm_apply (ULift.up (Additive.ofMul v))
  have hbc := congrArg (fun z ↦
    (Abelian.Ext.mk₀ ((EtaleOpenComparison.restrictedSectionsEquiv j X.gmSheaf).symm z)).comp
      ((X.kummerSequence_shortExact m hmX).map_of_exact
        (Scheme.etaleRestriction j)).extClass (zero_add 1)) hsec
  have hb' := hb.trans hbc
  have hbc' := congrArg (fun z ↦
    z.comp (Abelian.Ext.mk₀ (Scheme.rootsOfUnityRestrictionIso j m).hom)
      (add_zero 1)) hb'
  refine hbc'.trans ?_
  have hss := congrArg (fun z ↦ (Abelian.Ext.mk₀ z).comp
    ((X.kummerSequence_shortExact m hmX).map_of_exact
      (Scheme.etaleRestriction j)).extClass (zero_add 1)) hs
  have hss' := congrArg (fun z ↦
    z.comp (Abelian.Ext.mk₀ (Scheme.rootsOfUnityRestrictionIso j m).hom)
      (add_zero 1)) hss
  refine hss'.trans ?_
  have hδ := Scheme.kummerδ₀_eq_comp_extClass U m hmU v
  refine Eq.trans ?_ hδ.symm
  let θ := Abelian.Ext.mk₀ ((U.constantSheafULiftIntIso).hom ≫ Scheme.unitToGmSheaf v)
  let hS := (X.kummerSequence_shortExact m hmX).map_of_exact (Scheme.etaleRestriction j)
  have hn := hS.extClass_naturality
    (U.kummerSequence_shortExact m hmU) (Scheme.kummerSequenceRestriction j m)
  have he : hS.extClass.comp
      (Abelian.Ext.mk₀ (Scheme.rootsOfUnityRestrictionIso j m).hom) (add_zero 1) =
        (U.kummerSequence_shortExact m hmU).extClass :=
    hn.trans (Abelian.Ext.mk₀_id_comp _)
  calc
    _ = θ.comp (hS.extClass.comp
      (Abelian.Ext.mk₀ (Scheme.rootsOfUnityRestrictionIso j m).hom) (add_zero 1))
        (zero_add 1) := Abelian.Ext.comp_assoc θ _ _ (zero_add 1) (add_zero 1) (by omega)
    _ = _ := congrArg (fun z ↦ θ.comp z (zero_add 1)) he

private theorem fullAbConstant (X : Scheme.{u}) [ConnectedSpace X] :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).Full := by
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    exact Scheme.bijective_toSheafify_app_terminal X M
  exact adj.fullyFaithfulLOfIsIsoUnit.full

private theorem restrictionHom_surjective
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [ConnectedSpace U]
    {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {M N : AddCommGrpCat.{u + 1}}
    (eG : G ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
    (eH : H ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N) :
    Function.Surjective ((Scheme.etaleRestriction j).map (X := G) (Y := H)) := by
  let R := Scheme.etaleRestriction j
  let CX := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let CU := constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}
  have := fullAbConstant U
  let η : CX ⋙ R ≅ CU :=
    Functor.isoWhiskerLeft CX
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
        inferInstance).symm ≪≫ Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} j
  have : (CX ⋙ R).Full := Functor.Full.of_iso η.symm
  intro f
  let φ : M ⟶ N := (CX ⋙ R).preimage (R.map eG.inv ≫ f ≫ R.map eH.hom)
  have hφ : R.map (CX.map φ) = R.map eG.inv ≫ f ≫ R.map eH.hom :=
    (CX ⋙ R).map_preimage _
  let hG := R.mapIso eG
  let hH := R.mapIso eH
  have hφ' : R.map (CX.map φ) = hG.inv ≫ f ≫ hH.hom := by
    dsimp only [hG, hH, Functor.mapIso_inv, Functor.mapIso_hom]
    exact hφ
  refine ⟨eG.hom ≫ CX.map φ ≫ eH.inv, ?_⟩
  calc
    _ = hG.hom ≫ (R.map (CX.map φ)) ≫ hH.inv := by
      dsimp only [hG, hH, Functor.mapIso_hom, Functor.mapIso_inv]
      exact R.map_comp eG.hom (CX.map φ ≫ eH.inv) |>.trans
        (congrArg (fun z ↦ R.map eG.hom ≫ z) (R.map_comp (CX.map φ) eH.inv))
    _ = hG.hom ≫ (hG.inv ≫ f ≫ hH.hom) ≫ hH.inv :=
      congrArg (fun z ↦ hG.hom ≫ z ≫ hH.inv) hφ'
    _ = f := by simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]

private theorem homologyMap_smul_id
    {A : Type (u + 1)} [CommRing A]
    (K : CochainComplex (ModuleCat.{u + 1} A) ℕ) (q : ℕ) (a : A) :
    HomologicalComplex.homologyMap (a • 𝟙 K) q = a • 𝟙 (K.homology q) := by
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor _ _ q).map (a • 𝟙 K) =
    a • 𝟙 (K.sc q) from rfl]
  simp only [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

private theorem derivedSections_smul_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) (a : A) :
    ((sections X.smallEtaleTopology A W).rightDerived q).map (a • 𝟙 F) =
      a • 𝟙 _ := by
  let E := sections X.smallEtaleTopology A W
  let I := injectiveResolution F
  let φ : I.cocomplex ⟶ I.cocomplex := a • 𝟙 _
  have hφ : I.ι.f 0 ≫ φ.f 0 = (a • 𝟙 F) ≫ I.ι.f 0 := by
    simp only [φ, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
      Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  have hw : I.ι ≫ φ = (CochainComplex.single₀ _).map (a • 𝟙 F) ≫ I.ι := by
    apply HomologicalComplex.from_single_hom_ext
    simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] using hφ
  rw [Functor.rightDerived_map_eq E q (a • 𝟙 F) φ hw]
  have hmap : (E.mapHomologicalComplex (.up ℕ)).map φ =
      a • 𝟙 ((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) := rfl
  simp only [Functor.comp_map]
  rw [hmap]
  change (I.isoRightDerivedObj E q).hom ≫
    HomologicalComplex.homologyMap
      (a • 𝟙 ((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)) q ≫
        (I.isoRightDerivedObj E q).inv = _
  rw [homologyMap_smul_id]
  have hid : (I.isoRightDerivedObj E q).hom ≫
      𝟙 (((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q) ≫
        (I.isoRightDerivedObj E q).inv = 𝟙 _ := by
    calc
      _ = (I.isoRightDerivedObj E q).hom ≫ (I.isoRightDerivedObj E q).inv :=
        congrArg (fun z ↦ (I.isoRightDerivedObj E q).hom ≫ z) (Category.id_comp _)
      _ = _ := (I.isoRightDerivedObj E q).hom_inv_id
  simpa only [Linear.comp_smul, Linear.smul_comp] using congrArg (fun z ↦ a • z) hid

private theorem kummerClass_evaluation
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v : Γ(W.left, ⊤)ˣ) :
    (evaluationExt X W 1).hom.app ((Etale.moduleAbelianForget A X).obj F)
      (((Etale.moduleEvaluationForgetComparison A X W 1).app F)
        (kummerClass A X W F m hm f v)) =
      ((Abelian.Ext.mk₀
        ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf).symm
          (ULift.up (Additive.ofMul v)))).comp
            (X.kummerSequence_shortExact m hm).extClass (zero_add 1)).comp
              (Abelian.Ext.mk₀ f) (add_zero 1) := by
  have := (Etale.module_cohomology_conventions A X).2.1 F W 1
  let c := asIso ((Etale.moduleEvaluationForgetComparison A X W 1).app F)
  let d := (evaluationExt X W 1).app ((Etale.moduleAbelianForget A X).obj F)
  change d.hom (c.hom (c.inv (d.inv _))) = _
  rw [c.inv_hom_id_apply, d.inv_hom_id_apply]

private theorem kummerClass_comp
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (g : F ⟶ G) (v : Γ(W.left, ⊤)ˣ) :
    kummerClass A X W G m hm (f ≫ (Etale.moduleAbelianForget A X).map g) v =
      ((sections X.smallEtaleTopology A W).rightDerived 1).map g
        (kummerClass A X W F m hm f v) := by
  have : IsIso (Etale.moduleEvaluationForgetComparison A X W 1) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact (Etale.module_cohomology_conventions A X).2.1 M W 1
  let e := asIso (Etale.moduleEvaluationForgetComparison A X W 1) ≪≫
    Functor.isoWhiskerLeft (Etale.moduleAbelianForget A X) (evaluationExt X W 1)
  apply (e.app G).addCommGroupIsoToAddEquiv.injective
  have h := ConcreteCategory.congr_hom (e.hom.naturality g)
    (kummerClass A X W F m hm f v)
  have hF := kummerClass_evaluation A X W F m hm f v
  have hG := kummerClass_evaluation A X W G m hm
    (f ≫ (Etale.moduleAbelianForget A X).map g) v
  change e.hom.app G (kummerClass A X W G m hm
    (f ≫ (Etale.moduleAbelianForget A X).map g) v) =
      e.hom.app G (((sections X.smallEtaleTopology A W).rightDerived 1).map g
        (kummerClass A X W F m hm f v))
  refine hG.trans ?_
  refine Eq.trans ?_ h.symm
  change _ = (e.hom.app F (kummerClass A X W F m hm f v)).comp
    (Abelian.Ext.mk₀ ((Etale.moduleAbelianForget A X).map g)) (add_zero 1)
  change _ = ((evaluationExt X W 1).hom.app ((Etale.moduleAbelianForget A X).obj F)
    (((Etale.moduleEvaluationForgetComparison A X W 1).app F)
      (kummerClass A X W F m hm f v))).comp _ _
  rw [hF, ← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero]


open AlgebraicGeometry.Scheme

private noncomputable def zmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite twist line is the existing abelian-sheaf scalar extension. -/
private noncomputable def finiteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (finiteEtaleMuModulePresheaf T N)
      (zmodScalarExtensionIso N A hA))


private noncomputable def finiteLineConstantIso
    (A : Type (u + 1)) [CommRing A] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {T : Scheme.{u}} (p : T ⟶ Spec (.of Ω)) (m : ℕ)
    (hA : (m : A) = 0) (hm : (m : Ω) ≠ 0) :
    finiteEtaleTateLine T m A hA ≅
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) :=
  finiteEtaleLineAbIso T m A hA ≪≫
    (Etale.extendScalars A T).mapIso
      (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf p hm).some.symm ≪≫
    Etale.extendScalarsConstantZModIso T hA

private noncomputable def muHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleMuModulePresheaf T N ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := finiteEtaleMuModuleObj T N U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := finiteEtaleMuModuleObj T N U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def lineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (muHomEquiv T N A hA P))

private lemma lineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (lineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [lineHomEquiv, muHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

private lemma lineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {P Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ P) (g : P ⟶ Q) :
    lineHomEquiv T N A hA Q (f ≫ g) =
      lineHomEquiv T N A hA P f ≫
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
  ext U z
  change g.hom.app U (f.hom.app U
    (finiteEtaleTateOneGenerator A N T hA U 1 z)) =
    g.hom.app U ((lineHomEquiv T N A hA P f).hom.app U z)
  rw [lineHomEquiv_generator]

/-- The coordinate's coefficient Kummer class is an A-basis of ordinary degree-one
cohomology on the punctured affine line.
Source: Milne, Lectures on Etale Cohomology, Section 14, Proposition 14.3;
blueprint sk-prop-a1-kummer, Coefficients and Degrees 0 and 1.

Proof: put m = ell^N. A primitive m-th root over Omega identifies the root sheaf
with the constant Z/m sheaf and the finite twist with the constant A sheaf.
The finite-abelian-coefficient computation of AffineLineKummer identifies the
cohomology of this latter sheaf with Hom(Z/m,A), by pushing forward the root
Kummer class of t. This is a bijection, also when A is zero. Under the adjunction
for tensoring the root sheaf with A, each coefficient map is the canonical
insertion x ↦ 1 tensor x followed by an endomorphism of the twist. Every such
endomorphism is multiplication by an element a of A, because the twist is
constant of rank one on a connected scheme. Naturality of the Kummer extension,
of the Ext/derived-evaluation comparison and of restriction identifies its class
with a times the displayed kappa(t). Thus a ↦ a kappa(t) is surjective; the
finite-abelian calculation gives equal finite cardinalities, hence injectivity.
This map is A-linear, so its inverse supplies the asserted module isomorphism;
at 1 it has exactly the stated normalization. No primitive root occurs in this
map or its normalization.
(blueprint: lem-pur-rank-one-finite-kummer-generator). -/
theorem finite_kummer_generator
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ℓ N : ℕ) (_hℓ : ℓ.Prime) (hℓΩ : IsUnit (ℓ : Ω)) (_hN : 1 ≤ N)
    (hA : ((ℓ ^ N : ℕ) : A) = 0)
    (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(Line (Spec (.of Ω)), ⊤)))
    (f : (Line (Spec (.of Ω))).rootsOfUnitySheaf (ℓ ^ N) ⟶
      (Etale.moduleAbelianForget A (Line (Spec (.of Ω)))).obj
        (Scheme.finiteEtaleTateSheaf A (ℓ ^ N) (Line (Spec (.of Ω))) hA 1))
    (hf : ∀ V z, f.hom.app V z =
      Scheme.finiteEtaleTateOneGenerator A (ℓ ^ N) (Line (Spec (.of Ω))) hA V 1 z) :
    let X := Line (Spec (.of Ω))
    let F := Scheme.finiteEtaleTateSheaf A (ℓ ^ N) X hA 1
    let κ := kummerClass A X (openObject (Spec (.of Ω))) F (ℓ ^ N) hm f
    (∃ τ : ModuleCat.of A A ≅
        ((sections X.smallEtaleTopology A (openObject (Spec (.of Ω)))).rightDerived 1).obj F,
      τ.hom 1 = κ (coordinateUnit (Spec (.of Ω)))) := by
  classical
  let X := Line (Spec (.of Ω))
  let U := Punctured (Spec (.of Ω))
  let j : U ⟶ X := openImmersion (Spec (.of Ω))
  let m := ℓ ^ N
  let F := Scheme.finiteEtaleTateSheaf A m X hA 1
  let W := Scheme.Etale.mk j
  let B := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A)
  let R := Scheme.etaleRestriction j
  let FF := (Etale.moduleAbelianForget A X).obj F
  have hmΩ : (m : Ω) ≠ 0 := by simpa only [m, Nat.cast_pow] using (hℓΩ.pow N).ne_zero
  let pX : X ⟶ Spec (.of Ω) := lineProjection (Spec (.of Ω))
  let pU : U ⟶ Spec (.of Ω) := j ≫ pX
  let ζX := (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf pX hmΩ).some
  let ζU := (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf pU hmΩ).some
  let σ : F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A) := finiteLineConstantIso A Ω pX m hA hmΩ
  let τX : FF ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B :=
    (Etale.moduleAbelianForget A X).mapIso σ ≪≫ Etale.forget₂SheafConstantSheafIso A X
  let τ : R.obj FF ≅ (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B :=
    R.mapIso τX ≪≫ ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
      inferInstance).symm.app _) ≪≫ (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} j).app B
  have hj := AffineSpace.range_basicOpen_ι_coord (Spec (.of Ω))
  have : ConnectedSpace X := by
    dsimp [X, Line]
    infer_instance
  have : ConnectedSpace U := Etale.connectedSpace_of_range_eq_compl_zeroSection j hj
  have ht : AffineSpace.unitLineCoord j hj = coordinateUnit (Spec (.of Ω)) := by
    apply Units.ext
    rw [AffineSpace.val_unitLineCoord]
    exact (IsUnit.unit_spec _).symm
  let t := coordinateUnit (Spec (.of Ω))
  let hmU := AffineSpace.isUnit_natCast_of_ne_zero pU hmΩ
  let δt := U.kummerδ₀ m hmU (Additive.ofMul t)
  have hB : ∀ b : B, m • b = 0 := by
    intro b
    rw [nsmul_eq_mul, hA, zero_mul]
  have hη := AffineSpace.bijective_sheafHConstantSheafNatTrans j hj hmΩ B hB
  let η := (sheafHConstantSheafNatTrans U m 1
    (AffineSpace.kummerClassZMod j hj hmΩ)).app B
  have hgen : ∀ y : Sheaf.H (R.obj FF) 1,
      ∃ g : U.rootsOfUnitySheaf m ⟶ R.obj FF, Sheaf.H.map g 1 δt = y := by
    intro y
    obtain ⟨g, hg⟩ := hη.2 (Sheaf.H.map τ.hom 1 y)
    refine ⟨ζU.inv ≫ (constantSheaf _ _).map g ≫ τ.inv, ?_⟩
    change Sheaf.H.map ((constantSheaf _ _).map g) 1
      (AffineSpace.kummerClassZMod j hj hmΩ) = _ at hg
    dsimp only [AffineSpace.kummerClassZMod] at hg
    rw [ht] at hg
    change Sheaf.H.map ((constantSheaf _ _).map g) 1
      (Sheaf.H.map ζU.inv 1 δt) = _ at hg
    rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply, hg,
      ← Sheaf.H.map_comp_apply, τ.hom_inv_id, Sheaf.H.map_id_apply]
  have hcomp := (Etale.module_cohomology_conventions A X).2.1 F W 1
  let e := asIso ((Etale.moduleEvaluationForgetComparison A X W 1).app F) ≪≫
    (evaluationExt X W 1).app FF
  let ψ : ((sections X.smallEtaleTopology A W).rightDerived 1).obj F →+
      Sheaf.H (R.obj FF) 1 :=
    (R.mapExtPrecomp (restrictionRepresentingUnit j) FF 1).comp
      e.addCommGroupIsoToAddEquiv.toAddMonoidHom
  have hψ : Function.Bijective ψ := (restrictionExt_bijective j FF 1).comp
    e.addCommGroupIsoToAddEquiv.bijective
  let E : ((sections X.smallEtaleTopology A W).rightDerived 1).obj F ≃ A :=
    (Equiv.ofBijective ψ hψ).trans
      (((Sheaf.functorH _ 1).mapIso τ).addCommGroupIsoToAddEquiv.toEquiv.trans
        ((Equiv.ofBijective η hη).symm.trans (AddCommGrpCat.zmodHomEquiv B hB)))
  have : Finite (((sections X.smallEtaleTopology A W).rightDerived 1).obj F) :=
    Finite.of_equiv A E.symm
  have hψκ (g : X.rootsOfUnitySheaf m ⟶ FF) :
      ψ (kummerClass A X W F m hm g t) =
        Sheaf.H.map ((Scheme.rootsOfUnityRestrictionIso j m).inv ≫ R.map g) 1 δt := by
    dsimp only [ψ, AddMonoidHom.comp_apply]
    change R.mapExtPrecomp _ FF 1 (e.hom (kummerClass A X W F m hm g t)) = _
    change R.mapExtPrecomp _ FF 1
      ((evaluationExt X W 1).hom.app FF
        (((Etale.moduleEvaluationForgetComparison A X W 1).app F)
          (kummerClass A X W F m hm g t))) = _
    rw [kummerClass_evaluation, Functor.mapExtPrecomp_comp_mk₀]
    have hb := restrictionExt_kummer j m hm hmU t
    have hb' := congrArg
      (fun z ↦ z.comp (Abelian.Ext.mk₀ (Scheme.rootsOfUnityRestrictionIso j m).inv)
        (add_zero 1)) hb
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Abelian.Ext.comp_mk₀_id] at hb'
    refine (congrArg (fun z ↦ z.comp (Abelian.Ext.mk₀ (R.map g)) (add_zero 1))
      hb').trans ?_
    change _ = (δt.comp (Abelian.Ext.mk₀
      ((Scheme.rootsOfUnityRestrictionIso j m).inv ≫ R.map g)) (add_zero 1))
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero]
  have hsurj : Function.Surjective (fun a : A ↦
      a • kummerClass A X W F m hm f t) := by
    intro y
    obtain ⟨gU, hgU⟩ := hgen (ψ y)
    obtain ⟨g, hg⟩ := restrictionHom_surjective j ζX.symm τX
      ((Scheme.rootsOfUnityRestrictionIso j m).hom ≫ gU)
    let gmod := (lineHomEquiv X m A hA F).symm g
    obtain ⟨a, ha⟩ := Etale.exists_eq_smul_id_of_iso A σ gmod
    have hgf : g = f ≫ (Etale.moduleAbelianForget A X).map (a • 𝟙 F) := by
      have he := (lineHomEquiv X m A hA F).apply_symm_apply g
      rw [show (lineHomEquiv X m A hA F).symm g = gmod from rfl, ha] at he
      ext V z
      have hev := ConcreteCategory.congr_hom (congrArg (fun h ↦ h.hom.app V) he) z
      have hv := congrArg (fun b : F.obj.obj V ↦ a • b) (hf V z)
      have hgen := lineHomEquiv_generator X m A hA F (a • 𝟙 F) V z
      have hgen' : (lineHomEquiv X m A hA F (a • 𝟙 F)).hom.app V z =
          a • Scheme.finiteEtaleTateOneGenerator A m X hA V 1 z := hgen
      exact hev.symm.trans (hgen'.trans hv.symm)
    refine ⟨a, hψ.1 ?_⟩
    have hκg : kummerClass A X W F m hm g t =
        a • kummerClass A X W F m hm f t := by
      rw [hgf, kummerClass_comp, derivedSections_smul_id]
      rfl
    calc
      _ = ψ (kummerClass A X W F m hm g t) := congrArg ψ hκg.symm
      _ = Sheaf.H.map ((Scheme.rootsOfUnityRestrictionIso j m).inv ≫ R.map g) 1 δt :=
        hψκ g
      _ = Sheaf.H.map gU 1 δt := by
        have hh : (Scheme.rootsOfUnityRestrictionIso j m).inv ≫ R.map g = gU := by
          exact (congrArg (fun h ↦ (Scheme.rootsOfUnityRestrictionIso j m).inv ≫ h) hg).trans
            (Iso.inv_hom_id_assoc _ _)
        exact congrArg (fun h ↦ Sheaf.H.map h 1 δt) hh
      _ = ψ y := hgU
  have hbij := hsurj.bijective_of_nat_card_le (le_of_eq (Nat.card_congr E).symm)
  let L : A →ₗ[A] ((sections X.smallEtaleTopology A W).rightDerived 1).obj F :=
    { toFun := fun a ↦ a • kummerClass A X W F m hm f t
      map_add' := fun a b ↦ add_smul a b _
      map_smul' := fun a b ↦ mul_smul a b _ }
  exact ⟨(LinearEquiv.ofBijective L hbij).toModuleIso, one_smul A _⟩

end WeilConjectures.PurityFiniteSetting.RankOne
