module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleKInjectivePullbackAbutment
import all WeilConjectures.AlgebraicGeometry.EtaleKInjectiveUnitLeray
import WeilConjectures.AlgebraicGeometry.ObjectSectionsNaturality

/-! # Cohomology pullback on a fixed resolution

Source: Stacks Project, Tags 03Q8 and 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option Elab.async false
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance
attribute [local instance] normalizationRestrictionAugmentation_quasiIso

private theorem single_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
    (G : C ⥤ D) (H : D ⥤ E) [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (n : ℤ) (F : C) :
    (H.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app F) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app (G.obj F) =
    (HomologicalComplex.singleMapHomologicalComplex (G ⋙ H) (.up ℤ) n).hom.app F := by
  ext i
  by_cases hi : i = n
  · subst i
    simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private theorem single_natIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
    {G H : C ⥤ D} [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (e : G ≅ H) (n : ℤ) (F : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) n).obj F) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app F =
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app F ≫
      (HomologicalComplex.single D (.up ℤ) n).map (e.hom.app F) := by
  ext i
  by_cases hi : i = n
  · subst i
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single_map_f_self]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private noncomputable def mappedAug {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] (F : C)
    (J : CochainComplex C ℤ) (ι : (HomologicalComplex.single C (.up ℤ) 0).obj F ⟶ J) :
    (HomologicalComplex.single D (.up ℤ) 0).obj (G.obj F) ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj J :=
  (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app F ≫
    (G.mapHomologicalComplex (.up ℤ)).map ι

private theorem augmentation_triangle {C D E : Type*}
    [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
    (A : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E)
    [A.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (e : H ≅ G ⋙ A) (F : C) (J : CochainComplex C ℤ)
    (ι : (HomologicalComplex.single C (.up ℤ) 0).obj F ⟶ J) :
    (A.mapHomologicalComplex (.up ℤ)).map (mappedAug G F J ι) ≫
        (NatIso.mapHomologicalComplex e.symm (.up ℤ)).hom.app J =
      (HomologicalComplex.singleMapHomologicalComplex A (.up ℤ) 0).hom.app (G.obj F) ≫
        (HomologicalComplex.single E (.up ℤ) 0).map (e.inv.app F) ≫
        mappedAug H F J ι := by
  have hc := single_comp G A 0 F
  have hn := single_natIso e.symm 0 F
  have ha := (NatIso.mapHomologicalComplex e.symm (.up ℤ)).hom.naturality ι
  have ha' : (A.mapHomologicalComplex (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map ι) ≫
      (NatIso.mapHomologicalComplex e.symm (.up ℤ)).hom.app J =
      (NatIso.mapHomologicalComplex e.symm (.up ℤ)).hom.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj F) ≫
        (H.mapHomologicalComplex (.up ℤ)).map ι := ha
  dsimp only [mappedAug]
  rw [CategoryTheory.Functor.map_comp, Category.assoc, ha']
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono
    ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app F)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [hn, ← hc]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(A.mapHomologicalComplex (.up ℤ)).map_id]
  erw [Category.id_comp, Category.comp_id]
  rfl

private theorem normalizationSectionsIso_eq {X : Scheme.{u}} (W : X.Etale) :
    normalizationSectionsIso W = (etaleObjectSectionsIso W).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  dsimp only [normalizationSectionsIso, etaleObjectSectionsIso, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv]
  simp only [Category.assoc]
  rw [(Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale W.left)).hom.naturality_assoc]

private theorem sections_restriction {X : Scheme.{u}} {W W' : X.Etale}
    (b : W' ⟶ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (sectionsPullbackNat b.left).app ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) ≫
        (Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((upperStarComp AddCommGrpCat.{u + 1} b.left W.hom W'.hom b.w.symm).inv.app F) ≫
        (normalizationSectionsIso W').hom.app F =
      (normalizationSectionsIso W).hom.app F ≫ F.obj.map b.op := by
  have h := objectSections_naturality b F
  apply (cancel_epi ((etaleObjectSectionsIso W).hom.app F)).1
  rw [normalizationSectionsIso_eq, normalizationSectionsIso_eq]
  try simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hr : (sectionsPullbackNat b.left).app
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) =
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} b.left
        ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) := by
    exact sections_unit b.left _
  rw [hr, ← reassoc_of% h]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [Iso.symm_hom]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [Iso.hom_inv_id_app]
  rfl

private theorem map_comp_three {C D E : Type*}
    [Category C] [Category D] [Category E] (T : D ⥤ E) (G : C ⥤ D)
    {A B : D} {K L M : C} (a : A ⟶ B) (b : B ⟶ G.obj K)
    (c : K ⟶ L) (d : L ⟶ M) :
    T.map (a ≫ b ≫ G.map (c ≫ d)) =
      T.map (a ≫ b ≫ G.map c) ≫ (G ⋙ T).map d := by
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

private theorem resolution_triangle_general {X Y : Scheme.{u}} (a : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (R : CochainComplex.KInjectiveResolutionChoice K)
    (S : CochainComplex.KInjectiveResolutionChoice L)
    (v : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (j : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex
      (.up ℤ)).obj R.complex ⟶ S.complex)
    (hj : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex (.up ℤ)).map
      R.map ≫ j = v ≫ S.map)
    (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj R.complex ⟶
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj S.complex)
    (hw : ∀ i : ℤ, w.f i = globalSectionsUpperStarMap AddCommGrpCat.{u + 1} a
        (R.complex.X i) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f i)) (n : ℤ) :
    (@resolutionEtaleCohomologyIso X K R.complex R.map R.quasiIso R.isKInjective n).inv ≫
      HomologicalComplex.homologyMap w n ≫
      (@resolutionEtaleCohomologyIso Y L S.complex S.map S.quasiIso S.isKInjective n).hom =
      rawAffineComplexPullback n a K ≫
        (cohomology AddCommGrpCat.{u + 1} Y n).map (DerivedCategory.Q.map v) := by
  have hab := etaleKInjective_pullback_abutment a K L v R S j
    ⟨Homotopy.ofEq hj⟩ w hw n
  have hm := map_comp_three
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n)
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y)
    ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app
        (DerivedCategory.Q.obj K)))
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} a).hom.app
      ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategory.obj (DerivedCategory.Q.obj K)))
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryFactors.hom.app K)
    (DerivedCategory.Q.map v)
  exact hab.trans hm

private theorem native_resolution_triangle {X Y : Scheme.{u}} (a : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (R : K.KInjectiveResolution)
    (S : L.KInjectiveResolution)
    (v : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (j : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex
      (.up ℤ)).obj R.I ⟶ S.I)
    (hj : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex (.up ℤ)).map
      R.ι ≫ j = v ≫ S.ι)
    (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj R.I ⟶
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj S.I)
    (hw : ∀ i : ℤ, w.f i = globalSectionsUpperStarMap AddCommGrpCat.{u + 1} a
        (R.I.X i) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f i)) (n : ℤ) :
    (R.homologyRightDerivedFunctorObjIso
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).hom ≫
      HomologicalComplex.homologyMap w n ≫
      (S.homologyRightDerivedFunctorObjIso
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).inv =
      rawAffineComplexPullback n a K ≫
        (cohomology AddCommGrpCat.{u + 1} Y n).map (DerivedCategory.Q.map v) := by
  have hR : R.homologyRightDerivedFunctorObjIso
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) n =
      (@resolutionEtaleCohomologyIso X K R.I R.ι R.quasiIso_ι R.isKInjective n).symm := by
    rfl
  have hS : S.homologyRightDerivedFunctorObjIso
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n =
      (@resolutionEtaleCohomologyIso Y L S.I S.ι S.quasiIso_ι S.isKInjective n).symm := by
    rfl
  rw [hR, hS]
  exact resolution_triangle_general a K L
    ⟨R.I, R.ι, R.quasiIso_ι, R.isKInjective⟩
    ⟨S.I, S.ι, S.quasiIso_ι, S.isKInjective⟩ v j hj w hw n

private noncomputable def restrictedComplexMap {X : Scheme.{u}} {W W' : X.Etale}
    (b : W' ⟶ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) :
    ((upperStar AddCommGrpCat.{u + 1} b.left).mapHomologicalComplex (.up ℤ)).obj
        (normalizationRestrictionComplex W F I) ⟶
      normalizationRestrictionComplex W' F I where
  f n := (upperStarComp AddCommGrpCat.{u + 1} b.left W.hom W'.hom b.w.symm).inv.app
    ((normalizationBaseComplex F I).X n)
  comm' i j _ :=
    ((upperStarComp AddCommGrpCat.{u + 1} b.left W.hom W'.hom b.w.symm).inv.naturality
      ((normalizationBaseComplex F I).d i j)).symm

private noncomputable def sectionsComparison {X Y : Scheme.{u}} (a : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (j : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj L where
  f n := (sectionsPullbackNat a).app (K.X n) ≫
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f n)
  comm' i k _ := by
    change ((sectionsPullbackNat a).app (K.X i) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f i)) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (L.d i k) =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (K.d i k) ≫
        (sectionsPullbackNat a).app (K.X k) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f k)
    rw [Category.assoc, ← Functor.map_comp, j.comm, Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map,
      Functor.mapHomologicalComplex_obj_d] using congrArg
      (fun z ↦ z ≫ (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f k))
      ((sectionsPullbackNat a).naturality (K.d i k)).symm

private theorem sectionsComparison_f {X Y : Scheme.{u}} (a : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (j : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (n : ℤ) :
    (sectionsComparison a K L j).f n =
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} a (K.X n) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f n) := by
  change (sectionsPullbackNat a).app _ ≫ _ = _
  exact congrArg
    (fun z ↦ z ≫ (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f n))
    (sections_unit a (K.X n))

private noncomputable def restrictedSectionChain {X : Scheme.{u}} {W W' : X.Etale}
    (b : W' ⟶ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) :=
  sectionsComparison b.left (normalizationRestrictionComplex W F I)
    (normalizationRestrictionComplex W' F I) (restrictedComplexMap b F I)

private noncomputable def restrictedCoefficientMap {X : Scheme.{u}} {W W' : X.Etale}
    (b : W' ⟶ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  normalizationRestrictionCoefficientMap b F

private theorem restrictedAugmentation_comm {X : Scheme.{u}} {W W' : X.Etale}
    (b : W' ⟶ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) :
    ((upperStar AddCommGrpCat.{u + 1} b.left).mapHomologicalComplex (.up ℤ)).map
        (normalizationRestrictionAugmentation W F I) ≫ restrictedComplexMap b F I =
      restrictedCoefficientMap b F ≫ normalizationRestrictionAugmentation W' F I := by
  ext n : 1
  exact congrArg (fun k ↦ k.f n)
    (augmentation_triangle (upperStar AddCommGrpCat.{u + 1} b.left)
      (upperStar AddCommGrpCat.{u + 1} W.hom) (upperStar AddCommGrpCat.{u + 1} W'.hom)
      (upperStarComp AddCommGrpCat.{u + 1} b.left W.hom W'.hom b.w.symm)
      F (normalizationBaseComplex F I) (normalizationBaseAugmentation F I))

/-- Evaluate the restricted resolution termwise using the sections isomorphism.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-weil-pbc-raw-restricted-resolution-restriction). -/
private noncomputable def sectionComplexIso {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    ((Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj
      (normalizationRestrictionComplex ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I) ≅
    (((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
      (.up ℤ)).obj (normalizationPresheafComplex f F I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (normalizationSectionsIso
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)).app ((normalizationBaseComplex F I).X i))
    (fun i j _ ↦ (normalizationSectionsIso
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)).hom.naturality
        ((normalizationBaseComplex F I).d i j) |>.symm)

private noncomputable def sectionTail {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    (((Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).obj
      (normalizationRestrictionComplex
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I)).homology (q : ℤ) ≅
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
      (sectionComplexIso f F I V) ≪≫
  ((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
    ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))

private theorem sectionTail_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    {V V' : S.Etale} (t : V' ⟶ V) :
    let _W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
    let _W' := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V'
    let b := (MorphismProperty.Over.pullback @Etale ⊤ f).map t
    HomologicalComplex.homologyMap
        (restrictedSectionChain b F I) (q : ℤ) ≫
        (sectionTail f q F I V').hom =
      (sectionTail f q F I V).hom ≫
        ((normalizationPresheafComplex f F I).homology (q : ℤ)).map t.op := by
  intro W W' b
  let P := normalizationPresheafComplex f F I
  let E := (evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
  let E' := (evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V')
  let τ : E ⟶ E' := (evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map t.op
  let e := sectionComplexIso f F I V
  let e' := sectionComplexIso f F I V'
  let z := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P
  have hw : restrictedSectionChain b F I ≫ e'.hom =
      e.hom ≫ z := by
    ext i : 1
    change (sectionsComparison _ _ _ _).f i ≫ _ = _
    change ((sectionsPullbackNat b.left).app _ ≫
      (Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((restrictedComplexMap b F I).f i)) ≫ _ = _
    exact sections_restriction b ((normalizationBaseComplex F I).X i)
  have hn : HomologicalComplex.homologyMap
      (restrictedSectionChain b F I) (q : ℤ) ≫
      HomologicalComplex.homologyMap e'.hom (q : ℤ) =
      HomologicalComplex.homologyMap e.hom (q : ℤ) ≫
      HomologicalComplex.homologyMap z (q : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, hw, HomologicalComplex.homologyMap_comp]
  have hτ := NatTrans.app_homology τ (P.sc (q : ℤ))
  have hz : HomologicalComplex.homologyMap z (q : ℤ) ≫
      ((P.sc (q : ℤ)).mapHomologyIso E').hom =
      ((P.sc (q : ℤ)).mapHomologyIso E).hom ≫ τ.app (P.homology (q : ℤ)) := by
    change ShortComplex.homologyMap ((P.sc (q : ℤ)).mapNatTrans τ) ≫ _ =
      _ ≫ τ.app (P.sc (q : ℤ)).homology
    rw [hτ]
    simp only [Iso.hom_inv_id_assoc]
  change HomologicalComplex.homologyMap _ (q : ℤ) ≫
      HomologicalComplex.homologyMap e'.hom (q : ℤ) ≫
        ((P.sc (q : ℤ)).mapHomologyIso E').hom =
    HomologicalComplex.homologyMap e.hom (q : ℤ) ≫
      ((P.sc (q : ℤ)).mapHomologyIso E).hom ≫ τ.app (P.homology (q : ℤ))
  rw [← Category.assoc, hn, Category.assoc, hz]

private theorem assemble_restriction {C : Type*} [Category C]
    {A B D E Z Z' : C} (r : A ≅ B) (s : D ≅ E) (e : B ≅ Z) (e' : E ≅ Z')
    (a : A ⟶ D) (w : B ⟶ E) (t : Z ⟶ Z')
    (hr : r.hom ≫ w ≫ s.inv = a) (ht : w ≫ e'.hom = e.hom ≫ t) :
    a ≫ (s ≪≫ e').hom = (r ≪≫ e).hom ≫ t := by
  rw [← hr]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ht]

attribute [local irreducible] upperStar upperStarComp normalizationRestrictedIso

private theorem restrictedIso_factor {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    normalizationRestrictedIso f q F I V =
      normalizationChartResolutionIso f q F I V ≪≫
        sectionTail f q F I V := by
  unfold normalizationRestrictedIso sectionTail
  apply Iso.ext
  rfl

private theorem restriction_on_resolution {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) {V V' : S.Etale} (t : V' ⟶ V) :
    normalizationCohomologyRestriction f q F t ≫
        (normalizationRestrictedIso f q F I V').hom =
      (normalizationRestrictedIso f q F I V).hom ≫
        ((normalizationPresheafComplex f F I).homology (q : ℤ)).map t.op := by
  let B : S.Etale ⥤ X.Etale := MorphismProperty.Over.pullback @Etale ⊤ f
  let W : X.Etale := B.obj V
  let W' : X.Etale := B.obj V'
  let b : W' ⟶ W := B.map t
  let r := normalizationChartResolutionIso f q F I V
  let s := normalizationChartResolutionIso f q F I V'
  have hr : r.hom ≫ HomologicalComplex.homologyMap
      (restrictedSectionChain b F I) (q : ℤ) ≫ s.inv =
      normalizationCohomologyRestriction f q F t := by
    dsimp only [r, s]
    let j := restrictedComplexMap b F I
    let v := restrictedCoefficientMap b F
    have hj := restrictedAugmentation_comm b F I
    exact native_resolution_triangle b.left _ _ (normalizationRestrictedResolution W F I)
      (normalizationRestrictedResolution W' F I) v j hj (restrictedSectionChain b F I)
      (fun n ↦ sectionsComparison_f b.left _ _ j n) (q : ℤ)
  have ht := sectionTail_naturality f q F I t
  rw [restrictedIso_factor f q F I V, restrictedIso_factor f q F I V']
  exact assemble_restriction r s (sectionTail f q F I V) (sectionTail f q F I V')
    _ _ _ hr ht

/-- Etale chart pullback is the restriction on the chosen resolution's section homology.
Source: Stacks Project, Tag 03Q8, restriction of injective resolutions; Tag 03Q9,
final injective-complex paragraph.
(blueprint: lem-weil-pbc-raw-restricted-resolution-restriction).

Proof: Work first with an arbitrary injective resolution I. The restricted
augmentations commute with inverse-image composition by naturality and the
single-complex comparison's composition law. The existing K-injective pullback
abutment theorem therefore identifies cohomology pullback with the homology of
the section-chain map, under the two resolution isomorphisms.

The section-chain map is sectionsPullbackNat followed by global sections of the
inverse-image composition isomorphism. The sections-unit identity and
objectSections_naturality identify this map, under normalizationSectionsIso,
with the presheaf restriction in each degree. Apply homology to this square.
Naturality of mapHomologyIso under the natural transformation between the two
evaluation functors identifies the final evaluation factors as well. Compose
the two squares and cancel the intermediate resolution isomorphism. Finally
specialize I to injectiveResolution F. No step assumes positive degree or a
nonempty chart. -/
theorem rawRestrictedResolution_restriction {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (t : V' ⟶ V) :
    normalizationCohomologyRestriction f q F t ≫
        (normalizationRestrictedIso f q F (injectiveResolution F) V').hom =
      (normalizationRestrictedIso f q F (injectiveResolution F) V).hom ≫
        ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ)).map t.op := by
  exact restriction_on_resolution f q F (injectiveResolution F) t

end AlgebraicGeometry.Etale
