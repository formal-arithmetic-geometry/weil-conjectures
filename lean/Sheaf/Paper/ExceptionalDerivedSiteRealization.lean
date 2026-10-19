/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalSiteRealization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
/-! # Derived realization of the actual etale/pro-etale system comparison
Source: blueprint def-weil-exceptional-inverse-image. All ordinary maps are fixed on
sections or by adjunction transposes; their derived maps retain the localization units.
(blueprint: def-pur-adic-derived-site-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  AlgebraicGeometry SheafOfModules

private theorem localizationComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {A B : C ⥤ E} {F G : D ⥤ E}
    (a : L ⋙ F ≅ A) (b : L ⋙ G ≅ B) (c : A ≅ B) :
    ∃! e : F ≅ G, ∀ X, e.hom.app (L.obj X) ≫ b.hom.app X =
      a.hom.app X ≫ c.hom.app X := by
  let e := Localization.liftNatIso L W _ _ F G (a ≪≫ c ≪≫ b.symm)
  have he (X) : e.hom.app (L.obj X) ≫ b.hom.app X =
      a.hom.app X ≫ c.hom.app X := by
    simp [e, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext L W
  intro X
  exact (cancel_mono (b.hom.app X)).1 ((he' X).trans (he X).symm)

private theorem cochain_derives
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    [Abelian A] [Abelian C] [HasDerivedCategory C]
    (F : A ⥤ C) [F.Additive] (V : DerivedCategory C ⥤ D) :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ V) := by
  intro X Y f hf
  have hX : X.obj.IsKInjective := X.property
  have hY : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (V.map (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map f.hom)))
  infer_instance

private def cochainRightUnitComposite
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ C) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _).hom ≫
  whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) F.rightDerivedFunctorUnit ≫
  (Functor.associator _ _ _).inv ≫
  whiskerRight (DerivedCategory.quotientCompQhIso A).hom F.rightDerivedFunctor

private theorem cochainRightUnitComposite_app
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ C) [F.Additive] (J : CochainComplex A ℤ) :
    (cochainRightUnitComposite F).app J =
      (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj J) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app J) := by
  simp [cochainRightUnitComposite, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv]
  rfl

private def cochainRightUnit
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ C) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app J := (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj J) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).inv.app J)
  naturality X Y f := by
    have hx := cochainRightUnitComposite_app F X
    have hy := cochainRightUnitComposite_app F Y
    have h := (cochainRightUnitComposite F).naturality f
    rw [hx, hy] at h
    exact h

private theorem cochainRightUnit_app
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ C) [F.Additive] (J : CochainComplex A ℤ) :
    (cochainRightUnit F).app J =
      (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj J) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).inv.app J) := rfl

private theorem cochainRightUnit_isIso
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ C) [F.Additive] (J : CochainComplex A ℤ) [J.IsKInjective] :
    IsIso ((cochainRightUnit F).app J) := by
  rw [cochainRightUnit_app]
  infer_instance

attribute [local instance] cochainRightUnit_isIso

attribute [local irreducible] WeilConjectures.integralExceptionalProRealization
  WeilConjectures.integralExceptionalEtaleRealization
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem squareNormalization
    {C : Type*} [Category* C] {X Y Z W : C}
    (s : X ≅ Y) (r : Z ≅ W) (f : X ⟶ Z) (g : Y ⟶ W) :
    f ≫ r.hom = s.hom ≫ g ↔ s.inv ≫ f = g ≫ r.inv := by
  constructor
  · intro h
    have h' := congrArg (fun k ↦ s.inv ≫ k ≫ r.inv) h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h'
  · intro h
    have h' := congrArg (fun k ↦ s.hom ≫ k ≫ r.hom) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using h'

/-- The universal-unit square on all cochain representatives for direct image.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def CategoryTheory.Functor.IsDerivedRightComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    (G : B ⥤ A) [G.Additive] (R : B ⥤ D) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : A ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : D ⥤ C) [T.Additive] (V : DerivedCategory B ⥤ DerivedCategory A)
    (vunit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ V)
    (comparison : G ⋙ S ≅ R ⋙ T)
    (e : V ⋙ S.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ T.rightDerivedFunctor) : Prop :=
    ∀ J : CochainComplex B ℤ,
        S.mapDerivedCategory.map (vunit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
            T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app J) =
          S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J) ≫
            ((DerivedCategory.quotientCompQhIso C).inv.app _ ≫
              T.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj
                ((R.mapHomologicalComplex (.up ℤ)).obj J)) ≫
              T.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).inv.app
                ((R.mapHomologicalComplex (.up ℤ)).obj J)))

private theorem derivedRightComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    (G : B ⥤ A) [G.Additive] (R : B ⥤ D) [R.Additive] [R.IsEquivalence]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : A ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : D ⥤ C) [T.Additive] (V : DerivedCategory B ⥤ DerivedCategory A)
    (vunit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ V)
    (computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (vunit.app I))
    (comparison : G ⋙ S ≅ R ⋙ T) :
    ∃! e : V ⋙ S.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ T.rightDerivedFunctor,
      CategoryTheory.Functor.IsDerivedRightComparison G R S T V vunit comparison e := by
  unfold CategoryTheory.Functor.IsDerivedRightComparison
  let normalization (e : V ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ T.rightDerivedFunctor) : Prop :=
    ∀ J : CochainComplex B ℤ,
      S.mapDerivedCategory.map (vunit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
          T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app J) =
        S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J) ≫
          (cochainRightUnit T).app ((R.mapHomologicalComplex (.up ℤ)).obj J)
  let RF := V ⋙ S.mapDerivedCategory
  let RG := R.mapDerivedCategory ⋙ T.rightDerivedFunctor
  let a : (G ⋙ S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF := {
    app J := S.mapDerivedCategoryFactors.inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫ S.mapDerivedCategory.map (vunit.app J)
    naturality X Y f := by
      have h := (whiskerLeft (G.mapHomologicalComplex (.up ℤ))
        S.mapDerivedCategoryFactors.inv ≫ (Functor.associator _ _ _).inv ≫
          whiskerRight vunit S.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom).naturality f
      simpa only [RF, RG, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
        Functor.mapHomologicalComplex,
        Category.id_comp, Category.comp_id, Category.assoc] using h }
  let b : (R ⋙ T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG := {
    app J := (cochainRightUnit T).app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
      T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app J)
    naturality X Y f := by
      have h := (whiskerLeft (R.mapHomologicalComplex (.up ℤ)) (cochainRightUnit T) ≫
        (Functor.associator _ _ _).inv ≫
          whiskerRight R.mapDerivedCategoryFactors.inv T.rightDerivedFunctor ≫
          (Functor.associator _ _ _).hom).naturality f
      simpa only [RF, RG, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
        Functor.mapHomologicalComplex,
        Category.id_comp, Category.comp_id, Category.assoc] using h }
  have ha : RF.IsRightDerivedFunctor a (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply (cochain_derives (G ⋙ S) (𝟭 _)).isRightDerivedFunctor_of_isIso a
    intro I
    change IsIso (a.app I.obj)
    have : I.obj.IsKInjective := I.property
    have : IsIso (vunit.app I.obj) :=
      computes I.obj I.property
    have : IsIso (S.mapDerivedCategory.map
        (vunit.app I.obj)) := inferInstance
    change IsIso
      (S.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
        S.mapDerivedCategory.map (vunit.app I.obj))
    infer_instance
  have hb : RG.IsRightDerivedFunctor b (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply (cochain_derives (R ⋙ T) (𝟭 _)).isRightDerivedFunctor_of_isIso b
    intro I
    change IsIso (b.app I.obj)
    have : I.obj.IsKInjective := I.property
    have : CochainComplex.IsKInjective
        ((R.mapHomologicalComplex (.up ℤ)).obj I.obj) := inferInstance
    have : IsIso ((cochainRightUnit T).app
        ((R.mapHomologicalComplex (.up ℤ)).obj I.obj)) := inferInstance
    change IsIso
      ((cochainRightUnit T).app ((R.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
        T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app I.obj))
    infer_instance
  let c : (G ⋙ S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      (R ⋙ T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    isoWhiskerRight
      (NatIso.mapHomologicalComplex comparison (.up ℤ))
      DerivedCategory.Q
  let e := Functor.rightDerivedNatIso RF RG a b
    (HomologicalComplex.quasiIso _ (.up ℤ)) c
  have normalize (q : RF ≅ RG) :
      normalization q ↔
        ∀ J, a.app J ≫ q.hom.app (DerivedCategory.Q.obj J) =
          c.hom.app J ≫ b.app J := by
    change (∀ J : CochainComplex B ℤ,
      S.mapDerivedCategory.map (vunit.app J) ≫ q.hom.app (DerivedCategory.Q.obj J) ≫
          T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app J) =
        S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J) ≫
          (cochainRightUnit T).app ((R.mapHomologicalComplex (.up ℤ)).obj J)) ↔
      ∀ J : CochainComplex B ℤ,
        (S.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
          S.mapDerivedCategory.map (vunit.app J)) ≫ q.hom.app (DerivedCategory.Q.obj J) =
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J) ≫
          (cochainRightUnit T).app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app J)
    apply forall_congr'
    intro J
    simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv] using (squareNormalization (S.mapDerivedCategoryFactors.app
      ((G.mapHomologicalComplex (.up ℤ)).obj J))
      (T.rightDerivedFunctor.mapIso (R.mapDerivedCategoryFactors.app J))
      (S.mapDerivedCategory.map (vunit.app J) ≫ q.hom.app (DerivedCategory.Q.obj J))
      (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J) ≫
        (cochainRightUnit T).app ((R.mapHomologicalComplex (.up ℤ)).obj J)))
  have he : normalization e := by
    apply (normalize e).2
    intro J
    exact Functor.rightDerivedNatTrans_app RF RG a b
      (HomologicalComplex.quasiIso _ (.up ℤ)) c.hom J
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Functor.rightDerived_ext RF a (HomologicalComplex.quasiIso _ (.up ℤ))
  ext J
  exact ((normalize e').1 he' J).trans (((normalize e).1 he J).symm)

/-- The exact factorization square on all cochain representatives for inverse image.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def CategoryTheory.Functor.IsDerivedInverseComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive]
    (R : B ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : A ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (V : DerivedCategory A ⥤ DerivedCategory B)
    (factors : DerivedCategory.Q ⋙ V ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (comparison : F ⋙ R ≅ S ⋙ T)
    (e : V ⋙ R.mapDerivedCategory ≅ S.mapDerivedCategory ⋙ T.mapDerivedCategory) : Prop :=
    ∀ J : CochainComplex A ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
            T.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app J) ≫
            T.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj J) =
          R.mapDerivedCategory.map (factors.hom.app J) ≫
            R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J)

private theorem derivedInverseComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive]
    (R : B ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : A ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (V : DerivedCategory A ⥤ DerivedCategory B)
    (factors : DerivedCategory.Q ⋙ V ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (comparison : F ⋙ R ≅ S ⋙ T) :
    ∃! e : V ⋙ R.mapDerivedCategory ≅ S.mapDerivedCategory ⋙ T.mapDerivedCategory,
      CategoryTheory.Functor.IsDerivedInverseComparison F R S T V factors comparison e := by
  unfold CategoryTheory.Functor.IsDerivedInverseComparison
  let a : DerivedCategory.Q ⋙ (V ⋙ R.mapDerivedCategory) ≅
      (F.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight factors R.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ R.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  let b : DerivedCategory.Q ⋙ (S.mapDerivedCategory ⋙ T.mapDerivedCategory) ≅
      (S.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight S.mapDerivedCategoryFactors T.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ T.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  let c : (F.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ)) ⋙
      DerivedCategory.Q ≅
      (S.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    isoWhiskerRight
      (NatIso.mapHomologicalComplex comparison (.up ℤ))
      DerivedCategory.Q
  obtain ⟨e, he, hu⟩ := localizationComparison DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) a b c
  refine ⟨e, ?_, ?_⟩
  · intro J
    simpa only [a, b, c, Iso.trans_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      whiskerRight_app, whiskerLeft_app, NatIso.mapHomologicalComplex, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc] using (he J).trans
        (Category.assoc _ _ _)
  · intro e' he'
    apply hu e'
    intro J
    simpa only [a, b, c, Iso.trans_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      whiskerRight_app, whiskerLeft_app, NatIso.mapHomologicalComplex, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc] using (he' J).trans
        (Category.assoc _ _ _).symm

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E))
  (B : IntegralExceptionalComparison l E W P)

/-- The complete inverse realization normalization on all cochain complexes.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def IsIntegralExceptionalSiteDerivedInverse (n : ℕ)
    (e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory) :
            Prop :=
  CategoryTheory.Functor.IsDerivedInverseComparison (B.ordinary.lift n).modules
    (integralExceptionalProRealization l E W n) (integralExceptionalEtaleRealization l E W n)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).inverse (B.derived.level n).inverseFactors
    (integralExceptionalSiteInverse l E W P B n) e

/-- The exact derived site inverse comparison, fixed on every cochain representative.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization).
Proof: apply exact localization to the preceding ordinary inverse comparison and
compose the two specified factorization isomorphisms. Their square is the displayed
condition. Every derived arrow is represented by a roof, proving uniqueness. -/
theorem integralExceptionalSiteDerivedInverse_existsUnique (n : ℕ) :
    ∃! e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory,
      IsIntegralExceptionalSiteDerivedInverse l E W P B n e := by
  unfold IsIntegralExceptionalSiteDerivedInverse
  exact derivedInverseComparison (B.ordinary.lift n).modules
    (integralExceptionalProRealization l E W n) (integralExceptionalEtaleRealization l E W n)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).inverse (B.derived.level n).inverseFactors
    (integralExceptionalSiteInverse l E W P B n)

/-- The exact inverse comparison, fixed by its universal representative square.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
@[no_expose] def integralExceptionalSiteDerivedInverse (n : ℕ) :
    (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory :=
  (integralExceptionalSiteDerivedInverse_existsUnique l E W P B n).choose

/-- The actual cochain-level unit of derived site direct image.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
def integralExceptionalSiteFixedRightUnit (n : ℕ)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    DerivedCategory.Q.obj
      (((ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapHomologicalComplex
           (.up ℤ)).obj J) ⟶
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.obj
         (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctorUnit.app
         ((HomotopyCategory.quotient _ _).obj J) ≫
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.map
         ((DerivedCategory.quotientCompQhIso _).inv.app J)

/-- The complete right realization normalization on all cochain complexes.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def IsIntegralExceptionalSiteDerivedRight (n : ℕ)
    (e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor) :
            Prop :=
  CategoryTheory.Functor.IsDerivedRightComparison (B.ordinary.right n)
    (integralExceptionalProRealization l E W n) (integralExceptionalEtaleRealization l E W n)
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).direct (B.derived.level n).directUnit
    (integralExceptionalSiteRight l E W P B n) e

/-- The derived site direct comparison is fixed by both universal right-derived units.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization).
Proof: on K-injective representatives both derived units are invertible and the
ordinary section comparison determines the map. Exact realization is an equivalence,
so it preserves K-injective representatives. Universal right derivation extends this
map uniquely and gives the displayed square on all complexes. -/
theorem integralExceptionalSiteDerivedRight_existsUnique (n : ℕ) :
    ∃! e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor,
      IsIntegralExceptionalSiteDerivedRight l E W P B n e := by
  unfold IsIntegralExceptionalSiteDerivedRight
  exact derivedRightComparison (B.ordinary.right n)
    (integralExceptionalProRealization l E W n) (integralExceptionalEtaleRealization l E W n)
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).direct (B.derived.level n).directUnit
    (B.derived.level n).computes (integralExceptionalSiteRight l E W P B n)

/-- The universal-unit-normalized derived site direct comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
@[no_expose] def integralExceptionalSiteDerivedRight (n : ℕ) :
    (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor :=
  (integralExceptionalSiteDerivedRight_existsUnique l E W P B n).choose
end WeilConjectures
