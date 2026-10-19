/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionResolution
import Mathlib.CategoryTheory.Limits.Final
/-! # The normalized derived arithmetic comparison

Source: Stacks Project, Tags 0941 and 0H9K; uniqueness of right derived functors.
-/

@[expose] public section
set_option autoImplicit false
universe a b w uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic
private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }
private lemma limitMap_isIso
    (A : Type a) [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsIso (limitMap e I) := by
  have : (index e).Initial := Functor.initial_of_adjunction (indexAdjunction e he)
  have (i : ℤ) : IsIso ((limitMap e I).f i) := by
    dsimp [limitMap]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

variable (A : Type a) [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
  (η : limitComplex A ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
private noncomputable def limitNat (e : ℕ) :
    limitComplex A ⟶ complexRestriction A e ⋙ limitComplex A where
  app X := limitMap e X
  naturality X Y f := by
    ext i
    exact limit.map_pre (f.f i) (index e)
private noncomputable def comparisonUnit (e : ℕ) :
    limitComplex A ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (derivedRestriction A e ⋙ RF) :=
  Functor.whiskerRight (limitNat A e) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (complexRestriction A e) η ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (restriction A e).mapDerivedCategoryFactors.inv RF ≫
    (Functor.associator _ _ _).hom
private lemma comparisonUnit_app (e : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (comparisonUnit A RF η e).app X =
      DerivedCategory.Q.map (limitMap e X) ≫
        η.app ((complexRestriction A e).obj X) ≫
        RF.map ((restriction A e).mapDerivedCategoryFactors.inv.app X) := by
  simp [comparisonUnit, limitNat]

private noncomputable def comparison (e : ℕ)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))) :
    RF ⟶ derivedRestriction A e ⋙ RF := by
  let _ := hRF
  exact RF.rightDerivedDesc η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ (comparisonUnit A RF η e)
private lemma comparison_fac (e : ℕ)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    η.app X ≫ (comparison A RF η e hRF).app (DerivedCategory.Q.obj X) ≫
        RF.map ((restriction A e).mapDerivedCategoryFactors.hom.app X) =
      DerivedCategory.Q.map (limitMap e X) ≫ η.app ((complexRestriction A e).obj X) := by
  let _ := hRF
  have h := RF.rightDerived_fac_app η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ (comparisonUnit A RF η e) X
  change η.app X ≫ (comparison A RF η e hRF).app _ = _ at h
  rw [← Category.assoc, h, comparisonUnit_app]
  simp
private lemma comparison_isIso (e : ℕ) (he : 1 ≤ e)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (hres : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : X ⟶ I),
        I.IsKInjective ∧ QuasiIso j) :
    IsIso (comparison A RF η e hRF) := by
  have hI (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hi : I.IsKInjective) :
      IsIso ((comparison A RF η e hRF).app (DerivedCategory.Q.obj I)) := by
    let _ := hi
    have := restriction_preservesKInjectives A e he I
    have := hη I hi
    have := hη _ (restriction_preservesKInjectives A e he I)
    have := limitMap_isIso A e he I
    have h := comparison_fac A RF η e hRF I
    have : IsIso (η.app I ≫ (comparison A RF η e hRF).app (DerivedCategory.Q.obj I) ≫
        RF.map ((restriction A e).mapDerivedCategoryFactors.hom.app I)) := by
      rw [h]
      infer_instance
    exact (isIso_comp_left_iff (η.app I) _).1
      (by simpa only [Category.assoc] using
        ((isIso_comp_right_iff _ (RF.map
          ((restriction A e).mapDerivedCategoryFactors.hom.app I))).1
            (by simpa only [Category.assoc] using this)))
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  let Q := DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)
  let X := Q.objPreimage Z
  obtain ⟨I,j,hi,hj⟩ := hres X
  let _ := hj
  let f := comparison A RF η e hRF
  have := hI I hi
  have := f.naturality (Q.map j)
  have : IsIso (f.app (Q.obj X)) := by
    have : IsIso (RF.map (Q.map j) ≫ f.app (Q.obj I)) := by infer_instance
    rw [f.naturality (Q.map j)] at this
    exact (isIso_comp_right_iff _ ((derivedRestriction A e ⋙ RF).map (Q.map j))).1 this
  exact (NatTrans.isIso_app_iff_of_iso f (Q.objObjPreimageIso Z)).1 this

private noncomputable def indexOne : index 1 ≅ 𝟭 (ℕᵒᵖ) :=
  NatIso.ofComponents (fun n ↦ eqToIso (by cases n; simp [index])) (by
    intro i j f
    exact Subsingleton.elim _ _)
private noncomputable def restrictionOne : restriction A 1 ≅ 𝟭 _ :=
  (Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ A).mapIso indexOne ≪≫
    Functor.whiskeringLeftObjIdIso
private noncomputable def complexOne : complexRestriction A 1 ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (restrictionOne A) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ℕᵒᵖ ⥤ A) (.up ℤ)
private noncomputable def derivedOne : derivedRestriction A 1 ≅ 𝟭 _ :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight (complexOne A) DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private lemma complexOne_app (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) (n : ℕ) :
    (((complexOne A).hom.app X).f i).app (op n) =
      (X.X i).map (eqToHom (by simp [index])) := by
  dsimp [complexOne, restrictionOne, indexOne, NatIso.mapHomologicalComplex]
  simp only [Category.comp_id]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] in
private lemma derivedOne_app (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (derivedOne A).hom.app (DerivedCategory.Q.obj X) =
      (restriction A 1).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((complexOne A).hom.app X) := by
  simp [derivedOne, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private lemma limitMap_one (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limitMap 1 X ≫ (limitComplex A).map ((complexOne A).hom.app X) = 𝟙 _ := by
  ext i
  apply limit.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.id_comp]
  rw [Category.assoc]
  change limit.pre (X.X i) (index 1) ≫
    (lim.map (((complexOne A).hom.app X).f i) ≫ limit.π (X.X i) n) = _
  erw [limMap_π]
  rw [← Category.assoc]
  erw [limit.pre_π]
  cases n using Opposite.rec
  rw [complexOne_app]
  exact limit.w _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma comparison_one
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))) :
    comparison A RF η 1 hRF ≫ Functor.whiskerRight (derivedOne A).hom RF ≫
      RF.rightUnitor.hom = 𝟙 RF := by
  let _ := hRF
  apply RF.rightDerived_ext η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  ext X
  dsimp
  rw [derivedOne_app, RF.map_comp]
  simp only [Category.comp_id]
  have h := congrArg (fun f ↦ f ≫
    RF.map (DerivedCategory.Q.map ((complexOne A).hom.app X)))
      (comparison_fac A RF η 1 hRF X)
  simp only [Category.assoc] at h
  rw [h]
  have hn := η.naturality ((complexOne A).hom.app X)
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  change DerivedCategory.Q.map (limitMap 1 X) ≫
    DerivedCategory.Q.map ((limitComplex A).map ((complexOne A).hom.app X)) ≫ η.app X = _
  rw [← DerivedCategory.Q.map_comp_assoc, limitMap_one]
  simp

/-- The canonical derived comparison, its cone-unit equation and its identity case.
Source: Stacks Project, Tags 0941 and 0H9K
(blueprint: lem-sp-strict-tower-arithmetic-restriction-comparison).
Construct the natural comparison by the universal property of the right derived functor.
The arithmetic index has right adjoint n ↦ n/e, so ordinary limit restriction is invertible.
Whiskering that adjunction gives an exact left adjoint to restriction, so restriction
preserves K-injectives. The comparison is therefore invertible on K-injectives, hence on
every derived object by a K-injective resolution. Precomposing the unit equation proves
the cone-unit equation. At e=1, construct the identity restriction isomorphisms explicitly;
the ordinary limit equation and uniqueness of right derived transformations give identity. -/
theorem strictTowerArithmeticRestrictionComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (η : limitComplex (ringedSiteModules.{max uC vC r} R) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
        (ComplexShape.up ℤ)))
    (_hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) :
    ∃ (ρ : ∀ (e : ℕ), 1 ≤ e →
        (RF ≅ derivedRestriction (ringedSiteModules.{max uC vC r} R) e ⋙ RF)),
      (∀ (e : ℕ) (he : 1 ≤ e) X,
        η.app X ≫ (ρ e he).hom.app (DerivedCategory.Q.obj X) ≫
            RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app X) =
          DerivedCategory.Q.map (limitMap e X) ≫
            η.app ((complexRestriction _ e).obj X)) ∧
      (∀ (e : ℕ) (he : 1 ≤ e) X (K : CochainComplex
          (ringedSiteModules.{max uC vC r} R) ℤ)
          (a : K ⟶ (limitComplex _).obj X),
        (DerivedCategory.Q.map a ≫ η.app X) ≫
            (ρ e he).hom.app (DerivedCategory.Q.obj X) ≫
            RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app X) =
          DerivedCategory.Q.map (a ≫ limitMap e X) ≫
            η.app ((complexRestriction _ e).obj X)) ∧
      (∃ (ζ : complexRestriction (ringedSiteModules.{max uC vC r} R) 1 ≅ 𝟭 _)
          (ι : derivedRestriction (ringedSiteModules.{max uC vC r} R) 1 ≅ 𝟭 _),
        (∀ X (i : ℤ) (n : ℕ),
          ((ζ.hom.app X).f i).app (op n) =
            (X.X i).map (eqToHom (by simp [index]))) ∧
        (∀ X, ι.hom.app (DerivedCategory.Q.obj X) =
          (restriction _ 1).mapDerivedCategoryFactors.hom.app X ≫
            DerivedCategory.Q.map (ζ.hom.app X)) ∧
        (∀ Z, (ρ 1 (by decide)).hom.app Z ≫ RF.map (ι.hom.app Z) = 𝟙 (RF.obj Z))) := by
  let A := ringedSiteModules.{max uC vC r} R
  have hres (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : X ⟶ I),
        I.IsKInjective ∧ QuasiIso j := by
    obtain ⟨I, j, hj, hI, _⟩ :=
      strictTowerArithmeticRestrictionResolution.{w, uC, vC, r}
        J R _hcomm RF η _hRF _hη 1 (by decide) X
    exact ⟨I, j, hI, hj⟩
  let ρ := fun e he ↦
    @asIso _ _ _ _ (comparison A RF η e _hRF)
      (comparison_isIso A RF η e he _hRF _hη hres)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro e he X
    exact comparison_fac A RF η e _hRF X
  · intro e he X K a
    simpa only [ρ, asIso_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ DerivedCategory.Q.map a ≫ f)
        (comparison_fac A RF η e _hRF X)
  · refine ⟨complexOne A, derivedOne A, complexOne_app A, derivedOne_app A, ?_⟩
    intro Z
    have h := congrArg (fun f ↦ f.app Z) (comparison_one A RF η _hRF)
    change _ ≫ _ ≫ 𝟙 _ = _ at h
    rw [Category.comp_id] at h
    exact h

end CategoryTheory.StrictTowerArithmetic
