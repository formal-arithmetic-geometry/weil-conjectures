/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictCoextendScalars
public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-!
# The canonical compact-support restriction comparison

Source: Stacks Tags 0GL5, 0GL6 and 0D6E; blueprint
(blueprint: lem-sf-compact-support-restriction-of-scalars).
All categories are the standard fixed-scalar presentation of modules over the constant ring.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The exact open adjunction, with the published derived pullback as right adjoint.
Source: Stacks Tag 03S2
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarOpenAdjunction (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} A]) ⊣ L((j)^*[ModuleCat.{u + 1} A]) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm

/-- Open extension and scalar restriction, normalized by the unit of the open adjunction.
It is the inverse mate of the actual restriction/pullback isomorphism.
Source: Stacks Tags 03S2 and 07A6
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        D((j)_!open[ModuleCat.{u + 1} A]) ⟶
      D((j)_!open[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ :=
  (mateEquiv (fixedScalarOpenAdjunction B j) (fixedScalarOpenAdjunction A j)).symm
    (fixedScalarRestrictionPullback φ j).inv

-- Transporting an adjunction's right adjoint does not change the normalized inverse mate.

private theorem inverse_mate_right_iso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ : E ⥤ F} {R₂ R₂' : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e₁ : R₁ ≅ R₁') (e₂ : R₂ ≅ R₂')
    (w : TwoSquare R₁ H G R₂) :
    (mateEquiv (a₁.ofNatIsoRight e₁) (a₂.ofNatIsoRight e₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.whiskerRight e₁.inv G ≫ w.natTrans ≫
        Functor.whiskerLeft H e₂.hom)) = (mateEquiv a₁ a₂).symm w := by
  apply (mateEquiv (a₁.ofNatIsoRight e₁) (a₂.ofNatIsoRight e₂)).injective
  rw [Equiv.apply_symm_apply, mateEquiv_ofNatIsoRight, Equiv.apply_symm_apply]

private noncomputable def openRestrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)^*[ModuleCat.{u + 1} B] ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙ (j)^*[ModuleCat.{u + 1} A] :=
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) _ ≪≫
    (show openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm

private theorem leftUniq_whiskerLeft
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {F G : D ⥤ E} {S : E ⥤ D} (b : F ⊣ S) (c : G ⊣ S) :
    ((a.comp b).leftAdjointUniq (a.comp c)).hom =
      Functor.whiskerLeft L (b.leftAdjointUniq c).hom := by
  apply (conjugateEquiv (a.comp c) (a.comp b)).injective
  rw [conjugateEquiv_whiskerLeft]
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv]

private theorem leftUniq_whiskerRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} {S : D ⥤ C} (b : F ⊣ S) (c : G ⊣ S)
    {L : D ⥤ E} {R : E ⥤ D} (a : L ⊣ R) :
    ((b.comp a).leftAdjointUniq (c.comp a)).hom =
      Functor.whiskerRight (b.leftAdjointUniq c).hom L := by
  apply (conjugateEquiv (c.comp a) (b.comp a)).injective
  rw [conjugateEquiv_whiskerRight]
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv]

private theorem openRestrictScalarsIso_inv_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openRestrictScalarsIso φ j).inv = (upperStarRestrictScalarsIso φ j).hom := by
  let a := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j
  let d := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology U) φ
  let b' := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let c' := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j
  have hadj : a.comp b' = c'.comp d := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change ((a.comp b').unit.app M).hom.app V = ((c'.comp d).unit.app M).hom.app V
    simp only [Adjunction.comp_unit_app]
    dsimp only [a, b', c', d]
    let siteAdj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let t := M.obj.map (siteAdj.counit.app V.unop).op
    change ((Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ).unit.app M).hom.app V ≫
        (ModuleCat.coextendScalars φ).map ((ModuleCat.restrictScalars φ).map t) =
      t ≫ ((Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology U) φ).unit.app
        ((openImmersionRestriction (ModuleCat B) j).obj M)).hom.app _
    rw [Sheaf.restrictCoextendScalarsAdj_unit_app_hom_app,
      Sheaf.restrictCoextendScalarsAdj_unit_app_hom_app]
    exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).unit.naturality t).symm
  change _ = ((a.comp b).leftAdjointUniq (c.comp d)).hom
  calc
    (openRestrictScalarsIso φ j).inv =
        ((a.comp b).leftAdjointUniq (a.comp b')).hom ≫
          ((c'.comp d).leftAdjointUniq (c.comp d)).hom := by
      have hleft := leftUniq_whiskerLeft a b b'
      have hright := leftUniq_whiskerRight c' c d
      have hcomp := congrArg₂ (fun f g ↦ f ≫ g) hleft hright
      refine Eq.trans ?_ hcomp.symm
      ext M
      simp only [openRestrictScalarsIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, upperStarIsoOpenImmersionRestriction]
      rfl
    _ = _ := by
      rw [← hadj, Adjunction.leftAdjointUniq_trans]

-- On the open slice, both coextension and restriction of scalars are sectionwise.
-- Their identity square has an identity mate by the scalar adjunction triangle.
-- A second mate is conjugation, so is invertible.

private theorem literal_open_mate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso ((mateEquiv (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)).symm
      (TwoSquare.mk (openImmersionRestriction (ModuleCat.{u + 1} B) j)
      (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (openImmersionRestriction (ModuleCat.{u + 1} A) j) (𝟙 _))).natTrans := by
  let aB := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j
  let aA := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
  let eX := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ
  let eZ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z) φ
  let d : TwoSquare _ _ _ _ := TwoSquare.mk
    (sheafCompose (Scheme.ProEt.topology Z) (ModuleCat.coextendScalars φ))
    (openImmersionRestriction (ModuleCat.{u + 1} A) j)
    (openImmersionRestriction (ModuleCat.{u + 1} B) j)
    (sheafCompose (Scheme.ProEt.topology X) (ModuleCat.coextendScalars φ)) (𝟙 _)
  have hm : ((mateEquiv eZ eX).symm d).natTrans = 𝟙 _ := by
    ext M V x
    simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.id_obj,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.id_comp]
    dsimp only [d, TwoSquare.mk, TwoSquare.natTrans, eX, eZ]
    simp only [ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
      NatTrans.id_app,
      openImmersionRestriction, localizationRestriction,
      Functor.sheafPushforwardContinuous_map_hom]
    exact congrArg (fun t ↦ t.hom x)
      ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).left_triangle_components
        (M.obj.obj ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj V)))
  have hh := iterated_mateEquiv_conjugateEquiv_symm aB aA eX eZ d
  have hm' : (mateEquiv eZ eX).symm d = TwoSquare.mk _ _ _ _ (𝟙 _) := by
    apply TwoSquare.ext
    intro M
    exact congr_app hm M
  rw [hm'] at hh
  rw [hh]
  change IsIso ((conjugateEquiv (aB.comp eZ) (eX.comp aA)).symm (𝟙 _))
  infer_instance

private noncomputable def ordinaryRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv)).natTrans

private theorem ordinaryRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (ordinaryRestrictionOpenMap φ j) := by
  have he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIso φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  let eB := (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).symm
  let eA := (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm
  have ht := inverse_mate_right_iso
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j) eB eA
    (TwoSquare.mk (openImmersionRestriction (ModuleCat.{u + 1} B) j)
      (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (openImmersionRestriction (ModuleCat.{u + 1} A) j) (𝟙 _))
  have hm : ordinaryRestrictionOpenMap φ j =
      ((mateEquiv (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)).symm
        (TwoSquare.mk (openImmersionRestriction (ModuleCat.{u + 1} B) j)
          (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ)
          (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
          (openImmersionRestriction (ModuleCat.{u + 1} A) j) (𝟙 _))).natTrans := by
    unfold ordinaryRestrictionOpenMap
    rw [← he]
    convert congrArg TwoSquare.natTrans ht using 1
    rfl
  rw [hm]
  exact literal_open_mate_isIso φ j

private theorem fixedScalarRestrictionOpenMap_eq_exact_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    fixedScalarRestrictionOpenMap φ j =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
          j).mapDerivedCategoryAdjunction
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          j).mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (upperStarRestrictScalarsIso φ j)).inv)).natTrans := by
  let eB := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
  let eA := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  have h : (fixedScalarRestrictionPullback φ j).inv =
      Functor.whiskerRight eB.inv (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso φ j)).inv ≫
        Functor.whiskerLeft (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
          eA.hom := by
    ext K
    simp only [fixedScalarRestrictionPullback, leftDerivedUpperStarRestrictScalarsIso,
      Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      eA, eB, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  unfold fixedScalarRestrictionOpenMap
  rw [h]
  exact congrArg TwoSquare.natTrans (inverse_mate_right_iso
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction eB eA _)

private theorem square_symm
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    {F : C ⥤ D} {G : D ⥤ V} {H : C ⥤ E} {J : E ⥤ V}
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [Limits.PreservesFiniteLimits J] [Limits.PreservesFiniteColimits J]
    (e : F ⋙ G ≅ H ⋙ J) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  ext M
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    NatTrans.comp_app, Category.assoc]

private theorem ordinaryRestrictionOpenMap_derived
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    [IsIso (ordinaryRestrictionOpenMap φ j)] :
    (Functor.mapDerivedCategorySquareIso (asIso (ordinaryRestrictionOpenMap φ j))).hom =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
          j).mapDerivedCategoryAdjunction
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          j).mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIso φ j).symm).hom)).natTrans := by
  apply NatTrans.ext
  funext K
  apply (((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  erw [← unit_mateEquiv_symm]
  apply Adjunction.mapDerivedCategoryAdjunction_mate
  intro M
  exact (unit_mateEquiv_symm
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv) M).symm

/-- Restriction commutes with the exact extension by zero.
Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: on sheaves both composites have the same underlying extension-by-zero groups,
restriction maps and scalar actions. The identity on these groups is an isomorphism.
Its transpose is restriction of the unit of the open adjunction, hence it is exactly
the inverse mate displayed above. The equality descends termwise because all open
functors and restriction of scalars are exact. -/
theorem fixedScalarRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (fixedScalarRestrictionOpenMap φ j) := by
  let := ordinaryRestrictionOpenMap_isIso φ j
  have h := ordinaryRestrictionOpenMap_derived φ j
  rw [square_symm, Iso.symm_hom] at h
  rw [fixedScalarRestrictionOpenMap_eq_exact_mate, ← h]
  infer_instance

/-- The canonical open comparison, with its unit normalization.
Source: Stacks Tag 0GL6 (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionOpen
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := fixedScalarRestrictionOpenMap_isIso φ j
  asIso (fixedScalarRestrictionOpenMap φ j)

/-- The specified proper/open composite, in the forward restriction direction.
Source: Stacks Tags 0GL5 and 0GL6
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def compactSupportRestrictionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        Rf_!(c)[ModuleCat.{u + 1} A] ≅
      Rf_!(c)[ModuleCat.{u + 1} B] ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fixedScalarRestrictionOpen φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (fixedScalarRestrictionDirectImage φ c.g) ≪≫
    (Functor.associator _ _ _).symm

-- Inverse mates paste: transpose using the last unit, then apply naturality
-- and the two individual unit identities.

end AlgebraicGeometry.ProEtale
