/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ModuleDerivedCompositorCoherence
public import Sheaf.Paper.DerivedDirectImageOpenCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.IdentityOpenModuleSections
import Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare

/-!
# Derived direct image over a common identity open

Source: Stacks Project, sites-cohomology.tex, Tags 0D6G and 0D6E;
blueprint main-20261015, det-sf-comp-coherence-cocycle, Refinement isomorphisms
and Independence (blueprint: lem-sfb-identity-open-derived-restriction).

The maps specialize the existing open-square mates to the identity map of the common
open. Their targets are identified using the existing module direct-image identity
comparisons. Thus all coefficient actions and all derived functors are the published
ones, on the ordinary unbounded categories, with no completion or boundedness condition.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical underived restriction, followed by the identity direct-image comparison.
Source: Stacks 0D6G and the sectionwise identity direct image
(blueprint: lem-sfb-identity-open-derived-restriction). -/
noncomputable def identityOpenRestriction {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j) :
    lowerStar Λ h ⋙ upperStar Λ j ⟶ upperStar Λ j' :=
  directImageOpenRestriction Λ (CommSq.mk (w.trans (Category.id_comp j).symm)) ≫
    Functor.whiskerLeft (upperStar Λ j') (lowerStarId Λ U).hom ≫
    (Functor.rightUnitor (upperStar Λ j')).hom

/-- The normalized derived restriction map `r_h`. It is a mate, followed by the
sectionwise-normalized derived identity comparison, rather than a chosen arbitrary map.
Source: Stacks 0D6G and 0D6E
(blueprint: lem-sfb-identity-open-derived-restriction). -/
noncomputable def identityOpenDerivedRestriction {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j) :
    (lowerStar Λ h).rightDerivedFunctor ⋙ (upperStar Λ j).mapDerivedCategory ⟶
      (upperStar Λ j').mapDerivedCategory :=
  derivedDirectImageOpenRestriction Λ (CommSq.mk (w.trans (Category.id_comp j).symm)) ≫
    Functor.whiskerLeft (upperStar Λ j').mapDerivedCategory
      (moduleDerivedIdentity Λ U).hom ≫
    (Functor.rightUnitor (upperStar Λ j').mapDerivedCategory).hom

/-- The map from `V` to its base change along `h`: identity on `V` and `j' v` on `Z'`.
Its pullback projections specify the identification under which restriction is identity.
Source: Stacks 0D6G, fibre-product computation
(blueprint: lem-sfb-identity-open-derived-restriction). -/
noncomputable def identityOpenSectionArrow {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j)
    [IsOpenImmersion j] [IsOpenImmersion j'] (V : U.ProEt) :
    (MorphismProperty.Over.map (f := j') ⊤ (inferInstance : WeaklyEtale j')).obj V ⟶
      (Scheme.proEtaleBaseChange h).obj
        ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 V.left) (V.hom ≫ j')
      ((Category.id_comp _).trans
        ((Category.assoc V.hom j' h).trans
          (congrArg (fun t : U ⟶ Z ↦ V.hom ≫ t) w)).symm))
    (pullback.lift_snd _ _ _)

private lemma kInjective_ext
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] {F G : DerivedCategory C ⥤ D}
    (a b : F ⟶ G)
    (hab : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I)) : a = b := by
  apply NatTrans.ext
  funext K
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  apply (cancel_mono (G.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, hab I]

private lemma identityOpen_underived :
    ∃ c : IdentityOpenModuleSections.Comparisons Λ,
      IdentityOpenModuleSections.UniqueNormalized Λ c ∧
      IdentityOpenModuleSections.Composition Λ c ∧
      IdentityOpenModuleSections.Identity Λ c ∧
      (∀ {V T T' : Scheme.{u}} (i : V ⟶ T) (i' : V ⟶ T')
        [IsOpenImmersion i] [IsOpenImmersion i'] (f : T' ⟶ T)
        (v : i' ≫ f = i) (hv : f ⁻¹' Set.range i = Set.range i'),
        (c i i' f v hv).hom = identityOpenRestriction Λ i i' f v) := by
  obtain ⟨_hg, _ho, c, hn, hc, hi, hm⟩ :=
    IdentityOpenModuleSections.identityOpenModuleSections_canonical Λ
  refine ⟨c, hn, hc, hi, ?_⟩
  intro V T T' i i' _ _ f v hv
  exact hm i i' f v hv

private lemma identityOpen_underived_isIso
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
    (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j') :
    IsIso (identityOpenRestriction Λ j j' h w) := by
  obtain ⟨c, _hn, _hc, _hi, hm⟩ := identityOpen_underived Λ
  rw [← hm j j' h w hw]
  infer_instance

private lemma cochainUnit_eq_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    CategoryTheory.UnboundedExactTower.cochainUnit F I =
      (F.rightDerivedFunctorObjQIso I).inv := by
  unfold CategoryTheory.UnboundedExactTower.cochainUnit
  have hh : DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = _
    exact DerivedCategory.Qh.map_id _
  conv_lhs =>
    arg 2
    arg 1
    rw [hh]
  conv_lhs =>
    arg 2
    erw [Category.id_comp]
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, asIso_hom, Category.assoc]

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  CategoryTheory.mateEquiv
  CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction

attribute [local irreducible] upperStarLowerStarAdjunction upperStarComp lowerStarComp
  lowerStarId upperStarCongr


private lemma normalized_mate
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : B ⥤ A) (F' : C ⥤ C) (g : B ⥤ C) (h : A ⥤ C)
    [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    [PreservesFiniteLimits h] [PreservesFiniteColimits h]
    (G : A ⥤ B) (G' : C ⥤ C) [G.Additive] [G'.Additive]
    (a : F ⊣ G) (a' : F' ⊣ G') (θ : g ⋙ F' ≅ F ⋙ h)
    (i : G' ≅ 𝟭 C) (d : G'.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C))
    (c : G ⋙ g ⟶ h) (r : G.rightDerivedFunctor ⋙ g.mapDerivedCategory ⟶
      h.mapDerivedCategory)
    (hc : c = (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans ≫
      Functor.whiskerLeft h i.hom ≫ (Functor.rightUnitor h).hom)
    (hr : r = (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        a'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          (UnboundedExactTower.localizedSquare F F' g h θ).hom)).natTrans ≫
        Functor.whiskerLeft h.mapDerivedCategory d.hom ≫
        (Functor.rightUnitor h.mapDerivedCategory).hom)
    (I : CochainComplex A ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective ((h.mapHomologicalComplex (.up ℤ)).obj I)]
    (hd : d.app (DerivedCategory.Q.obj ((h.mapHomologicalComplex (.up ℤ)).obj I)) =
      G'.rightDerivedFunctorObjQIso ((h.mapHomologicalComplex (.up ℤ)).obj I) ≪≫
        DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex i (.up ℤ)).app
            ((h.mapHomologicalComplex (.up ℤ)).obj I)) ≪≫
        DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app
          ((h.mapHomologicalComplex (.up ℤ)).obj I))) :
    r.app (DerivedCategory.Q.obj I) ≫ h.mapDerivedCategoryFactors.hom.app I =
    g.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso I).hom ≫
      g.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) := by
  have hd := congrArg (fun e ↦ e.hom) hd
  simp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom] at hd
  rw [hc, hr]
  have hn := UnboundedExactTower.localized_mate_cochain_normalization a a' θ I
  rw [cochainUnit_eq_inv, cochainUnit_eq_inv] at hn
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.assoc]
  erw [Category.id_comp]
  have hnatu := d.hom.naturality (h.mapDerivedCategoryFactors.hom.app I)
  dsimp only [Functor.id_map, Functor.comp_obj] at hnatu
  erw [← hnatu]
  apply (cancel_epi (g.mapDerivedCategoryFactors.inv.app _ ≫
    g.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso I).inv)).mp
  simp only [Category.assoc]
  erw [reassoc_of% hn, hd, Iso.inv_hom_id_assoc]
  conv_rhs =>
    arg 2
    rw [← g.mapDerivedCategory.map_comp_assoc]
    erw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← CategoryTheory.Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  rfl

private lemma identityOpenRestriction_mate {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j) :
    identityOpenRestriction Λ j j' h w =
      (mateEquiv (upperStarLowerStarAdjunction Λ h)
        (upperStarLowerStarAdjunction Λ (𝟙 U))
        (TwoSquare.mk _ _ _ _ (openCoherencePullbackSquare Λ
          (CommSq.mk (w.trans (Category.id_comp j).symm))).hom)).natTrans ≫
      Functor.whiskerLeft (upperStar Λ j') (lowerStarId Λ U).hom ≫
      (Functor.rightUnitor (upperStar Λ j')).hom := rfl

private lemma identityOpenDerivedRestriction_mate {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j) :
    identityOpenDerivedRestriction Λ j j' h w =
      (mateEquiv
        (upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction Λ (𝟙 U)).mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          (UnboundedExactTower.localizedSquare (upperStar Λ h) (upperStar Λ (𝟙 U))
            (upperStar Λ j) (upperStar Λ j') (openCoherencePullbackSquare Λ
              (CommSq.mk (w.trans (Category.id_comp j).symm)))).hom)).natTrans ≫
      Functor.whiskerLeft (upperStar Λ j').mapDerivedCategory (moduleDerivedIdentity Λ U).hom ≫
      (Functor.rightUnitor (upperStar Λ j').mapDerivedCategory).hom := rfl

private lemma open_complex_isKInjective {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j]
    (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj I) := by
  infer_instance

section Normalization
attribute [local irreducible] upperStar lowerStar identityOpenRestriction
  identityOpenDerivedRestriction directImageOpenRestriction derivedDirectImageOpenRestriction
  moduleDerivedIdentity

private lemma identityOpen_normalization (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') [IsOpenImmersion j']
    (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1}) (condensedRingObj Λ Z')) ℤ)
    [I.IsKInjective] :
    (identityOpenDerivedRestriction Λ j j' h w).app (DerivedCategory.Q.obj I) ≫
        (upperStar Λ j').mapDerivedCategoryFactors.hom.app I =
      (upperStar Λ j).mapDerivedCategory.map
          ((lowerStar Λ h).rightDerivedFunctorObjQIso I).hom ≫
        (upperStar Λ j).mapDerivedCategoryFactors.hom.app
          (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (identityOpenRestriction Λ j j' h w) (.up ℤ)).app I) := by
  let J : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ :=
    ((upperStar Λ j').mapHomologicalComplex (.up ℤ)).obj I
  have hJ : J.IsKInjective := open_complex_isKInjective Λ j' I
  let sq := CommSq.mk (w.trans (Category.id_comp j).symm)
  exact @normalized_mate
    (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1}) (condensedRingObj Λ Z'))
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    Mod.instCategory Mod.instCategory Mod.instCategory
    (Mod.instAbelian (condensedRingObj Λ Z'))
    (Mod.instAbelian (condensedRingObj Λ Z))
    (Mod.instAbelian (condensedRingObj Λ U))
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    inferInstance inferInstance
    (upperStar Λ h) (upperStar Λ (𝟙 U)) (upperStar Λ j) (upperStar Λ j')
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (lowerStar Λ h) (lowerStar Λ (𝟙 U)) inferInstance inferInstance
    (upperStarLowerStarAdjunction Λ h) (upperStarLowerStarAdjunction Λ (𝟙 U))
    (openCoherencePullbackSquare Λ sq) (lowerStarId Λ U) (moduleDerivedIdentity Λ U)
    (identityOpenRestriction Λ j j' h w) (identityOpenDerivedRestriction Λ j j' h w)
    (identityOpenRestriction_mate Λ j j' h w)
    (identityOpenDerivedRestriction_mate Λ j j' h w)
    I inferInstance hJ (module_derived_identity_normalization Λ ℓ hΛ U J)




end Normalization

attribute [local irreducible] identityOpenRestriction identityOpenDerivedRestriction

/-- The canonical restriction is invertible, is sectionwise the identity under
`V ×_Z Z' ≅ V`, and is represented by the termwise restriction on every K-injective.
Source: Stacks 0D6G, 079P, 070I and 08BJ
(blueprint: lem-sfb-identity-open-derived-restriction).

Proof plan (steps 1--4 of the node): identify open pullback with slice restriction using
lem-weil-proetale-weakly-etale-localization and lem-sfb-coefficient-sections-localization.
The coefficient comparison is invertible for every commutative condensed ring; module
pullback is exact by det-prop-sfb-module-pullback-exact-main. The inverse-image condition
identifies V ×_Z Z' with V, with inverse (1_V,j'v). Evaluation of the canonical mate gives
the displayed section formula, linear for the pulled-back coefficient actions. Transport
through lem-sfb-internal-module-operations-transport. Take K-injective resolutions by
prop-pur-kinjective-resolutions-exist and compute the ordinary total direct image by
sk-def-sfb-module-derived-pushpull. The termwise comparison localizes to the displayed
formula. The K-injective Hom bijection of lem-weil-pbc-kinjective-hom-derived proves
independence and naturality. Exact module inverse image and its adjunction also give
preservation of K-injectives by direct image (lem-weil-pbc-right-adjoint-preserves-kinjective).
-/
theorem identity_open_derived_restriction (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (hw : h ⁻¹' Set.range j = Set.range j') :
    IsIso (identityOpenDerivedRestriction Λ j j' h w) ∧
    IsIso (identityOpenRestriction Λ j j' h w) ∧
    (∀ V : U.ProEt, IsIso (identityOpenSectionArrow j j' h w V)) ∧
    (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z') AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z')) (V : U.ProEt)
      (s : M.X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj
        ((MorphismProperty.Over.map (f := j) ⊤
          (inferInstance : WeaklyEtale j)).obj V)))),
      ((identityOpenRestriction Λ j j' h w).app M).hom.hom.app (op V)
          (openCoherenceSectionCoprojection Λ j ((lowerStar Λ h).obj M) V s) =
        openCoherenceSectionCoprojection Λ j' M V
          (M.X.obj.map (identityOpenSectionArrow j j' h w V).op s)) ∧
    (∀ (I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Z') AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z')) ℤ) [I.IsKInjective],
      (identityOpenDerivedRestriction Λ j j' h w).app (DerivedCategory.Q.obj I) ≫
          (upperStar Λ j').mapDerivedCategoryFactors.hom.app I =
        (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ h).rightDerivedFunctorObjQIso I).hom ≫
          (upperStar Λ j).mapDerivedCategoryFactors.hom.app
            (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (identityOpenRestriction Λ j j' h w) (.up ℤ)).app I)) := by
  have hu := identityOpen_underived_isIso Λ j j' h w hw
  have hn := identityOpen_normalization Λ ℓ hΛ j j' h w
  have hd : IsIso (identityOpenDerivedRestriction Λ j j' h w) := by
    have hall : ∀ K, IsIso ((identityOpenDerivedRestriction Λ j j' h w).app K) := by
      intro K
      obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
      rw [NatTrans.isIso_app_iff_of_iso _ e]
      have hf : IsIso
          ((identityOpenDerivedRestriction Λ j j' h w).app (DerivedCategory.Q.obj I) ≫
            (upperStar Λ j').mapDerivedCategoryFactors.hom.app I) := by
        rw [hn I]
        have : IsIso ((NatTrans.mapHomologicalComplex
            (identityOpenRestriction Λ j j' h w) (.up ℤ)).app I) :=
          ((NatIso.mapHomologicalComplex
            (asIso (identityOpenRestriction Λ j j' h w)) (.up ℤ)).app I).isIso_hom
        infer_instance
      exact IsIso.of_isIso_comp_right _ ((upperStar Λ j').mapDerivedCategoryFactors.hom.app I)
    exact NatIso.isIso_of_isIso_app _
  obtain ⟨hg, _ho, _c, _hc, _hcomp, _hid, _hm⟩ :=
    IdentityOpenModuleSections.identityOpenModuleSections_canonical Λ
  obtain ⟨c, hc, _hcomp, _hid, hm⟩ := identityOpen_underived Λ
  refine ⟨hd, hu, ?_, ?_, hn⟩
  · intro V
    obtain ⟨e, he, _ht⟩ := hg j j' h w hw
    let i :
        (MorphismProperty.Over.map (f := j') ⊤ (inferInstance : WeaklyEtale j')).obj V ≅
          (Scheme.proEtaleBaseChange h).obj
            ((MorphismProperty.Over.map (f := j) ⊤
              (inferInstance : WeaklyEtale j)).obj V) :=
      MorphismProperty.Over.isoMk (e V).symm (he V).2.2
    have hi : i.hom = identityOpenSectionArrow j j' h w V := by
      apply MorphismProperty.Over.Hom.ext
      change (e V).inv = pullback.lift _ _ _
      apply pullback.hom_ext
      · simpa only [pullback.lift_fst] using (he V).2.1
      · simpa only [pullback.lift_snd] using (he V).2.2
    rw [← hi]
    infer_instance
  · intro M V s
    have ht := (hc j j' h w hw).1 M V s
    have he := hm j j' h w hw
    rw [← he]
    dsimp only [ModuleOpenPasting.coprojection, openCoherenceSectionCoprojection] at ht ⊢
    convert ht using 1
    rfl

attribute [local implicit_reducible] Functor.mapHomologicalComplex

private lemma restriction_cochain_composition
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    (E₀ : C ⥤ D) (E₁ : B ⥤ D) (E₂ : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    (d : F ⋙ G ≅ H) (c : G ⋙ E₀ ⟶ E₁) (c' : F ⋙ E₁ ⟶ E₂)
    (b : H ⋙ E₀ ⟶ E₂)
    (hb : b = Functor.whiskerRight d.inv E₀ ≫ (Functor.associator F G E₀).hom ≫
      Functor.whiskerLeft F c ≫ c') (I : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex b (.up ℤ)).app I =
      (E₀.mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso d (.up ℤ)).inv.app I) ≫
        (NatTrans.mapHomologicalComplex c (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex c' (.up ℤ)).app I := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f]
  dsimp only [Functor.mapHomologicalComplex]
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.map_id, Category.id_comp, Category.assoc]
    using congr_app hb (I.X n)
private lemma normalized_restriction_comp
    {A₀ A₁ A₂ B : Type*} [Category A₀] [Category A₁] [Category A₂] [Category B]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁]
    [HasDerivedCategory A₂] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A₁] [Abelian.HasKInjectiveResolutions A₂]
    (H : A₁ ⥤ A₀) (J : A₂ ⥤ A₁) (P : A₂ ⥤ A₀)
    [H.Additive] [J.Additive] [P.Additive] [J.PreservesKInjectiveComplexes]
    (E₀ : A₀ ⥤ B) (E₁ : A₁ ⥤ B) (E₂ : A₂ ⥤ B)
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
    (d : J ⋙ H ≅ P) (c : H ⋙ E₀ ⟶ E₁) (c' : J ⋙ E₁ ⟶ E₂)
    (b : P ⋙ E₀ ⟶ E₂)
    (r : H.rightDerivedFunctor ⋙ E₀.mapDerivedCategory ⟶ E₁.mapDerivedCategory)
    (r' : J.rightDerivedFunctor ⋙ E₁.mapDerivedCategory ⟶ E₂.mapDerivedCategory)
    (t : P.rightDerivedFunctor ⋙ E₀.mapDerivedCategory ⟶ E₂.mapDerivedCategory)
    (κ : P.rightDerivedFunctor ≅ J.rightDerivedFunctor ⋙ H.rightDerivedFunctor)
    (hb : b = Functor.whiskerRight d.inv E₀ ≫ (Functor.associator J H E₀).hom ≫
      Functor.whiskerLeft J c ≫ c')
    (hr : ∀ (I : CochainComplex A₁ ℤ) [I.IsKInjective],
      r.app (DerivedCategory.Q.obj I) ≫ E₁.mapDerivedCategoryFactors.hom.app I =
        E₀.mapDerivedCategory.map (H.rightDerivedFunctorObjQIso I).hom ≫
          E₀.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I))
    (hr' : ∀ (I : CochainComplex A₂ ℤ) [I.IsKInjective],
      r'.app (DerivedCategory.Q.obj I) ≫ E₂.mapDerivedCategoryFactors.hom.app I =
        E₁.mapDerivedCategory.map (J.rightDerivedFunctorObjQIso I).hom ≫
          E₁.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c' (.up ℤ)).app I))
    (ht : ∀ (I : CochainComplex A₂ ℤ) [I.IsKInjective],
      t.app (DerivedCategory.Q.obj I) ≫ E₂.mapDerivedCategoryFactors.hom.app I =
        E₀.mapDerivedCategory.map (P.rightDerivedFunctorObjQIso I).hom ≫
          E₀.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app I))
    (hκ : ∀ (I : CochainComplex A₂ ℤ) [I.IsKInjective],
      κ.hom.app (DerivedCategory.Q.obj I) ≫
          H.rightDerivedFunctor.map (J.rightDerivedFunctorObjQIso I).hom ≫
          (H.rightDerivedFunctorObjQIso ((J.mapHomologicalComplex (.up ℤ)).obj I)).hom =
        (P.rightDerivedFunctorObjQIso I).hom ≫ DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso d (.up ℤ)).inv.app I)) :
    t = Functor.whiskerRight κ.hom E₀.mapDerivedCategory ≫
      (Functor.associator J.rightDerivedFunctor H.rightDerivedFunctor
        E₀.mapDerivedCategory).hom ≫ Functor.whiskerLeft J.rightDerivedFunctor r ≫ r' := by
  apply kInjective_ext
  intro I hI
  let K : CochainComplex A₁ ℤ := (J.mapHomologicalComplex (.up ℤ)).obj I
  have hK : K.IsKInjective := inferInstance
  apply (cancel_mono (E₂.mapDerivedCategoryFactors.hom.app I)).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.assoc, Category.id_comp]
  rw [ht I, hr' I]
  have hn := r.naturality (J.rightDerivedFunctorObjQIso I).hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% hr K]
  simp only [← E₀.mapDerivedCategory.map_comp_assoc]
  rw [hκ I]
  simp only [Functor.map_comp, Category.assoc]
  erw [E₀.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← Functor.map_comp]
  congr 2
  congr 1
  exact restriction_cochain_composition J H P E₀ E₁ E₂ d c c' b hb I

section Composition

attribute [local irreducible] upperStar lowerStar moduleDerivedCompositor
  moduleDerivedIteratedObjIso

/-- Transitivity of the common-open comparison, with the specified derived compositor.
Source: Stacks 0D6G and 0D6E; blueprint Refinement isomorphisms and Independence
(blueprint: lem-sfb-identity-open-derived-restriction).

Proof plan (steps 4--5): take a K-injective I on Z''. The exact-left-adjoint criterion
lem-weil-pbc-right-adjoint-preserves-kinjective makes k_*I K-injective. Thus all three
comparisons are computed on I, k_*I and h_*k_*I with no extra replacement. By
lem-sfb-module-derived-compositor-coherence the compositor is the inverse of the termwise
module compositor. The associator of fibre products identifies the successive inverses
(1_V,j'v) and (1_V,j''v) with (1_V,j''v) for hk: both projections agree. Hence the maps
of complexes agree sectionwise, with the same module actions. Localize and use the
representative formula above; naturality gives the displayed equality of transformations.
-/
theorem identity_open_derived_restriction_comp (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' Z'' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (j'' : U ⟶ Z'')
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion j'] [QuasiCompact j']
    [IsOpenImmersion j'']
    (h : Z' ⟶ Z) (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j')
    (k : Z'' ⟶ Z') (w' : j'' ≫ k = j') (hw' : k ⁻¹' Set.range j' = Set.range j'') :
    identityOpenDerivedRestriction Λ j j'' (k ≫ h)
        ((Category.assoc j'' k h).symm.trans
          ((congrArg (fun t : U ⟶ Z' ↦ t ≫ h) w').trans w)) =
      Functor.whiskerRight (moduleDerivedCompositor Λ k h).hom
          (upperStar Λ j).mapDerivedCategory ≫
        (Functor.associator (lowerStar Λ k).rightDerivedFunctor
          (lowerStar Λ h).rightDerivedFunctor (upperStar Λ j).mapDerivedCategory).hom ≫
        Functor.whiskerLeft (lowerStar Λ k).rightDerivedFunctor
          (identityOpenDerivedRestriction Λ j j' h w) ≫
        identityOpenDerivedRestriction Λ j' j'' k w' := by
  obtain ⟨c, _hn, hc, _hi, hm⟩ := identityOpen_underived Λ
  have hu := hc j j' j'' h w hw k w' hw'
  simp only [hm] at hu
  let := (upperStarLowerStarAdjunction Λ k).preservesKInjectiveComplexes
  apply normalized_restriction_comp (lowerStar Λ h) (lowerStar Λ k)
    (lowerStar Λ (k ≫ h)) (upperStar Λ j) (upperStar Λ j') (upperStar Λ j'')
    (lowerStarComp Λ k h) (identityOpenRestriction Λ j j' h w)
    (identityOpenRestriction Λ j' j'' k w') _ _ _ _ (moduleDerivedCompositor Λ k h) hu
    (identityOpen_normalization Λ ℓ hΛ j j' h w)
    (identityOpen_normalization Λ ℓ hΛ j' j'' k w')
    (identityOpen_normalization Λ ℓ hΛ j j'' (k ≫ h) _)
  intro I hI
  have hd := congrArg (fun e ↦ e.hom)
    (module_derived_compositor_normalization Λ ℓ hΛ k h I)
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    moduleDerivedIteratedObjIso, Category.assoc] using hd

end Composition

/-- Identity normalization of the common-open comparison.
Source: Stacks 0D6G and 0D6E
(blueprint: lem-sfb-identity-open-derived-restriction).

Proof plan (step 6): for h = 1_Z the inverse (1_V,jv) is the ordinary identity
base-change identification. The section formula is therefore the sectionwise identity
after lowerStarId. The theorem module_derived_identity_normalization of
lem-sfb-module-derived-compositor-coherence identifies its localization with the
canonical derived identity comparison. Apply the representative formula on every
K-injective and then the K-injective Hom bijection to obtain this natural equality.
No properness, density or field hypothesis enters any step. -/
theorem identity_open_derived_restriction_id (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j] :
    identityOpenDerivedRestriction Λ j j (𝟙 Z) (Category.comp_id j) =
      Functor.whiskerRight (moduleDerivedIdentity Λ Z).hom
          (upperStar Λ j).mapDerivedCategory ≫
        (Functor.leftUnitor (upperStar Λ j).mapDerivedCategory).hom := by
  obtain ⟨c, _hn, _hc, hi, hm⟩ :=
    identityOpen_underived Λ
  have hu := hi j
  rw [hm] at hu
  apply kInjective_ext
  intro I hI
  apply (cancel_mono ((upperStar Λ j).mapDerivedCategoryFactors.hom.app I)).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.assoc]
  rw [identityOpen_normalization Λ ℓ hΛ j j (𝟙 Z)]
  have hid := congrArg (fun e ↦ e.hom)
    (module_derived_identity_normalization Λ ℓ hΛ Z I)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hid
  rw [hid]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [Category.id_comp]
  have hf := (upperStar Λ j).mapDerivedCategoryFactors_hom_naturality
    (((NatIso.mapHomologicalComplex (lowerStarId Λ Z) (.up ℤ)).hom.app I) ≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app I)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hf
  erw [hf]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 2
  congr 1
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.leftUnitor_hom_app, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc]
  convert congr_app hu (I.X n) using 1
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.leftUnitor_hom_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  exact congrArg (fun t ↦ (upperStar Λ j).map ((lowerStarId Λ Z).hom.app (I.X n)) ≫ t)
    ((upperStar Λ j).map_id (I.X n))

end AlgebraicGeometry.ProEtale.CondensedRing
