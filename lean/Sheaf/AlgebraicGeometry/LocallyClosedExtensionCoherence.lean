/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Normalized locally closed extensions with arbitrary pro-etale coefficients

Source: Stacks Project, proetale.tex, Tags 09AA, 09BM, 09BN and 09AH;
sites-modules.tex, Tags 03DI and 03DJ; schemes.tex, Tag 02V0;
blueprint main-20261015, det-prop-scalar-six-pullback, proof (2)
(blueprint: lem-sfb-locally-closed-extension-coherence).

The structures below package the witnesses in this single coherence assertion.
They do not choose a functor from a mere existence theorem. The only categories and
inverse/direct images used are the published module-sheaf constructions. An open
extension is specified by its adjunction, equivalently by slice extension followed
by module sheafification. Closed extensions are identified with actual direct image.
All derived functors are the exact termwise localizations of these same functors.
-/

@[expose] public noncomputable section


set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

namespace LocallyClosedExtensionData

/-- The same comparisons on unbounded derived categories, required to be the
localizations of the module comparisons on every cochain complex, not arbitrary isos.
Source: Stacks, Tags 05RU and 015F; exact-functor localization
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure DerivedCoherence (E : LocallyClosedExtensionData.{u}) where
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), E.derived a ⋙ a.pull.mapDerivedCategory ≅ 𝟭 _
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    E.derived b ⋙ E.derived a ≅ E.derived (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u}, E.derived (.identity X) ≅ 𝟭 _
  restrictionTermwise : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (K : CochainComplex (proEtaleRingModules S.scheme S.ring) ℤ),
    (restriction a).hom.app (DerivedCategory.Q.obj K) =
      a.pull.mapDerivedCategory.map ((E.extension a).mapDerivedCategoryFactors.hom.app K) ≫
        a.pull.mapDerivedCategoryFactors.hom.app
          (((E.extension a).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.restriction a) (.up ℤ)).hom.app K)
  gammaTermwise : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (K : CochainComplex (proEtaleRingModules T.scheme T.ring) ℤ),
    (gamma a b).hom.app (DerivedCategory.Q.obj K) ≫
        (E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K =
      (E.derived a).map ((E.extension b).mapDerivedCategoryFactors.hom.app K) ≫
        (E.extension a).mapDerivedCategoryFactors.hom.app
          (((E.extension b).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.gamma a b) (.up ℤ)).hom.app K)
  identityTermwise : ∀ (X : LocallyClosedCoefficients.{u})
    (K : CochainComplex (proEtaleRingModules X.scheme X.ring) ℤ),
    (identity X).hom.app (DerivedCategory.Q.obj K) =
      (E.extension (.identity X)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.identity X) (.up ℤ)).hom.app K)
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.derived a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.derived a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (M N : DerivedCategory (proEtaleRingModules S.scheme S.ring)),
    Function.Bijective (fun f : (E.derived a).obj M ⟶ (E.derived a).obj N ↦
      (restriction a).inv.app M ≫ a.pull.mapDerivedCategory.map f ≫ (restriction a).hom.app N)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      gamma a (.identity S) ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerRight (identity S) (E.derived a) ≪≫ Functor.leftUnitor (E.derived a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      gamma (.identity X) a ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerLeft (E.derived a) (identity X) ≪≫ Functor.rightUnitor (E.derived a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (gamma b d) (E.derived a) ≪≫ gamma a (b.comp d) =
        Functor.associator (E.derived d) (E.derived b) (E.derived a) ≪≫
          Functor.isoWhiskerLeft (E.derived d) (gamma a b) ≪≫ gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.derived h)


end LocallyClosedExtensionData

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_hom_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ G ≅ 𝟭 C) (M N : C) :
    Function.Bijective (fun f : F.obj M ⟶ F.obj N ↦
      r.inv.app M ≫ G.map f ≫ r.hom.app N) := by
  have hr (f : M ⟶ N) :
      r.inv.app M ≫ G.map (F.map f) ≫ r.hom.app N = f := by
    simpa using congrArg (fun g ↦ r.inv.app M ≫ g) (r.hom.naturality f)
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := F.map_surjective f
    obtain ⟨g, rfl⟩ := F.map_surjective g
    change r.inv.app M ≫ G.map (F.map f) ≫ r.hom.app N =
      r.inv.app M ≫ G.map (F.map g) ≫ r.hom.app N at h
    rw [hr, hr] at h
    exact congrArg F.map h
  · intro f
    exact ⟨F.map f, hr f⟩

private noncomputable def exactAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ)) F.mapDerivedCategory G.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_full_faithful_left
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (r : F ⋙ G ≅ 𝟭 C) :
    F.mapDerivedCategory.Full ∧ F.mapDerivedCategory.Faithful := by
  let e := Functor.mapDerivedCategoryCompNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C
  let h := (exactAdjunction adj).fullyFaithfulLOfCompIsoId e
  exact ⟨h.full, h.faithful⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_full_faithful_right
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (r : G ⋙ F ≅ 𝟭 D) :
    G.mapDerivedCategory.Full ∧ G.mapDerivedCategory.Faithful := by
  let e := Functor.mapDerivedCategoryCompNatIso r ≪≫ Functor.mapDerivedCategoryIdIso D
  let h := (exactAdjunction adj).fullyFaithfulROfCompIsoId e
  exact ⟨h.full, h.faithful⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_postcompose
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Abelian C] [Abelian D] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    {F : C ⥤ D} {G : D ⥤ B} {H H' : C ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (γ : F ⋙ G ≅ H) (e : H ≅ H') :
    Functor.mapDerivedCategoryCompNatIso (γ ≪≫ e) =
      Functor.mapDerivedCategoryCompNatIso γ ≪≫ Functor.mapDerivedCategoryNatIso e := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_eqToIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {A : Type*} (F : A → C ⥤ D) [∀ a, (F a).Additive]
    [∀ a, PreservesFiniteLimits (F a)] [∀ a, PreservesFiniteColimits (F a)]
    {a b : A} (h : a = b) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h)) =
      eqToIso (congrArg (fun x ↦ (F x).mapDerivedCategory) h) := by
  subst b
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_left_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : C ⥤ C) (F : C ⥤ D) [I.Additive] [F.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : I ≅ 𝟭 C) :
    Functor.mapDerivedCategoryCompNatIso
        (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F) =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C)
        F.mapDerivedCategory ≪≫ Functor.leftUnitor F.mapDerivedCategory := by
  apply Iso.ext
  rw [derived_postcompose]
  have hL : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, hL, Functor.comp_obj,
    Functor.id_obj, Category.comp_id,
    Functor.mapDerivedCategoryCompNatIso, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.leftUnitor_hom_app, Functor.whiskerRight_app, CategoryTheory.Functor.map_comp]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso I F).hom.app K),
    Iso.hom_inv_id_app_assoc]
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [Functor.comp_obj, Functor.id_obj] at hn hu ⊢
  rw [← Category.assoc, ← hn, Category.assoc, hu]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_right_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : D ⥤ D) (F : C ⥤ D) [I.Additive] [F.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : I ≅ 𝟭 D) :
    Functor.mapDerivedCategoryCompNatIso
        (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F) =
      Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D) ≪≫
          Functor.rightUnitor F.mapDerivedCategory := by
  apply Iso.ext
  rw [derived_postcompose]
  have hL : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, hL, Functor.comp_obj,
    Functor.id_obj, Category.comp_id,
    Functor.mapDerivedCategoryCompNatIso, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.rightUnitor_hom_app, Functor.whiskerLeft_app]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F I).hom.app K),
    Iso.hom_inv_id_app_assoc]
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [Functor.comp_obj, Functor.id_obj] at hn hu ⊢
  rw [← Category.assoc, ← hn, Category.assoc, hu]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_cocycle
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {FG : A ⥤ C} {GH : B ⥤ D} {FGH : A ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : F ⋙ G ≅ FG) (eFGH : FG ⋙ H ≅ FGH)
    (eGH : G ⋙ H ≅ GH) (eFGH' : F ⋙ GH ≅ FGH)
    (h : Functor.isoWhiskerRight eFG H ≪≫ eFGH =
      Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F eGH ≪≫ eFGH') :
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompNatIso eFG)
        H.mapDerivedCategory ≪≫ Functor.mapDerivedCategoryCompNatIso eFGH =
      Functor.associator F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompNatIso eGH) ≪≫
            Functor.mapDerivedCategoryCompNatIso eFGH' := by
  have hm (M : A) := congr_app (congrArg Iso.hom h) M
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hm
  apply Iso.ext
  ext K
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
      Functor.mapDerivedCategoryCompNatIso_cocycle eFG eFGH eGH eFGH' hm K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem identity_factors {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
  have hf := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app] at hf
  have h₁ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have h₂ : (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K = 𝟙 _ := rfl
  rw [h₁, h₂] at hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.comp_id] at hf
  have he : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  rw [he] at hf
  erw [Category.id_comp, Category.comp_id, Category.comp_id] at hf
  exact hf

namespace LocallyClosedExtensionData

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_factorization
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    ∃ (V : LocallyClosedCoefficients.{u}) (v : LocallyClosedCoefficientImmersion V X)
      (c : LocallyClosedCoefficientImmersion S V),
      IsClosedImmersion c.hom ∧ IsOpenImmersion v.hom ∧ v.comp c = a := by
  rcases a with ⟨f, hf, cf⟩
  obtain ⟨V, c, v, hc, hv, h⟩ := IsImmersion.isImmersion_iff_exists.mp hf
  subst f
  let := hc
  let := hv
  let : IsNoetherian X.scheme := ⟨⟩
  let : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  let : NoetherianSpace V :=
    v.isOpenEmbedding.isInducing.noetherianSpace
  let B : LocallyClosedCoefficients.{u} :=
    { scheme := V
      locallyNoetherian := inferInstance
      compact := inferInstance
      ring := (proEtaleSheafInverseImage v CommRingCat.{u + 1}).obj X.ring }
  let vv : LocallyClosedCoefficientImmersion B X :=
    { hom := v
      immersion := inferInstance
      coefficient := Iso.refl _ }
  let cc : LocallyClosedCoefficientImmersion S B :=
    { hom := c
      immersion := inferInstance
      coefficient := ((proEtaleRingInverseImageComp c v).app X.ring).symm ≪≫ cf }
  refine ⟨B, vv, cc, hc, hv, ?_⟩
  dsimp [LocallyClosedCoefficientImmersion.comp, vv, cc,
    proEtaleRingCompositeCoefficients]
  congr 1
  simp

private theorem module_full_faithful_open (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (ha : IsOpenImmersion a.hom) :
    (E.extension a).Full ∧ (E.extension a).Faithful := by
  let h := (E.openAdjunction a ha).fullyFaithfulLOfCompIsoId (E.restriction a)
  exact ⟨h.full, h.faithful⟩

private theorem module_full_faithful_closed (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (ha : IsClosedImmersion a.hom) :
    (E.extension a).Full ∧ (E.extension a).Faithful := by
  let adj : a.pull ⊣ E.extension a :=
    (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).ofNatIsoRight
      (E.closedComparison a ha).symm
  let h := adj.fullyFaithfulROfCompIsoId (E.restriction a)
  exact ⟨h.full, h.faithful⟩

private theorem module_full_faithful (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    (E.extension a).Full ∧ (E.extension a).Faithful := by
  obtain ⟨V, v, c, hc, hv, h⟩ := coefficient_factorization a
  obtain ⟨hvc, hvc'⟩ := module_full_faithful_open E v hv
  obtain ⟨hcc, hcc'⟩ := module_full_faithful_closed E c hc
  let := hvc
  let := hvc'
  let := hcc
  let := hcc'
  subst a
  exact ⟨Functor.Full.of_iso (E.gamma v c), Functor.Faithful.of_iso (E.gamma v c)⟩

private theorem coherent_of_normalized (E : LocallyClosedExtensionData.{u})
    (h : E.NormalizedComposition) : E.Coherent where
  full a := (module_full_faithful E a).1
  faithful a := (module_full_faithful E a).2
  homBijection a M N := by
    have := (module_full_faithful E a).1
    have := (module_full_faithful E a).2
    exact restriction_hom_bijective (E.extension a) a.pull (E.restriction a) M N
  normalized := h.normalized
  innerUnit := h.innerUnit
  outerUnit := h.outerUnit
  associative := h.associative

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_full_faithful_open (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (ha : IsOpenImmersion a.hom) : (E.derived a).Full ∧ (E.derived a).Faithful := by
  exact derived_full_faithful_left (E.openAdjunction a ha) (E.restriction a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_full_faithful_closed (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (ha : IsClosedImmersion a.hom) : (E.derived a).Full ∧ (E.derived a).Faithful := by
  exact derived_full_faithful_right
    ((proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).ofNatIsoRight
      (E.closedComparison a ha).symm) (E.restriction a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_full_faithful (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    (E.derived a).Full ∧ (E.derived a).Faithful := by
  obtain ⟨V, v, c, hc, hv, h⟩ := coefficient_factorization a
  obtain ⟨hvc, hvc'⟩ := derived_full_faithful_open E v hv
  obtain ⟨hcc, hcc'⟩ := derived_full_faithful_closed E c hc
  let := hvc
  let := hvc'
  let := hcc
  let := hcc'
  let e := Functor.mapDerivedCategoryCompNatIso (E.gamma v c)
  subst a
  exact ⟨Functor.Full.of_iso e, Functor.Faithful.of_iso e⟩

private noncomputable def derivedRestriction (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    E.derived a ⋙ a.pull.mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompNatIso (E.restriction a)) ≪≫
    Functor.mapDerivedCategoryIdIso _

private noncomputable def derivedGamma (E : LocallyClosedExtensionData.{u})
    {S X T : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (b : LocallyClosedCoefficientImmersion T S) :
    E.derived b ⋙ E.derived a ≅ E.derived (a.comp b) :=
  Functor.mapDerivedCategoryCompNatIso (E.gamma a b)

private noncomputable def derivedIdentity (E : LocallyClosedExtensionData.{u})
    (X : LocallyClosedCoefficients.{u}) : E.derived (.identity X) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (E.identity X) ≪≫ Functor.mapDerivedCategoryIdIso _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem identityTermwise (E : LocallyClosedExtensionData.{u})
    (X : LocallyClosedCoefficients.{u})
    (K : CochainComplex (proEtaleRingModules X.scheme X.ring) ℤ) :
    (E.derivedIdentity X).hom.app (DerivedCategory.Q.obj K) =
      (E.extension (.identity X)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.identity X) (.up ℤ)).hom.app K) := by
  have h := Functor.mapDerivedCategoryNatIso_fac (E.identity X) K
  change (Functor.mapDerivedCategoryNatIso (E.identity X)).hom.app _ ≫ _ = _ at h
  dsimp only [derivedIdentity, Iso.trans_hom, NatTrans.comp_app]
  rw [identity_factors]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionTermwise (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (K : CochainComplex (proEtaleRingModules S.scheme S.ring) ℤ) :
    (E.derivedRestriction a).hom.app (DerivedCategory.Q.obj K) =
      a.pull.mapDerivedCategory.map ((E.extension a).mapDerivedCategoryFactors.hom.app K) ≫
        a.pull.mapDerivedCategoryFactors.hom.app
          (((E.extension a).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.restriction a) (.up ℤ)).hom.app K) := by
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (E.restriction a) K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at h
  erw [Category.id_comp] at h
  dsimp only [derivedRestriction, Iso.trans_hom, NatTrans.comp_app]
  rw [identity_factors]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gammaTermwise (E : LocallyClosedExtensionData.{u})
    {S X T : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (b : LocallyClosedCoefficientImmersion T S)
    (K : CochainComplex (proEtaleRingModules T.scheme T.ring) ℤ) :
    (E.derivedGamma a b).hom.app (DerivedCategory.Q.obj K) ≫
        (E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K =
      (E.derived a).map ((E.extension b).mapDerivedCategoryFactors.hom.app K) ≫
        (E.extension a).mapDerivedCategoryFactors.hom.app
          (((E.extension b).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.gamma a b) (.up ℤ)).hom.app K) := by
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (E.gamma a b) K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at h
  erw [Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_inner_unit (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent)
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    ∃ h : a.comp (.identity S) = a,
      E.derivedGamma a (.identity S) ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerRight (E.derivedIdentity S) (E.derived a) ≪≫
          Functor.leftUnitor (E.derived a) := by
  obtain ⟨h, hh⟩ := hE.innerUnit a
  refine ⟨h, ?_⟩
  change Functor.mapDerivedCategoryCompNatIso (E.gamma a (.identity S)) ≪≫ _ = _
  rw [← derived_eqToIso E.extension h, ← derived_postcompose, hh]
  exact derived_left_unit _ _ (E.identity S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_outer_unit (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent)
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.derivedGamma (.identity X) a ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerLeft (E.derived a) (E.derivedIdentity X) ≪≫
          Functor.rightUnitor (E.derived a) := by
  obtain ⟨h, hh⟩ := hE.outerUnit a
  refine ⟨h, ?_⟩
  change Functor.mapDerivedCategoryCompNatIso (E.gamma (.identity X) a) ≪≫ _ = _
  rw [← derived_eqToIso E.extension h, ← derived_postcompose, hh]
  exact derived_right_unit _ _ (E.identity X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_associative (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent)
    {S X T W : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (b : LocallyClosedCoefficientImmersion T S) (d : LocallyClosedCoefficientImmersion W T) :
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.derivedGamma b d) (E.derived a) ≪≫
          E.derivedGamma a (b.comp d) =
        Functor.associator (E.derived d) (E.derived b) (E.derived a) ≪≫
          Functor.isoWhiskerLeft (E.derived d) (E.derivedGamma a b) ≪≫
            E.derivedGamma (a.comp b) d ≪≫ eqToIso (congrArg E.derived h) := by
  obtain ⟨h, hh⟩ := hE.associative a b d
  refine ⟨h, ?_⟩
  have hc := derived_cocycle (E.gamma b d) (E.gamma a (b.comp d))
    (E.gamma a b) (E.gamma (a.comp b) d ≪≫ eqToIso (congrArg E.extension h)) hh
  rw [derived_postcompose, derived_eqToIso E.extension h] at hc
  exact hc

private noncomputable def derivedCoherence (E : LocallyClosedExtensionData.{u})
    (hE : E.Coherent) : E.DerivedCoherence where
  restriction := E.derivedRestriction
  gamma := E.derivedGamma
  identity := E.derivedIdentity
  restrictionTermwise := E.restrictionTermwise
  gammaTermwise := E.gammaTermwise
  identityTermwise := E.identityTermwise
  full a := (derived_full_faithful E a).1
  faithful a := (derived_full_faithful E a).2
  homBijection a M N := by
    have := (derived_full_faithful E a).1
    have := (derived_full_faithful E a).2
    exact restriction_hom_bijective (E.derived a) a.pull.mapDerivedCategory
      (E.derivedRestriction a) M N
  innerUnit := E.derived_inner_unit hE
  outerUnit := E.derived_outer_unit hE
  associative := E.derived_associative hE

end LocallyClosedExtensionData

/-- Exact locally closed extensions, their restriction Hom bijection, and normalized
composition on modules and ordinary unbounded derived categories.

Source: Stacks, proetale.tex Tags 09AA, 09BM, 09BN and 09AH; sites-modules.tex
Tags 03DI and 03DJ; schemes.tex Tag 02V0; blueprint main-20261015,
det-prop-scalar-six-pullback proof (2)
(blueprint: lem-sfb-locally-closed-extension-coherence).

Proof: obtain the normalized module extension system from
`locallyClosedModuleExtensionCoherence`. Factor each coefficient immersion as closed then
open. The separate module adjunctions and their invertible restriction comparisons make
the two factor extensions fully faithful; the composition comparison gives this for every
immersion. Naturality identifies restriction conjugated by its comparison with the
inverse of extension on Hom sets, giving `Coherent`.

Descend the exact open and closed adjunctions termwise through homotopy and localization.
Their invertible restriction comparisons give derived full faithfulness for each factor;
factorization gives it for all immersions. Construct the derived restriction, identity and
composition comparisons with the published exact-functor descent APIs. Their termwise
formulas follow from the factorization isomorphisms. The generic left-unit, right-unit and
cocycle identities for descent transport the module laws, including the equalities of
composite coefficient immersions. These constructions give every `DerivedCoherence`
field, so the chosen module system is the required witness. -/
theorem locallyClosedExtensionCoherence :
    ∃ E : LocallyClosedExtensionData.{u}, E.Coherent ∧ Nonempty E.DerivedCoherence := by
  obtain ⟨E, hE⟩ := locallyClosedModuleExtensionCoherence.{u}
  have hC := E.coherent_of_normalized hE
  exact ⟨E, hC, ⟨E.derivedCoherence hC⟩⟩

end AlgebraicGeometry.Scheme
