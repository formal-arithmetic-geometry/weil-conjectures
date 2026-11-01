/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow
import all WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Compatibility of the existing finite scalar/site isomorphism proof

The canonical arrow is defined independently in FiniteCoefficientSiteScalarArrow.
This module retains the already proved ambient invertibility assertion for existing
consumers; invertibility is not data in the definition of that arrow.
Source: blueprint thm-coef-finite-hom, site descent
(blueprint: def-sf-finite-coefficient-site-scalar-arrow).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [-instance] integralOperationsSiteSmall integralReductionSiteEssentiallySmall

private instance finiteHomCompatibilitySiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] integralCoefficientRingSheafify integralCoefficientAbSheafify
  integralCoefficientAbLocallyBijective
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] finiteHomCommSheafify finiteHomAbSheafify
  finiteHomAbWeakSheafify finiteHomAbLocallyBijective finiteHomCompose
  finiteHomEncoding_equivalence finiteHomEncoding_full finiteHomEncoding_faithful

attribute [local irreducible] finiteHomEncodingRestrictionGeneral finiteHomRealizationIsoGeneral

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private def finiteHomCompatibilityEncoding (n : ℕ) :
    normalizedDVRModules.{u, u} l E X n ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  Scheme.proEtaleModuleRestriction X (Padic.coefficientExtensionRing l E (n + 1))

private instance finiteHomConcreteEncoding_additive (n : ℕ) :
    (finiteHomCompatibilityEncoding l E X n).Additive where
  map_add := by intros; ext U x; rfl

private instance finiteHomConcreteEncoding_equivalence (n : ℕ) :
    (finiteHomCompatibilityEncoding l E X n).IsEquivalence :=
  Scheme.proEtaleModuleRestriction_isEquivalence X _

private instance finiteHomConcreteEncoding_limits (n : ℕ) :
    PreservesFiniteLimits (finiteHomCompatibilityEncoding l E X n) := inferInstance

private instance finiteHomConcreteEncoding_colimits (n : ℕ) :
    PreservesFiniteColimits (finiteHomCompatibilityEncoding l E X n) := inferInstance

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedLeftWhisker
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (I : B ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : G ⋙ H ≅ I) (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryCompNatIso (F := F ⋙ G) (G := H)
      (Functor.isoWhiskerLeft F e)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F I).hom.app K =
      H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).hom.app K) ≫
        (Functor.mapDerivedCategoryCompNatIso e).hom.app (F.mapDerivedCategory.obj K) := by
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn ha
  have ht := congrArg (fun z ↦
    (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).inv.app K ≫ z ≫
      (Functor.mapDerivedCategoryCompIso G H).inv.app (F.mapDerivedCategory.obj K)) ha
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app] at ht
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  have ht' : (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).inv.app K ≫
      (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).hom.app K =
    H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).hom.app K) ≫
      (Functor.mapDerivedCategoryCompIso G H).inv.app (F.mapDerivedCategory.obj K) := by
    erw [Category.comp_id] at ht
    exact ht
  rw [hn, ← Category.assoc, ht', Category.assoc]


private theorem derivedRightWhisker
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : A ⥤ B) (U : B ⥤ C) (S : C ⥤ D) (V : A ⥤ C)
    (P : A ⥤ E) (Q : E ⥤ D)
    [F.Additive] [U.Additive] [S.Additive] [V.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (γ : F ⋙ U ≅ V) (ε : V ⋙ S ≅ P ⋙ Q) (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryCompNatIso (F := F) (G := U ⋙ S)
      (Functor.isoWhiskerRight γ S ≪≫ ε)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso P Q).hom.app K =
      (Functor.mapDerivedCategoryCompIso U S).hom.app (F.mapDerivedCategory.obj K) ≫
        S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso γ).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso ε).hom.app K := by
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight γ S) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc F U S) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn ha
  have ht := congrArg (fun z ↦
    (Functor.mapDerivedCategoryCompIso F (U ⋙ S)).inv.app K ≫ z ≫
      S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F U).inv.app K)) ha
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id] at ht
  simp only [Functor.mapDerivedCategoryCompNatIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_trans, Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht]
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc]



private theorem derivedCompatibility
    {A B C D E J : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category J]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian J]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory J]
    (F : A ⥤ B) (R : B ⥤ C) (T : C ⥤ D) (U : B ⥤ E) (S : E ⥤ D)
    (V : A ⥤ E) (P : A ⥤ J) (Q : J ⥤ C) (Q' : J ⥤ D)
    [F.Additive] [R.Additive] [T.Additive] [U.Additive] [S.Additive]
    [V.Additive] [P.Additive] [Q.Additive] [Q'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
    (α : F ⋙ R ≅ P ⋙ Q) (β : R ⋙ T ≅ U ⋙ S)
    (γ : F ⋙ U ≅ V) (δ : Q ⋙ T ≅ Q') (ε : V ⋙ S ≅ P ⋙ Q')
    (h : ∀ M, T.map (α.hom.app M) ≫ δ.hom.app (P.obj M) =
      β.hom.app (F.obj M) ≫ S.map (γ.hom.app M) ≫ ε.hom.app M)
    (K : DerivedCategory A) :
    T.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso α).hom.app K) ≫
        (Functor.mapDerivedCategoryCompNatIso δ).hom.app (P.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso β).hom.app (F.mapDerivedCategory.obj K) ≫
        S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso γ).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso ε).hom.app K := by
  have hd := Functor.mapDerivedCategoryCompNatIso_cocycle α
    (Functor.isoWhiskerLeft P δ) β (Functor.isoWhiskerRight γ S ≪≫ ε) h K
  have hl := derivedLeftWhisker P Q T Q' δ K
  have hr := derivedRightWhisker F U S V P Q' γ ε K
  have hz := congrArg (fun z ↦ z ≫ (Functor.mapDerivedCategoryCompIso P Q').hom.app K) hd
  simp only [Category.assoc] at hz
  rw [hl, hr] at hz
  simpa only [Functor.mapDerivedCategoryCompNatIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using hz


private theorem transferLeftMate
    {A B C D E F : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F]
    {L : A ⥤ B} {R : B ⥤ A} {M : C ⥤ D} {U : D ⥤ C}
    {K : E ⥤ F} {V : F ⥤ E}
    (a : L ⊣ R) (b : M ⊣ U) (c : K ⊣ V)
    (T : C ⥤ E) (S : D ⥤ F) [S.ReflectsIsomorphisms]
    {N : A ⥤ C} {P : B ⥤ D} {N' : A ⥤ E} {P' : B ⥤ F}
    (α : T ⋙ K ⟶ M ⋙ S) (hα : IsIso α)
    (β : S ⋙ V ≅ U ⋙ T) (γ : N' ≅ N ⋙ T) (δ : P' ≅ P ⋙ S)
    (τ : R ⋙ N ⟶ P ⋙ U) (τ' : R ⋙ N' ⟶ P' ⋙ V)
    (hu : ∀ X, c.unit.app (T.obj X) ≫ V.map (α.app X) ≫
      β.hom.app (M.obj X) = T.map (b.unit.app X))
    (ht : ∀ X, γ.hom.app (R.obj X) ≫ T.map (τ.app X) =
      τ'.app X ≫ V.map (δ.hom.app X) ≫ β.hom.app (P.obj X))
    (hτ' : IsIso (((mateEquiv a c).symm (TwoSquare.mk _ _ _ _ τ')).natTrans)) :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans) := by
  let _ : IsIso α := hα
  let _ := hτ'
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  have he := AlgebraicGeometry.ProEtale.left_mate_normalization a b a c
    (𝟭 _) (𝟭 _) T S (𝟙 _) α (Iso.refl _) β γ δ τ τ'
    (fun Y ↦ by simp) hu
    (fun Y ↦ by
      change N'.map (𝟙 _) ≫ γ.hom.app (R.obj Y) ≫ T.map (τ.app Y) =
        τ'.app Y ≫ V.map (δ.hom.app Y) ≫ β.hom.app (P.obj Y)
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact ht Y) X
  have hi : IsIso (K.map (γ.hom.app X) ≫ α.app (N.obj X) ≫
      S.map (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans.app X)) := by
    rw [← he]
    infer_instance
  have : IsIso (S.map
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans.app X)) :=
    (isIso_comp_left_iff _ _).1 ((isIso_comp_left_iff _ _).1 hi)
  exact isIso_of_reflects_iso _ S

private theorem leftMateUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (T : A ⥤ C) (S : B ⥤ D)
    (e : R ⋙ T ≅ S ⋙ R') (X : A) :
    b.unit.app (T.obj X) ≫ R'.map
        (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans.app X) ≫
      e.inv.app (L.obj X) = T.map (a.unit.app X) := by
  have h := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ e.hom) X
  have ht := congrArg (fun z ↦ z ≫ e.inv.app (L.obj X)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at ht
  erw [Category.comp_id] at ht
  exact ht.symm

private theorem reverseEncoding
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {A B : C} {W V Z : D}
    (a : A ≅ B) (b : T.obj B ≅ W) (c : T.obj A ≅ V) (d : V ≅ Z) (e : Z ≅ W)
    (h : T.map a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    b.inv ≫ T.map a.inv = e.inv ≫ d.inv ≫ c.inv := by
  have he : T.mapIso a ≪≫ b = c ≪≫ d ≪≫ e := Iso.ext h
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using
    congrArg Iso.inv he

private instance finiteHomDerivedEncoding_equivalence (n : ℕ) :
    (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory.IsEquivalence :=
  Functor.isEquivalence_mapDerivedCategory _

private def finiteHomNuDerivedEncoded (n : ℕ) :
    finiteHomNu l E X n ⋙ (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).mapDerivedCategory := by
  letI := finiteHomConcreteEncoding_additive l E X n
  letI := finiteHomConcreteEncoding_limits l E X n
  letI := finiteHomConcreteEncoding_colimits l E X n
  exact (Functor.mapDerivedCategoryCompIso (finiteHomNuOrdinary l E X n)
    (finiteHomCompatibilityEncoding l E X n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (F := finiteHomNuOrdinary l E X n ⋙ finiteHomCompatibilityEncoding l E X n)
        (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)
        (finiteHomNuEncoded l E X n)

private def finiteHomDerivedEncodingRestriction {n m : ℕ} (h : m ≤ n) :
    normalizedDVRRes.{u, u} l E X h ⋙ (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory ≅
      (finiteHomCompatibilityEncoding l E X m).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h) := by
  letI := finiteHomConcreteEncoding_additive l E X n
  letI := finiteHomConcreteEncoding_limits l E X n
  letI := finiteHomConcreteEncoding_colimits l E X n
  letI := finiteHomConcreteEncoding_additive l E X m
  letI := finiteHomConcreteEncoding_limits l E X m
  letI := finiteHomConcreteEncoding_colimits l E X m
  exact (Functor.mapDerivedCategoryCompIso
    (normalizedDVRModuleRes.{u, u} l E X h)
    (finiteHomCompatibilityEncoding l E X n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (F := normalizedDVRModuleRes.{u, u} l E X h ⋙ finiteHomCompatibilityEncoding l E X n)
        (G := finiteHomCompatibilityEncoding l E X m ⋙
          Sheaf.restrictScalars (ProEt.topology X) (finiteHomQuotient l E h))
        (finiteHomEncodingRestriction l E X h) ≪≫
      Functor.mapDerivedCategoryCompIso (finiteHomCompatibilityEncoding l E X m)
        (Sheaf.restrictScalars (ProEt.topology X) (finiteHomQuotient l E h))

private theorem finiteHomDerivedRestriction_encoding {n m : ℕ} (h : m ≤ n)
    (K : finiteHomEtale l E X m) :
    (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory.map
        ((finiteHomNuDerivedRestriction l E X h).hom.app K) ≫
        (finiteHomNuDerivedEncoded l E X n).hom.app
          ((Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology
            (finiteHomQuotient l E h)).obj K) =
      (finiteHomDerivedEncodingRestriction l E X h).hom.app ((finiteHomNu l E X m).obj K) ≫
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h)).map
          ((finiteHomNuDerivedEncoded l E X m).hom.app K) ≫
        (ProEtale.pbcDerivedComparisonRestrict.{u} X (finiteHomQuotient l E h)).hom.app K := by
  let := finiteHomConcreteEncoding_additive l E X n
  let := finiteHomConcreteEncoding_limits l E X n
  let := finiteHomConcreteEncoding_colimits l E X n
  let := finiteHomConcreteEncoding_additive l E X m
  let := finiteHomConcreteEncoding_limits l E X m
  let := finiteHomConcreteEncoding_colimits l E X m
  exact derivedCompatibility
    (finiteHomNuOrdinary l E X m)
    (normalizedDVRModuleRes.{u, u} l E X h)
    (finiteHomCompatibilityEncoding l E X n)
    (finiteHomCompatibilityEncoding l E X m)
    (Sheaf.restrictScalars (ProEt.topology X) (finiteHomQuotient l E h))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) X)
    (Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h))
    (finiteHomNuOrdinary l E X n)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)
    (finiteHomNuRestriction l E X h) (finiteHomEncodingRestriction l E X h)
    (finiteHomNuEncoded l E X m) (finiteHomNuEncoded l E X n)
    (finiteHomFixedRestriction X (finiteHomQuotient l E h))
    (finiteHomRestriction_encoding l E X h) K

private theorem finiteHomDerivedRestriction_inverse_encoding {n m : ℕ} (h : m ≤ n)
    (K : finiteHomEtale l E X m) :
    (finiteHomNuDerivedEncoded l E X n).inv.app
        ((Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology
          (finiteHomQuotient l E h)).obj K) ≫
      (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory.map
        ((finiteHomNuDerivedRestriction l E X h).inv.app K) =
    (ProEtale.pbcDerivedComparisonRestrict.{u} X (finiteHomQuotient l E h)).inv.app K ≫
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h)).map
        ((finiteHomNuDerivedEncoded l E X m).inv.app K) ≫
      (finiteHomDerivedEncodingRestriction l E X h).inv.app ((finiteHomNu l E X m).obj K) := by
  exact reverseEncoding (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory
    ((finiteHomNuDerivedRestriction l E X h).app K)
    ((finiteHomNuDerivedEncoded l E X n).app
      ((Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology
        (finiteHomQuotient l E h)).obj K))
    ((finiteHomDerivedEncodingRestriction l E X h).app ((finiteHomNu l E X m).obj K))
    ((Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h)).mapIso
      ((finiteHomNuDerivedEncoded l E X m).app K))
    ((ProEtale.pbcDerivedComparisonRestrict.{u} X (finiteHomQuotient l E h)).app K)
    (finiteHomDerivedRestriction_encoding l E X h K)

private theorem finiteHomEquivalenceLeftMate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} [G.IsEquivalence] [H.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (τ : R ⋙ G ≅ H ⋙ R') :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ.hom)).natTrans) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ.hom)).natTrans
  let τop : TwoSquare H.op R.op R'.op G.op :=
    TwoSquare.mk _ _ _ _ (NatTrans.op τ.hom)
  have hi := isIso_mateEquiv_of_isEquivalence a.op b.op τop
  have he : NatTrans.op α = (mateEquiv a.op b.op τop).natTrans := by
    ext X
    simp [α, τop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

private def finiteHomScalarEncodingMate {n m : ℕ} (h : m ≤ n) :
    (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory ⋙
        ProEtale.pbcFixedScalarExtension.{u} (ProEt.topology X) (finiteHomQuotient l E h) ⟶
      coefficientFiniteQuotientDerived l E X h ⋙
        (finiteHomCompatibilityEncoding l E X m).mapDerivedCategory :=
  ((mateEquiv
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h)))).symm
    (TwoSquare.mk _ _ _ _ (finiteHomDerivedEncodingRestriction l E X h).hom)).natTrans

private instance finiteHomScalarEncodingMate_isIso {n m : ℕ} (h : m ≤ n) :
    IsIso (finiteHomScalarEncodingMate l E X h) :=
  finiteHomEquivalenceLeftMate_isIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h)))
    (finiteHomDerivedEncodingRestriction l E X h)

/-- The specified beta mate is invertible on every ambient object.
Source: blueprint site-comparison paragraph
(blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: encode intrinsic module sheaves by their constant scalar action. The
canonical sheafification units identify encoded inverse image with the ordinary
fixed-ring comparison. The section normalization identifies the restriction
square with the conjugate fixed-ring square. Exact localization preserves this
identity. The mate of the encoding square is invertible because both encodings
are equivalences. Mate normalization then identifies the encoded beta, up to
invertible factors, with the proved fixed-ring comparison mate. Cancel those
factors and reflect isomorphisms through the derived encoding equivalence. -/
@[instance] theorem finiteHomSiteBeta_isIso {n m : ℕ} (h : m ≤ n) :
    IsIso (finiteHomSiteBeta l E X h) := by
  let a := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology (finiteHomQuotient l E h))
  let b := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h
  let c := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) (finiteHomQuotient l E h))
  let T := (finiteHomCompatibilityEncoding l E X n).mapDerivedCategory
  let S := (finiteHomCompatibilityEncoding l E X m).mapDerivedCategory
  let α := finiteHomScalarEncodingMate l E X h
  let β := (finiteHomDerivedEncodingRestriction l E X h).symm
  let γ := (finiteHomNuDerivedEncoded l E X n).symm
  let δ := (finiteHomNuDerivedEncoded l E X m).symm
  exact transferLeftMate a b c T S α (finiteHomScalarEncodingMate_isIso l E X h) β γ δ
    (finiteHomNuDerivedRestriction l E X h).inv
    (ProEtale.pbcDerivedComparisonRestrict.{u} X (finiteHomQuotient l E h)).inv
    (leftMateUnit b c T S (finiteHomDerivedEncodingRestriction l E X h))
    (finiteHomDerivedRestriction_inverse_encoding l E X h)
    (ProEtale.pbcComparisonReductionMap_isIso.{u} X (finiteHomQuotient l E h))

end WeilConjectures
