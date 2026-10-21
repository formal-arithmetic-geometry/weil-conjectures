/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NH and Q8
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import all Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage

/-!
# Coefficient cocycle of the normalized pro-etale derived direct image

Source: Stacks Project, derived.tex, Tag 070Y (`lemma-K-injective-defined`), and the
agent-written coefficient-composition argument in the DAG
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

The comparisons are the specified `fixedScalarRestrictionDirectImage` isomorphisms.
The restriction associators are the existing sectionwise identity isomorphisms localized
termwise as `Sheaf.derivedRestrictScalarsCompIso`. All derived categories are unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

-- The coefficient-chain calculation uses only exact localization and adjunctions.
/-- Mates preserve a pasted coefficient square: transpose along the final adjunction and use
its counit, naturality, and the two individual mate identities.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem mate_chain
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {Q : B ⥤ A} (adj : Q ⊣ P)
    {P' : C ⥤ D} {Q' : D ⥤ C} (adj' : Q' ⊣ P')
    {P'' : E ⥤ F} {Q'' : F ⥤ E} (adj'' : Q'' ⊣ P'')
    {S : B ⥤ D} {S' : A ⥤ C} {T : D ⥤ F} {T' : C ⥤ E}
    {U : B ⥤ F} {U' : A ⥤ E}
    (α : S ⋙ Q' ⟶ Q ⋙ S') (β : T ⋙ Q'' ⟶ Q' ⋙ T')
    (γ : U ⋙ Q'' ⟶ Q ⋙ U') (c : S ⋙ T ≅ U) (c' : S' ⋙ T' ≅ U')
    (hγ : ∀ M : B, γ.app M = Q''.map (c.inv.app M) ≫ β.app (S.obj M) ≫
      T'.map (α.app M) ≫ c'.hom.app (Q.obj M)) (K : A) :
    (mateEquiv adj adj'' (TwoSquare.mk _ _ _ _ γ)).natTrans.app K =
      c.inv.app (P.obj K) ≫ T.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α)).natTrans.app K) ≫
        (mateEquiv adj' adj'' (TwoSquare.mk _ _ _ _ β)).natTrans.app (S'.obj K) ≫
        P''.map (c'.hom.app K) := by
  apply (adj''.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [adj''.counit_naturality]
  rw [mateEquiv_counit]
  rw [reassoc_of% (mateEquiv_counit adj' adj'' (TwoSquare.mk _ _ _ _ β) (S'.obj K)), hγ]
  simp only [Category.assoc]
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  erw [β.naturality_assoc]
  simp only [Functor.comp_map]
  slice_rhs 3 4 => rw [← T'.map_comp, mateEquiv_counit, T'.map_comp]
  simp only [Category.assoc]
  rw [← c'.hom.naturality]
  rfl

/-- Exact localization preserves coefficient pasting. Apply the square-composition API to
the inverse squares and cancel the comparison isomorphisms.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem derive_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type (u + 1)}
    [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂]
    [Category.{u} B₀] [Category.{u} B₁] [Category.{u} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{u} A₀] [HasDerivedCategory.{u} A₁] [HasDerivedCategory.{u} A₂]
    [HasDerivedCategory.{u} B₀] [HasDerivedCategory.{u} B₁] [HasDerivedCategory.{u} B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    [R₁₀.Additive] [R₂₁.Additive] [R₂₀.Additive]
    [U₁₀.Additive] [U₂₁.Additive] [U₂₀.Additive]
    [Q₀.Additive] [Q₁.Additive] [Q₂.Additive]
    [PreservesFiniteLimits R₁₀] [PreservesFiniteColimits R₁₀]
    [PreservesFiniteLimits R₂₁] [PreservesFiniteColimits R₂₁]
    [PreservesFiniteLimits R₂₀] [PreservesFiniteColimits R₂₀]
    [PreservesFiniteLimits U₁₀] [PreservesFiniteColimits U₁₀]
    [PreservesFiniteLimits U₂₁] [PreservesFiniteColimits U₂₁]
    [PreservesFiniteLimits U₂₀] [PreservesFiniteColimits U₂₀]
    [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
    [PreservesFiniteLimits Q₁] [PreservesFiniteColimits Q₁]
    [PreservesFiniteLimits Q₂] [PreservesFiniteColimits Q₂]
    (e₀₁ : R₁₀ ⋙ Q₀ ≅ Q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ Q₁ ≅ Q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ Q₀ ≅ Q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = Q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (Q₂.obj M))
    (M : DerivedCategory A₂) :
    (Functor.mapDerivedCategorySquareIso e₀₂).hom.app M =
      Q₀.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso R₂₁ R₁₀).symm ≪≫
          Functor.mapDerivedCategoryNatIso r).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso e₀₁).hom.app (R₂₁.mapDerivedCategory.obj M) ≫
      U₁₀.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso e₁₂).hom.app M) ≫
      ((Functor.mapDerivedCategoryCompIso U₂₁ U₁₀).symm ≪≫
        Functor.mapDerivedCategoryNatIso t).hom.app (Q₂.mapDerivedCategory.obj M) := by
  have hi (N : A₂) : e₀₂.inv.app N ≫ Q₀.map (r.inv.app N) =
      t.inv.app (Q₂.obj N) ≫ U₁₀.map (e₁₂.inv.app N) ≫ e₀₁.inv.app (R₂₁.obj N) := by
    let z := Q₀.mapIso (r.symm.app N) ≪≫ e₀₁.app (R₂₁.obj N) ≪≫
      U₁₀.mapIso (e₁₂.app N) ≪≫ t.app (Q₂.obj N)
    have hz : e₀₂.app N = z := Iso.ext (he N)
    have hh := congrArg Iso.inv hz
    dsimp only [z, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at hh
    rw [hh]
    simp only [Category.assoc, ← Q₀.map_comp, Iso.hom_inv_id_app, Q₀.map_id,
      Category.comp_id]
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    e₁₂.symm e₀₁.symm e₀₂.symm t.symm r.symm hi M
  apply (cancel_epi ((Functor.mapDerivedCategorySquareIso e₀₂).inv.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Category.assoc, Iso.symm_inv] at h ⊢
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rfl

/-- Transport coefficient pasting along three natural isomorphisms. Naturality moves
the source associator past the first comparison; the intermediate inverses cancel.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem transport_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    {Q₀ q₀ : A₀ ⥤ B₀} {Q₁ q₁ : A₁ ⥤ B₁} {Q₂ q₂ : A₂ ⥤ B₂}
    (a₀ : Q₀ ≅ q₀) (a₁ : Q₁ ≅ q₁) (a₂ : Q₂ ≅ q₂)
    (e₀₁ : R₁₀ ⋙ q₀ ≅ q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ q₁ ≅ q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ q₀ ≅ q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (q₂.obj M))
    (M : A₂) :
    (Functor.isoWhiskerLeft R₂₀ a₀ ≪≫ e₀₂ ≪≫
      Functor.isoWhiskerRight a₂.symm U₂₀).hom.app M = Q₀.map (r.inv.app M) ≫
    (Functor.isoWhiskerLeft R₁₀ a₀ ≪≫ e₀₁ ≪≫
      Functor.isoWhiskerRight a₁.symm U₁₀).hom.app (R₂₁.obj M) ≫
    U₁₀.map ((Functor.isoWhiskerLeft R₂₁ a₁ ≪≫ e₁₂ ≪≫
      Functor.isoWhiskerRight a₂.symm U₂₁).hom.app M) ≫ t.hom.app (Q₂.obj M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (a₀.hom.naturality (r.inv.app M)), he]
  slice_rhs 4 5 => rw [← U₁₀.map_comp, Iso.inv_hom_id_app, U₁₀.map_id]
  simp only [Category.assoc]
  rw [← t.hom.naturality]
  simp only [Functor.comp_map]
  erw [Category.id_comp]

namespace AlgebraicGeometry.ProEtale

/-- The ordinary pullback/scalar comparison satisfies the adjunction unit identity,
since its supplied ordinary mate is the identity on direct images.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem e_unit {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).map ((upperStarRestrictScalarsIso φ f).hom.app M) =
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app M) := by
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom) M
  have hm := restriction_underived_mate φ f
  dsimp only [TwoSquare.natTrans] at hm
  rw [hm] at h
  simpa using h.symm

/-- Ordinary scalar-pullback comparisons compose. Transpose along the pullback
adjunction, use the unit identity twice, and compare sectionwise identity associators.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem e_chain {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C)) :
    (upperStarRestrictScalarsIso (ψ.comp φ) f).hom.app M =
      (upperStar (ModuleCat.{u + 1} A) f).map
        ((Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl).inv.app M) ≫
      (upperStarRestrictScalarsIso φ f).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
        ((upperStarRestrictScalarsIso ψ f).hom.app M) ≫
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl).hom.app
        ((upperStar (ModuleCat.{u + 1} C) f).obj M) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [e_unit]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.naturality_assoc]
  erw [reassoc_of% (e_unit φ f ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M))]
  change _ = _ ≫ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M)) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
      ((lowerStar (ModuleCat.{u + 1} B) f).map
        ((upperStarRestrictScalarsIso ψ f).hom.app M)) ≫ _
  rw [← Functor.map_comp_assoc, e_unit]
  ext U x
  rfl

/-- Localize the ordinary coefficient chain termwise and transport to the specified
derived pullbacks; no preservation of K-injectives is used.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem scalarRestriction_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C))) :
    (leftDerivedUpperStarRestrictScalarsIso.{u} (ψ.comp φ) f).hom.app M =
      ((Functor.leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
        (upperStar.{u + 2, u} (ModuleCat.{u + 1} A) f))).map
        ((Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology X) rfl
          (f := φ) (g := ψ)).inv.app M) ≫
      (leftDerivedUpperStarRestrictScalarsIso.{u} φ f).hom.app
        ((Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) ψ).obj M) ≫
      (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ).map
        ((leftDerivedUpperStarRestrictScalarsIso.{u} ψ f).hom.app M) ≫
      (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology T) rfl
        (f := φ) (g := ψ)).hom.app (((Functor.leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1,
          u + 1}
        (upperStar.{u + 2, u} (ModuleCat.{u + 1} C) f))).obj M) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact @transport_chain.{u + 2, u + 2, u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} C)))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) ψ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) (ψ.comp φ))
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) ψ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) (ψ.comp φ))
    _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} C) f)
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso φ f))
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso ψ f))
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso (ψ.comp
        φ) f))
    (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology X) rfl)
    (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology T) rfl)
    (derive_chain.{u + 1}
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) (ψ.comp φ))
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) ψ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) (ψ.comp φ))
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} A) f)
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} B) f)
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} C) f)
      (upperStarRestrictScalarsIso φ f) (upperStarRestrictScalarsIso ψ f)
      (upperStarRestrictScalarsIso (ψ.comp φ) f)
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl)
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl)
      (e_chain φ ψ f)) M

/-- The inverse-resolution-map normalization determines the direct-image comparison uniquely.
Source: Stacks Tag 070Y and step 2 of the coefficient cocycle argument
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

The hypothesis is exactly the normalization of the recorded comparison theorem, with
all canonical evaluation identifications displayed. Since the localized direct image
of j is invertible, this equation says the evaluated component is its inverse.

Proof: step 1 uses the small pro-etale site and the ordinary direct image of
`def-weil-pbc-proetale-operations`. Grothendieck abelianness gives K-injective resolutions
by `prop-pur-kinjective-resolutions-exist`. For a K-injective H choose a resolution of
its scalar restriction. The hypothesis and
`lem-weil-proetale-direct-image-restriction-of-scalars` identify both evaluated
components with the inverse of the same localized direct-image resolution map.
Cancel the evaluation isomorphisms. For an arbitrary derived object L, represent it
by a complex and choose a K-injective resolution, giving an isomorphism L -> QH by
`def-weil-abstract-derived-category`. Naturality of both comparisons along this
isomorphism and cancellation give equality at L; extensionality gives equality of
natural isomorphisms. No restriction functor is assumed to preserve K-injectives. -/
theorem fixedScalarRestrictionDirectImage_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (γ : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) ≅
      R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    (hγ : ∀
      (H : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ)
      [H.IsKInjective]
      (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
      [I.IsKInjective]
      (j : ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
        (.up ℤ)).obj H ⟶ I) [QuasiIso j],
      QuasiIso (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) ∧
        γ.hom.app (_root_.DerivedCategory.Q.obj H) ≫
            (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
              ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso H).hom ≫
            (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
              (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj H) ≫
            _root_.DerivedCategory.Q.map
              (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) =
          (R((f)_*[ModuleCat.{u + 1} A])).map
              ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
                H) ≫
            (R((f)_*[ModuleCat.{u + 1} A])).map (_root_.DerivedCategory.Q.map j) ≫
            ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorObjQIso I).hom) :
    γ = fixedScalarRestrictionDirectImage φ f := by
  have hH (H : CochainComplex
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) [H.IsKInjective] :
      γ.hom.app (_root_.DerivedCategory.Q.obj H) =
        (fixedScalarRestrictionDirectImage φ f).hom.app (_root_.DerivedCategory.Q.obj H) := by
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
        (.up ℤ)).obj H)
    have : I.IsKInjective := hI
    have : QuasiIso j := hj
    obtain ⟨hq, hβ⟩ := fixedScalarRestrictionDirectImage_kInjective φ f H I j
    have : QuasiIso
        (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) := hq
    have h := (hγ H I j).2.trans hβ.symm
    apply (cancel_mono ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
      ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso H).hom)).1
    apply (cancel_mono
      ((Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
        (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj H))).1
    apply (cancel_mono (_root_.DerivedCategory.Q.map
      (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j))).1
    simpa only [Category.assoc] using h
  apply Iso.ext
  apply NatTrans.ext
  funext L
  obtain ⟨H, hHinj, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isKInjective L
  have : H.IsKInjective := hHinj
  apply (cancel_mono ((R((f)_*[ModuleCat.{u + 1} B]) ⋙
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map e.hom)).1
  rw [← γ.hom.naturality, ← (fixedScalarRestrictionDirectImage φ f).hom.naturality, hH H]

/-- Successive finite coefficient comparisons satisfy the cocycle with the canonical
restriction associators. Source: Stacks Tag 070Y and the coefficient-pasting DAG argument
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

Proof: the private scalar-pullback coherence calculation above uses arbitrary coefficient
maps and schemes, with the specified restriction associators. Apply the general
mate-composition lemma to the three derived pullback/direct-image adjunctions.
The inverse of each specified direct-image comparison is exactly this mate.
This gives the composition law for the inverse comparisons, with the target
associator inverse first and the source associator last. Invert the resulting
component isomorphism and cancel the image of the source associator with its
inverse. The result is the displayed equation. This uses neither a preservation
of K-injectives hypothesis nor any geometric finiteness hypothesis. -/
theorem fixedScalarRestrictionDirectImage_cocycle
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C))) :
    (R((f)_*[ModuleCat.{u + 1} A])).map
        ((Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology X)
          (f := φ) (g := ψ) rfl).hom.app L) ≫
      (fixedScalarRestrictionDirectImage (ψ.comp φ) f).hom.app L =
    (fixedScalarRestrictionDirectImage φ f).hom.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ψ).obj L) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((fixedScalarRestrictionDirectImage ψ f).hom.app L) ≫
      (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology Y)
        (f := φ) (g := ψ) rfl).hom.app ((R((f)_*[ModuleCat.{u + 1} C])).obj L) := by
  have h := mate_chain
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} C) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarRestrictScalarsIso ψ f).hom
    (leftDerivedUpperStarRestrictScalarsIso φ f).hom
    (leftDerivedUpperStarRestrictScalarsIso (ψ.comp φ) f).hom
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology Y) (f := φ) (g := ψ) rfl)
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology X) (f := φ) (g := ψ) rfl)
    (scalarRestriction_chain φ ψ f) L
  change (fixedScalarRestrictionDirectImageMap (ψ.comp φ) f).app L = _ at h
  let z :=
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology Y)
      (f := φ) (g := ψ) rfl).symm.app
        ((R((f)_*[ModuleCat.{u + 1} C])).obj L) ≪≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).mapIso
      ((fixedScalarRestrictionDirectImage ψ f).symm.app L) ≪≫
    (fixedScalarRestrictionDirectImage φ f).symm.app
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ψ).obj L) ≪≫
    (R((f)_*[ModuleCat.{u + 1} A])).mapIso
      ((Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology X)
        (f := φ) (g := ψ) rfl).app L)
  have hz : (fixedScalarRestrictionDirectImage (ψ.comp φ) f).symm.app L = z := by
    apply Iso.ext
    simpa only [z, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, fixedScalarRestrictionDirectImage_inv,
      fixedScalarRestrictionDirectImageMap, fixedScalarRestrictionPullback] using h
  have hh := congrArg Iso.inv hz
  dsimp only [z, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv] at hh
  rw [hh]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]


end AlgebraicGeometry.ProEtale
