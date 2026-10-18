/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-!
# Coefficient comparisons and the compact-support exchange map

We reduce the compatibility of the coefficient comparison
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso` with the
compact-support exchange map `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`
to the compatibility of each of its building blocks, through the abstract predicate
`AlgebraicGeometry.Etale.CoeffCompatible` and its stability under composition, whiskering and
inversion. The building blocks (A), (B), (C) are not proved yet. The file then deduces the
coefficient-change statements used by `AlgebraicGeometry.Etale.AdicSystem`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Abstract

variable {A A' B B' C C' D D' : Type*} [Category A] [Category A'] [Category B] [Category B']
  [Category C] [Category C'] [Category D] [Category D'] {RA : A' ⥤ A} {RB : B' ⥤ B}
  {RC : C' ⥤ C} {RD : D' ⥤ D}

/-- Two natural transformations `α : F ⟶ G` and `α' : F' ⟶ G'` are compatible with the
coefficient comparisons `ιF : RB ⋙ F ≅ F' ⋙ RA` and `ιG : RB ⋙ G ≅ G' ⋙ RA`. -/
def CoeffCompatible {F G : B ⥤ A} {F' G' : B' ⥤ A'} (ιF : RB ⋙ F ≅ F' ⋙ RA)
    (ιG : RB ⋙ G ≅ G' ⋙ RA) (α : F ⟶ G) (α' : F' ⟶ G') : Prop :=
  ∀ K, ιF.hom.app K ≫ RA.map (α'.app K) = α.app (RB.obj K) ≫ ιG.hom.app K

namespace CoeffCompatible

variable {F G H : B ⥤ A} {F' G' H' : B' ⥤ A'} {ιF : RB ⋙ F ≅ F' ⋙ RA}
  {ιG : RB ⋙ G ≅ G' ⋙ RA} {ιH : RB ⋙ H ≅ H' ⋙ RA}

lemma comp {α : F ⟶ G} {α' : F' ⟶ G'} {β : G ⟶ H} {β' : G' ⟶ H'}
    (h₁ : CoeffCompatible ιF ιG α α') (h₂ : CoeffCompatible ιG ιH β β') :
    CoeffCompatible ιF ιH (α ≫ β) (α' ≫ β') := by
  intro K
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, reassoc_of% (h₁ K), h₂ K,
    Category.assoc]

lemma inv {e : F ≅ G} {e' : F' ≅ G'} (h : CoeffCompatible ιF ιG e.hom e'.hom) :
    CoeffCompatible ιG ιF e.inv e'.inv := by
  intro K
  rw [← cancel_epi (e.hom.app (RB.obj K)), ← reassoc_of% (h K)]
  simp [← Functor.map_comp]

lemma whiskerLeft {E : C ⥤ B} {E' : C' ⥤ B'} (ιE : RC ⋙ E ≅ E' ⋙ RB) {α : F ⟶ G}
    {α' : F' ⟶ G'} (h : CoeffCompatible ιF ιG α α') :
    CoeffCompatible (pasteTwoSquaresIso ιE ιF) (pasteTwoSquaresIso ιE ιG)
      (Functor.whiskerLeft E α) (Functor.whiskerLeft E' α') := by
  intro K
  simp only [pasteTwoSquaresIso_hom_app, Functor.whiskerLeft_app, Category.assoc, h (E'.obj K)]
  exact α.naturality_assoc _ _

lemma whiskerRight {E : A ⥤ D} {E' : A' ⥤ D'} (ιE : RA ⋙ E ≅ E' ⋙ RD) {α : F ⟶ G}
    {α' : F' ⟶ G'} (h : CoeffCompatible ιF ιG α α') :
    CoeffCompatible (pasteTwoSquaresIso ιF ιE) (pasteTwoSquaresIso ιG ιE)
      (Functor.whiskerRight α E) (Functor.whiskerRight α' E') := by
  intro K
  have := ιE.hom.naturality (α'.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at this
  simp only [pasteTwoSquaresIso_hom_app, Functor.whiskerRight_app, Category.assoc, ← this,
    ← Functor.map_comp_assoc]
  rw [h K]

lemma associator_hom {F₁ : C ⥤ B} {F₂ : B ⥤ A} {F₃ : A ⥤ D} {F₁' : C' ⥤ B'} {F₂' : B' ⥤ A'}
    {F₃' : A' ⥤ D'} (ι₁ : RC ⋙ F₁ ≅ F₁' ⋙ RB) (ι₂ : RB ⋙ F₂ ≅ F₂' ⋙ RA)
    (ι₃ : RA ⋙ F₃ ≅ F₃' ⋙ RD) :
    CoeffCompatible (pasteTwoSquaresIso (pasteTwoSquaresIso ι₁ ι₂) ι₃)
      (pasteTwoSquaresIso ι₁ (pasteTwoSquaresIso ι₂ ι₃))
      (Functor.associator F₁ F₂ F₃).hom (Functor.associator F₁' F₂' F₃').hom := by
  intro K
  simp [pasteTwoSquaresIso_hom_app]

lemma associator_inv {F₁ : C ⥤ B} {F₂ : B ⥤ A} {F₃ : A ⥤ D} {F₁' : C' ⥤ B'} {F₂' : B' ⥤ A'}
    {F₃' : A' ⥤ D'} (ι₁ : RC ⋙ F₁ ≅ F₁' ⋙ RB) (ι₂ : RB ⋙ F₂ ≅ F₂' ⋙ RA)
    (ι₃ : RA ⋙ F₃ ≅ F₃' ⋙ RD) :
    CoeffCompatible (pasteTwoSquaresIso ι₁ (pasteTwoSquaresIso ι₂ ι₃))
      (pasteTwoSquaresIso (pasteTwoSquaresIso ι₁ ι₂) ι₃)
      (Functor.associator F₁ F₂ F₃).inv (Functor.associator F₁' F₂' F₃').inv := by
  intro K
  simp [pasteTwoSquaresIso_hom_app]

end CoeffCompatible

end Abstract

section DerivedLift

open Functor

variable {X X' Y Y' Z Z' : Type*} [Category X] [Category X'] [Category Y] [Category Y']
  [Category Z] [Category Z']

/-- The coefficient comparison `ι` conjugated by isomorphisms `φ : G ≅ F` and `φ' : G' ≅ F'` is
compatible with `φ` and `φ'`. -/
lemma CoeffCompatible.of_conj {rX : X' ⥤ X} {rY : Y' ⥤ Y} {F G : X ⥤ Y} {F' G' : X' ⥤ Y'}
    (ι : rX ⋙ F ≅ F' ⋙ rY) (φ : G ≅ F) (φ' : G' ≅ F') :
    CoeffCompatible (isoWhiskerLeft rX φ ≪≫ ι ≪≫ isoWhiskerRight φ'.symm rY) ι φ.hom φ'.hom := by
  intro K
  simp [← Functor.map_comp]

variable [Abelian X] [Abelian X'] [Abelian Y] [Abelian Y'] [Abelian Z] [Abelian Z']
  [HasDerivedCategory X] [HasDerivedCategory X'] [HasDerivedCategory Y] [HasDerivedCategory Y']
  [HasDerivedCategory Z] [HasDerivedCategory Z']
  {rX : X' ⥤ X} {rY : Y' ⥤ Y} {rZ : Z' ⥤ Z}
  [rX.Additive] [PreservesFiniteLimits rX] [PreservesFiniteColimits rX]
  [rY.Additive] [PreservesFiniteLimits rY] [PreservesFiniteColimits rY]
  [rZ.Additive] [PreservesFiniteLimits rZ] [PreservesFiniteColimits rZ]

/-- Compatibility with coefficient comparisons passes to the isomorphisms induced on derived
categories by exact functors. -/
lemma CoeffCompatible.mapDerivedCategoryNatIso {P Q : X ⥤ Y} {P' Q' : X' ⥤ Y'}
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [P'.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    [Q'.Additive] [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
    {α : rX ⋙ P ≅ P' ⋙ rY} {γ : rX ⋙ Q ≅ Q' ⋙ rY} {β : P ≅ Q} {β' : P' ≅ Q'}
    (h : CoeffCompatible α γ β.hom β'.hom) :
    CoeffCompatible (mapDerivedCategorySquareIso α) (mapDerivedCategorySquareIso γ)
      (Functor.mapDerivedCategoryNatIso β).hom (Functor.mapDerivedCategoryNatIso β').hom := by
  have hiso : α ≪≫ isoWhiskerRight β' rY = isoWhiskerLeft rX β ≪≫ γ := by
    ext K
    simpa using h K
  have hm : (Functor.mapDerivedCategoryNatIso α).hom ≫
      (Functor.mapDerivedCategoryNatIso (isoWhiskerRight β' rY)).hom =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerLeft rX β)).hom ≫
        (Functor.mapDerivedCategoryNatIso γ).hom := by
    rw [← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans, hiso]
  have hR := mapDerivedCategoryNatIso_isoWhiskerRight β' rY
  have hL := mapDerivedCategoryNatIso_isoWhiskerLeft rX β
  have H : (mapDerivedCategorySquareIso α).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso β').hom rY.mapDerivedCategory =
      Functor.whiskerLeft rX.mapDerivedCategory (Functor.mapDerivedCategoryNatIso β).hom ≫
        (mapDerivedCategorySquareIso γ).hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hR, reassoc_of% hm]
    rw [← cancel_epi (mapDerivedCategoryCompIso rX P).hom, Iso.hom_inv_id_assoc,
      ← reassoc_of% hL, Iso.hom_inv_id_assoc]
  intro K
  simpa using NatTrans.congr_app H K

/-- The isomorphism induced on derived categories by a pasted square is the pasting of the
induced isomorphisms, up to the composition isomorphisms. -/
lemma CoeffCompatible.mapDerivedCategoryCompIso {F₁ : X ⥤ Y} {F₂ : Y ⥤ Z} {F₁' : X' ⥤ Y'}
    {F₂' : Y' ⥤ Z'}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₁'.Additive] [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
    [F₂'.Additive] [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
    (ι₁ : rX ⋙ F₁ ≅ F₁' ⋙ rY) (ι₂ : rY ⋙ F₂ ≅ F₂' ⋙ rZ) :
    CoeffCompatible (mapDerivedCategorySquareIso (pasteTwoSquaresIso ι₁ ι₂))
      (pasteTwoSquaresIso (mapDerivedCategorySquareIso ι₁) (mapDerivedCategorySquareIso ι₂))
      (Functor.mapDerivedCategoryCompIso F₁ F₂).hom
      (Functor.mapDerivedCategoryCompIso F₁' F₂').hom := by
  intro K
  have := mapDerivedCategorySquareIso_hom_app_comp ι₁ ι₂ (pasteTwoSquaresIso ι₁ ι₂)
    (Iso.refl _) (Iso.refl _) (by simp [pasteTwoSquaresIso_hom_app]) K
  simp only [mapDerivedCategoryTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    mapDerivedCategoryNatIso_refl, Category.id_comp] at this
  rw [pasteTwoSquaresIso_hom_app]
  exact this

end DerivedLift

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Compactification

variable [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} [CompactSpace Y]

/-- The coefficient comparison `Res ∘ Rf_!(c) ≅ Rf_!(c) ∘ Res` for an arbitrary
compactification `c` over a quasi-compact base. -/
noncomputable def compactificationRestrictScalarsIso (c : Compactification f) :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ Rf_!(c)[ModuleCat.{u + 1} Λ] ≅
      Rf_!(c)[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ :=
  have := c.isProper
  have := c.isOpenImmersion
  have hd := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite c.g
  pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g hd.choose hd.choose_spec)

lemma derivedRestrictScalarsCompRightDerivedLowerShriekIso_eq (f : X ⟶ Y)
    [HasCompactification f] :
    derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f =
      compactificationRestrictScalarsIso ρ (HasCompactification.compactification f) :=
  rfl

end Compactification

end AlgebraicGeometry.Etale
