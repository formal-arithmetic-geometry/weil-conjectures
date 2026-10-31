/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.AmbientClopen.UnderivedPasting.Systems.AmbientUnderivedClopenPasting
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting

/-! # Ordinary derived clopen comparisons

Source: Stacks Project, Tags 0F7B--0F7D, 015F and 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  upperStar lowerStar Functor.rightDerivedFunctor
  Functor.leftAdjoint constantSheaf

open CategoryTheory.Limits AmbientClopen

attribute [local irreducible] openImmersionLowerShriek AmbientClopen.alpha localizeSquare
  properOpenAlpha leftDerivedUpperStarComp properOpenAdj Adjunction.leftAdjointCompIso

private theorem exact_vertical
    (C : Fin 6 → Type*) [∀ i, Category (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory (C i)]
    (J₀ : C 0 ⥤ₑ C 1) (J₁ : C 2 ⥤ₑ C 3) (J₂ : C 4 ⥤ₑ C 5)
    (R₁ : C 2 ⥤ₑ C 0) (R₂ : C 4 ⥤ₑ C 2) (R : C 4 ⥤ₑ C 0)
    (P₁ : C 3 ⥤ₑ C 1) (P₂ : C 5 ⥤ₑ C 3) (P : C 5 ⥤ₑ C 1)
    [J₀.obj.Additive]
    [J₁.obj.Additive]
    [J₂.obj.Additive]
    [R₁.obj.Additive]
    [R₂.obj.Additive]
    [R.obj.Additive]
    [P₁.obj.Additive]
    [P₂.obj.Additive]
    [P.obj.Additive]
    (cr : R.obj ≅ R₂.obj ⋙ R₁.obj) (cp : P.obj ≅ P₂.obj ⋙ P₁.obj)
    (a₁ : J₁.obj ⋙ P₁.obj ⟶ R₁.obj ⋙ J₀.obj)
    (a₂ : J₂.obj ⋙ P₂.obj ⟶ R₂.obj ⋙ J₁.obj)
    (a : J₂.obj ⋙ P.obj ⟶ R.obj ⋙ J₀.obj)
    (h : Functor.whiskerRight a₂ P₁.obj ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R₂.obj a₁ =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J₂.obj cp.inv ≫ a ≫
        Functor.whiskerRight cr.hom J₀.obj ≫ (Functor.associator _ _ _).hom) :
    Functor.whiskerRight (localizeSquare _ _ _ _ a₂) P₁.obj.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R₂.obj.mapDerivedCategory (localizeSquare _ _ _ _ a₁) =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft J₂.obj.mapDerivedCategory
          ((Functor.mapDerivedCategoryCompIso P₂.obj P₁.obj).inv ≫ localize cp.inv) ≫
        localizeSquare _ _ _ _ a ≫
        Functor.whiskerRight
          (localize cr.hom ≫ (Functor.mapDerivedCategoryCompIso R₂.obj R₁.obj).hom)
          J₀.obj.mapDerivedCategory ≫ (Functor.associator _ _ _).hom := by
  let j₀ : ExactDerivedPasting.Word C 0 1 := .edge J₀
  let j₁ : ExactDerivedPasting.Word C 2 3 := .edge J₁
  let j₂ : ExactDerivedPasting.Word C 4 5 := .edge J₂
  let r₁ : ExactDerivedPasting.Word C 2 0 := .edge R₁
  let r₂ : ExactDerivedPasting.Word C 4 2 := .edge R₂
  let r : ExactDerivedPasting.Word C 4 0 := .edge R
  let p₁ : ExactDerivedPasting.Word C 3 1 := .edge P₁
  let p₂ : ExactDerivedPasting.Word C 5 3 := .edge P₂
  let p : ExactDerivedPasting.Word C 5 1 := .edge P
  let e₁ : ExactDerivedPasting.Expression C (.comp j₁ p₁) (.comp r₁ j₀) := .cell a₁
  let e₂ : ExactDerivedPasting.Expression C (.comp j₂ p₂) (.comp r₂ j₁) := .cell a₂
  let e : ExactDerivedPasting.Expression C (.comp j₂ p) (.comp r j₀) := .cell a
  let ep : ExactDerivedPasting.Expression C (.comp p₂ p₁) p := .cell cp.inv
  let er : ExactDerivedPasting.Expression C r (.comp r₂ r₁) := .cell cr.hom
  let lhs : ExactDerivedPasting.Expression C
      (.comp (.comp j₂ p₂) p₁) (.comp r₂ (.comp r₁ j₀)) :=
    .vcomp (.output e₂ p₁) (.vcomp (.assoc r₂ j₁ p₁) (.input r₂ e₁))
  let rhs : ExactDerivedPasting.Expression C
      (.comp (.comp j₂ p₂) p₁) (.comp r₂ (.comp r₁ j₀)) :=
    .vcomp (.assoc j₂ p₂ p₁) (.vcomp (.input j₂ ep)
      (.vcomp e (.vcomp (.output er j₀) (.assoc r₂ r₁ j₀))))
  have he : lhs.ordinary = rhs.ordinary := h
  have hd := (ExactDerivedPasting.exact_derived_transformation_pasting C).2.1 lhs rhs he
  simpa only [lhs, rhs, e₁, e₂, e, ep, er, j₀, j₁, j₂, r₁, r₂, r, p₁, p₂, p,
    ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
    ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
    ExactDerivedPasting.Word.derived, Iso.trans_hom, Iso.trans_inv, Iso.refl_hom,
    Iso.refl_inv, Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Category.id_comp, Category.comp_id, localizeSquare, localize] using hd

private theorem exact_horizontal
    (C : Fin 6 → Type*) [∀ i, Category (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory (C i)]
    (I₁ : C 0 ⥤ₑ C 1) (I₂ : C 1 ⥤ₑ C 2) (I : C 0 ⥤ₑ C 2)
    (K₁ : C 3 ⥤ₑ C 4) (K₂ : C 4 ⥤ₑ C 5) (K : C 3 ⥤ₑ C 5)
    (R : C 0 ⥤ₑ C 3) (P : C 1 ⥤ₑ C 4) (Q : C 2 ⥤ₑ C 5)
    [I₁.obj.Additive]
    [I₂.obj.Additive]
    [I.obj.Additive]
    [K₁.obj.Additive]
    [K₂.obj.Additive]
    [K.obj.Additive]
    [R.obj.Additive]
    [P.obj.Additive]
    [Q.obj.Additive]
    (ci : I₁.obj ⋙ I₂.obj ≅ I.obj) (ck : K₁.obj ⋙ K₂.obj ≅ K.obj)
    (a₁ : I₁.obj ⋙ P.obj ⟶ R.obj ⋙ K₁.obj)
    (a₂ : I₂.obj ⋙ Q.obj ⟶ P.obj ⋙ K₂.obj)
    (a : I.obj ⋙ Q.obj ⟶ R.obj ⋙ K.obj)
    (h : (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft I₁.obj a₂ ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight a₁ K₂.obj =
      Functor.whiskerRight ci.hom Q.obj ≫ a ≫ Functor.whiskerLeft R.obj ck.inv ≫
        (Functor.associator _ _ _).inv) :
    (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft I₁.obj.mapDerivedCategory (localizeSquare _ _ _ _ a₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (localizeSquare _ _ _ _ a₁) K₂.obj.mapDerivedCategory =
      Functor.whiskerRight
        ((Functor.mapDerivedCategoryCompIso I₁.obj I₂.obj).inv ≫ localize ci.hom)
        Q.obj.mapDerivedCategory ≫ localizeSquare _ _ _ _ a ≫
        Functor.whiskerLeft R.obj.mapDerivedCategory
          (localize ck.inv ≫ (Functor.mapDerivedCategoryCompIso K₁.obj K₂.obj).hom) ≫
        (Functor.associator _ _ _).inv := by
  let i₁ : ExactDerivedPasting.Word C 0 1 := .edge I₁
  let i₂ : ExactDerivedPasting.Word C 1 2 := .edge I₂
  let i : ExactDerivedPasting.Word C 0 2 := .edge I
  let k₁ : ExactDerivedPasting.Word C 3 4 := .edge K₁
  let k₂ : ExactDerivedPasting.Word C 4 5 := .edge K₂
  let k : ExactDerivedPasting.Word C 3 5 := .edge K
  let r : ExactDerivedPasting.Word C 0 3 := .edge R
  let p : ExactDerivedPasting.Word C 1 4 := .edge P
  let q : ExactDerivedPasting.Word C 2 5 := .edge Q
  let e₁ : ExactDerivedPasting.Expression C (.comp i₁ p) (.comp r k₁) := .cell a₁
  let e₂ : ExactDerivedPasting.Expression C (.comp i₂ q) (.comp p k₂) := .cell a₂
  let e : ExactDerivedPasting.Expression C (.comp i q) (.comp r k) := .cell a
  let ei : ExactDerivedPasting.Expression C (.comp i₁ i₂) i := .cell ci.hom
  let ek : ExactDerivedPasting.Expression C k (.comp k₁ k₂) := .cell ck.inv
  let lhs : ExactDerivedPasting.Expression C
      (.comp (.comp i₁ i₂) q) (.comp (.comp r k₁) k₂) :=
    .vcomp (.assoc i₁ i₂ q) (.vcomp (.input i₁ e₂)
      (.vcomp (.assocInv i₁ p k₂) (.output e₁ k₂)))
  let rhs : ExactDerivedPasting.Expression C
      (.comp (.comp i₁ i₂) q) (.comp (.comp r k₁) k₂) :=
    .vcomp (.output ei q) (.vcomp e (.vcomp (.input r ek) (.assocInv r k₁ k₂)))
  have he : lhs.ordinary = rhs.ordinary := h
  have hd := (ExactDerivedPasting.exact_derived_transformation_pasting C).2.1 lhs rhs he
  simpa only [lhs, rhs, e₁, e₂, e, ei, ek, i₁, i₂, i, k₁, k₂, k, r, p, q,
    ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
    ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
    ExactDerivedPasting.Word.derived, Iso.trans_hom, Iso.trans_inv, Iso.refl_hom,
    Iso.refl_inv, Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Category.id_comp, Category.comp_id, localizeSquare, localize] using hd

private theorem vertical_transport
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (J₀ : A ⥤ B) (J₁ : C ⥤ D) (J₂ : E ⥤ F)
    (R₁ R₁' : C ⥤ A) (R₂ R₂' : E ⥤ C) (R R' : E ⥤ A)
    (P₁ P₁' : D ⥤ B) (P₂ P₂' : F ⥤ D) (P P' : F ⥤ B)
    (er₁ : R₁ ≅ R₁') (er₂ : R₂ ≅ R₂') (er : R ≅ R')
    (ep₁ : P₁ ≅ P₁') (ep₂ : P₂ ≅ P₂') (ep : P ≅ P')
    (cr : R' ⟶ R₂' ⋙ R₁') (cp : P₂' ⋙ P₁' ⟶ P')
    (a₁ : J₁ ⋙ P₁' ⟶ R₁' ⋙ J₀) (a₂ : J₂ ⋙ P₂' ⟶ R₂' ⋙ J₁)
    (a : J₂ ⋙ P' ⟶ R' ⋙ J₀)
    (h : ∀ M, cp.app (J₂.obj M) ≫ a.app M ≫ J₀.map (cr.app M) =
      P₁'.map (a₂.app M) ≫ a₁.app (R₂'.obj M)) (M : E) :
    (Functor.whiskerLeft P₂ ep₁.hom ≫ Functor.whiskerRight ep₂.hom P₁' ≫
        cp ≫ ep.inv).app (J₂.obj M) ≫
      (Functor.whiskerLeft J₂ ep.hom ≫ a ≫ Functor.whiskerRight er.inv J₀).app M ≫
      J₀.map ((er.hom ≫ cr ≫ Functor.whiskerRight er₂.inv R₁' ≫
        Functor.whiskerLeft R₂ er₁.inv).app M) =
    P₁.map ((Functor.whiskerLeft J₂ ep₂.hom ≫ a₂ ≫
        Functor.whiskerRight er₂.inv J₁).app M) ≫
      (Functor.whiskerLeft J₁ ep₁.hom ≫ a₁ ≫
        Functor.whiskerRight er₁.inv J₀).app (R₂.obj M) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← J₀.map_comp_assoc, Iso.inv_hom_id_app, J₀.map_id, Category.id_comp]
  rw [reassoc_of% (h M)]
  rw [← reassoc_of% (a₁.naturality (er₂.inv.app M))]
  rw [← reassoc_of% (ep₁.hom.naturality (ep₂.hom.app (J₂.obj M))),
    ← reassoc_of% (ep₁.hom.naturality (a₂.app M)),
    ← reassoc_of% (ep₁.hom.naturality (J₁.map (er₂.inv.app M)))]

private theorem horizontal_transport
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (I₁ : A ⥤ B) (I₂ : B ⥤ C) (I : A ⥤ C)
    (K₁ : D ⥤ E) (K₂ : E ⥤ F) (K : D ⥤ F)
    (R R' : A ⥤ D) (P P' : B ⥤ E) (Q Q' : C ⥤ F)
    (er : R ≅ R') (ep : P ≅ P') (eq : Q ≅ Q')
    (ci : I₁ ⋙ I₂ ⟶ I) (ck : K ⟶ K₁ ⋙ K₂)
    (a₁ : I₁ ⋙ P' ⟶ R' ⋙ K₁) (a₂ : I₂ ⋙ Q' ⟶ P' ⋙ K₂)
    (a : I ⋙ Q' ⟶ R' ⋙ K)
    (h : ∀ M, Q'.map (ci.app M) ≫ a.app M ≫ ck.app (R'.obj M) =
      a₂.app (I₁.obj M) ≫ K₂.map (a₁.app M)) (M : A) :
    Q.map (ci.app M) ≫
      (Functor.whiskerLeft I eq.hom ≫ a ≫ Functor.whiskerRight er.inv K).app M ≫
      ck.app (R.obj M) =
    (Functor.whiskerLeft I₂ eq.hom ≫ a₂ ≫ Functor.whiskerRight ep.inv K₂).app
        (I₁.obj M) ≫
      K₂.map ((Functor.whiskerLeft I₁ ep.hom ≫ a₁ ≫
        Functor.whiskerRight er.inv K₁).app M) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [eq.hom.naturality_assoc, ck.naturality]
  simp only [Functor.comp_map]
  rw [reassoc_of% (h M)]
  simp only [← K₂.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rfl

private theorem pull_comp_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ X) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (f ≫ g)).hom ≫
      (localize (upperStarComp (ModuleCat.{u + 1} Λ) f g).hom ≫
        (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) g)
          (upperStar (ModuleCat.{u + 1} Λ) f)).hom) ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).inv
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory ≫
      Functor.whiskerLeft (ProperOpenPull Λ g)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).inv := by
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Category.assoc]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_assoc]
  rfl

private theorem pull_comp_inv
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ X) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).inv =
      Functor.whiskerLeft (ProperOpenPull Λ g)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).hom ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).hom
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory ≫
      ((Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) g)
        (upperStar (ModuleCat.{u + 1} Λ) f)).inv ≫
        localize (upperStarComp (ModuleCat.{u + 1} Λ) f g).inv) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (f ≫ g)).inv := by
  simpa only [leftDerivedUpperStarCongr, upperStarCongr, eqToIso_refl, Iso.refl_hom,
    Category.comp_id] using
    ordinary_pull_cell_localized Λ f g (f ≫ g) rfl

local instance exact_additive {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (F : A ⥤ₑ B) : F.obj.Additive :=
  exactFunctor_le_additiveFunctor A B _ F.property

private theorem ordinary_vertical
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A C₀ E B D F : Scheme.{u}}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
    (hv : Functor.whiskerRight (AmbientClopen.alpha Λ i r₂ p₂ j h₂)
        (upperStar (ModuleCat.{u + 1} Λ) p₁) ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) r₂)
          (AmbientClopen.alpha Λ k r₁ p₁ i h₁) =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
          (upperStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).inv ≫
        AmbientClopen.alpha Λ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h ≫
        Functor.whiskerRight (upperStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ≫
        (Functor.associator _ _ _).hom)
    (M : ProperOpenDerived Λ E) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).inv.app
        ((ProperOpenShriek Λ j).obj M) ≫
      (properOpenAlpha Λ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
      (ProperOpenShriek Λ k).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom.app M) =
    (ProperOpenPull Λ p₁).map ((properOpenAlpha Λ i r₂ p₂ j h₂).app M) ≫
      (properOpenAlpha Λ k r₁ p₁ i h₁).app ((ProperOpenPull Λ r₂).obj M) := by
  let X : Fin 6 → Scheme.{u} := ![A, B, C₀, D, E, F]
  let C (a : Fin 6) := Sheaf (Scheme.ProEt.topology (X a)) (ModuleCat.{u + 1} Λ)
  let : ∀ a, Category.{u + 1} (C a) := fun a ↦ inferInstance
  let : ∀ a, Abelian (C a) := fun a ↦ inferInstance
  let : ∀ a, HasDerivedCategory.{u + 1} (C a) := fun a ↦ inferInstance
  have hd := exact_vertical C
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) r₁))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) r₂))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) (r₁ ≫ r₂)))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) p₁))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) p₂))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) (p₁ ≫ p₂)))
    (upperStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)
    (upperStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)
    (AmbientClopen.alpha Λ k r₁ p₁ i h₁) (AmbientClopen.alpha Λ i r₂ p₂ j h₂)
    (AmbientClopen.alpha Λ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h) hv
  simp only [ExactFunctor.of_fst] at hd
  let P {S T : Scheme.{u}} (f : S ⟶ T) :=
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory
  let e {S T : Scheme.{u}} (f : S ⟶ T) :=
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f
  have ht := vertical_transport
    (ProperOpenShriek Λ k) (ProperOpenShriek Λ i) (ProperOpenShriek Λ j)
    (ProperOpenPull Λ r₁) (P r₁) (ProperOpenPull Λ r₂) (P r₂)
    (ProperOpenPull Λ (r₁ ≫ r₂)) (P (r₁ ≫ r₂))
    (ProperOpenPull Λ p₁) (P p₁) (ProperOpenPull Λ p₂) (P p₂)
    (ProperOpenPull Λ (p₁ ≫ p₂)) (P (p₁ ≫ p₂))
    (e r₁) (e r₂) (e (r₁ ≫ r₂)) (e p₁) (e p₂) (e (p₁ ≫ p₂))
    (localize (upperStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom ≫
      (Functor.mapDerivedCategoryCompIso _ _).hom)
    ((Functor.mapDerivedCategoryCompIso _ _).inv ≫
      localize (upperStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).inv)
    (localizeSquare _ _ _ _ (AmbientClopen.alpha Λ k r₁ p₁ i h₁))
    (localizeSquare _ _ _ _ (AmbientClopen.alpha Λ i r₂ p₂ j h₂))
    (localizeSquare _ _ _ _
      (AmbientClopen.alpha Λ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h))
    (by
      intro N
      have hn := congr_app hd N
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id,
        Functor.map_comp, Category.assoc, P] using hn.symm) M
  rw [pull_comp_inv Λ p₁ p₂, pull_comp_hom Λ r₁ r₂,
    ← ordinary_alpha_localized Λ k r₁ p₁ i h₁,
    ← ordinary_alpha_localized Λ i r₂ p₂ j h₂,
    ← ordinary_alpha_localized Λ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h]
  exact ht

private theorem ordinary_horizontal
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B E C₀ D F : Scheme.{u}}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
    (hv : (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
          (AmbientClopen.alpha Λ l p q j h₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (AmbientClopen.alpha Λ k r p i h₁)
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) l) =
      Functor.whiskerRight (openComp Λ i j).hom (upperStar (ModuleCat.{u + 1} Λ) q) ≫
        AmbientClopen.alpha Λ (k ≫ l) r q (i ≫ j) h ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) r) (openComp Λ k l).inv ≫
        (Functor.associator _ _ _).inv)
    (M : ProperOpenDerived Λ C₀) :
    (ProperOpenPull Λ q).map ((properOpenShriekComp Λ i j).hom.app M) ≫
      (properOpenAlpha Λ (k ≫ l) r q (i ≫ j) h).app M ≫
      (properOpenShriekComp Λ k l).inv.app ((ProperOpenPull Λ r).obj M) =
    (properOpenAlpha Λ l p q j h₂).app ((ProperOpenShriek Λ i).obj M) ≫
      (ProperOpenShriek Λ l).map ((properOpenAlpha Λ k r p i h₁).app M) := by
  let X : Fin 6 → Scheme.{u} := ![C₀, D, F, A, B, E]
  let C (a : Fin 6) := Sheaf (Scheme.ProEt.topology (X a)) (ModuleCat.{u + 1} Λ)
  let : ∀ a, Category.{u + 1} (C a) := fun a ↦ inferInstance
  let : ∀ a, Abelian (C a) := fun a ↦ inferInstance
  let : ∀ a, HasDerivedCategory.{u + 1} (C a) := fun a ↦ inferInstance
  have hd := exact_horizontal C
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (i ≫ j)))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) l))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (k ≫ l)))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) r))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) p))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) q))
    (openComp Λ i j) (openComp Λ k l)
    (AmbientClopen.alpha Λ k r p i h₁) (AmbientClopen.alpha Λ l p q j h₂)
    (AmbientClopen.alpha Λ (k ≫ l) r q (i ≫ j) h) hv
  simp only [ExactFunctor.of_fst] at hd
  have hi := congrArg Iso.hom (ordinary_open_comp_localized Λ i j)
  have hk := congrArg Iso.inv (ordinary_open_comp_localized Λ k l)
  change (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    localize (openComp Λ i j).hom = (properOpenShriekComp Λ i j).hom at hi
  change localize (openComp Λ k l).inv ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom = (properOpenShriekComp Λ k l).inv at hk
  rw [hi, hk] at hd
  have ht := horizontal_transport
    (ProperOpenShriek Λ i) (ProperOpenShriek Λ j) (ProperOpenShriek Λ (i ≫ j))
    (ProperOpenShriek Λ k) (ProperOpenShriek Λ l) (ProperOpenShriek Λ (k ≫ l))
    (ProperOpenPull Λ r) (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory
    (ProperOpenPull Λ p) (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory
    (ProperOpenPull Λ q) (upperStar (ModuleCat.{u + 1} Λ) q).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) q)
    (properOpenShriekComp Λ i j).hom (properOpenShriekComp Λ k l).inv
    (localizeSquare _ _ _ _ (AmbientClopen.alpha Λ k r p i h₁))
    (localizeSquare _ _ _ _ (AmbientClopen.alpha Λ l p q j h₂))
    (localizeSquare _ _ _ _ (AmbientClopen.alpha Λ (k ≫ l) r q (i ≫ j) h))
    (by
      intro N
      have hn := congr_app hd N
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using hn.symm) M
  rw [← ordinary_alpha_localized Λ k r p i h₁,
    ← ordinary_alpha_localized Λ l p q j h₂,
    ← ordinary_alpha_localized Λ (k ≫ l) r q (i ≫ j) h]
  exact ht

local instance space_over (F : WeilConjectures.FiniteFieldDatum.{u}) (X : Spaces F) :
    X.obj.left.Over (Spec (.of F.k)) := ⟨X.obj.hom⟩

local instance space_finite_type (F : WeilConjectures.FiniteFieldDatum.{u}) (X : Spaces F) :
    LocallyOfFiniteType (X.obj.left ↘ Spec (.of F.k)) := X.property.1

local instance space_quasi_compact (F : WeilConjectures.FiniteFieldDatum.{u}) (X : Spaces F) :
    QuasiCompact (X.obj.left ↘ Spec (.of F.k)) := X.property.2

local instance space_map_over (F : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Spaces F} (f : X ⟶ Y) : f.hom.left.IsOver (Spec (.of F.k)) := ⟨f.hom.w⟩

/-- Both geometric pasting equations for the localized ordinary clopen arrow.
Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D; derived.tex, Tag 015F
(blueprint: lem-sf-ordinary-ambient-alpha-pasting).

Proof: At level n, take the vertical and horizontal equations of
ambientUnderivedClopenPasting. Regard inverse image and open extension as exact
functors and apply exact_derived_transformation_pasting to these finite diagrams.
Identify each localized clopen cell with properOpenAlpha using the ordinary clause
of ambientExactClopenComparisonLocalizes. The total-to-exact pullback comparisons
identify localized inverse-image compositors with leftDerivedUpperStarComp. The
localized open adjunction has the localized ordinary unit and counit; uniqueness of
left adjoints therefore identifies its open compositor with Calculus.jComp.
Substitute these comparisons into the two localized equations and cancel the
factorization isomorphisms. This gives the stated component equations. All steps
use arbitrary unbounded complexes. Identity and empty opens require no exclusions:
the ordinary equations and exact localization apply to them as well. -/
theorem ordinaryAmbientAlphaPasting (F₀ : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F₀.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    let c := (ordinary F₀ (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (∀ {A C₀ E B D F : Spaces F₀}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion ((geometry F₀).map k)] [IsOpenImmersion ((geometry F₀).map i)]
    [IsOpenImmersion ((geometry F₀).map j)]
    [QuasiCompact ((geometry F₀).map k)] [QuasiCompact ((geometry F₀).map i)]
    [QuasiCompact ((geometry F₀).map j)]
    [IsProper ((geometry F₀).map r₁)] [IsProper ((geometry F₀).map r₂)]
    [IsProper ((geometry F₀).map p₁)] [IsProper ((geometry F₀).map p₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : c.D E),
    (c.pComp p₁ p₂).inv.app ((c.J j).obj M) ≫
        (c.alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (c.J k).map ((c.pComp r₁ r₂).hom.app M) =
      (c.P p₁).map ((c.alpha i r₂ p₂ j h₂).app M) ≫
        (c.alpha k r₁ p₁ i h₁).app ((c.P r₂).obj M)) ∧
    (∀ {A B E C₀ D F : Spaces F₀}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion ((geometry F₀).map k)] [IsOpenImmersion ((geometry F₀).map l)]
    [IsOpenImmersion ((geometry F₀).map i)] [IsOpenImmersion ((geometry F₀).map j)]
    [QuasiCompact ((geometry F₀).map k)] [QuasiCompact ((geometry F₀).map l)]
    [QuasiCompact ((geometry F₀).map i)] [QuasiCompact ((geometry F₀).map j)]
    [IsProper ((geometry F₀).map r)] [IsProper ((geometry F₀).map p)]
    [IsProper ((geometry F₀).map q)]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : c.D C₀),
    (c.P q).map ((c.jComp i j).hom.app M) ≫
        (c.alpha (k ≫ l) r q (i ≫ j) h).app M ≫
        (c.jComp k l).inv.app ((c.P r).obj M) =
      (c.alpha l p q j h₂).app ((c.J i).obj M) ≫
        (c.J l).map ((c.alpha k r p i h₁).app M)) := by
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  have hp := (AmbientClopen.UnderivedPasting.ambientUnderivedClopenPasting F₀ l hl E).1 n
  constructor
  · intro A C₀ E₀ B D F k i j r₁ r₂ p₁ p₂ hk hi hj hqk hqi hqj hr₁ hr₂ hp₁ hp₂
      h₁ h₂ h M
    have : IsOpenImmersion k.hom.left := hk
    have : IsOpenImmersion i.hom.left := hi
    have : IsOpenImmersion j.hom.left := hj
    have : QuasiCompact k.hom.left := hqk
    have : QuasiCompact i.hom.left := hqi
    have : QuasiCompact j.hom.left := hqj
    have : IsProper r₁.hom.left := hr₁
    have : IsProper r₂.hom.left := hr₂
    have : IsProper p₁.hom.left := hp₁
    have : IsProper p₂.hom.left := hp₂
    exact ordinary_vertical Λ k.hom.left i.hom.left j.hom.left
      r₁.hom.left r₂.hom.left p₁.hom.left p₂.hom.left
      (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
      (congrArg (fun f ↦ f.hom.left) h)
      (hp.1 A.obj.left C₀.obj.left E₀.obj.left B.obj.left D.obj.left F.obj.left
        k.hom.left i.hom.left j.hom.left r₁.hom.left r₂.hom.left p₁.hom.left p₂.hom.left
        (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
        (congrArg (fun f ↦ f.hom.left) h)).1 M
  · intro A B E₀ C₀ D F k ll i j r p q hk hl hi hj hqk hql hqi hqj hr hp₀ hq h₁ h₂ h M
    have : IsOpenImmersion k.hom.left := hk
    have : IsOpenImmersion ll.hom.left := hl
    have : IsOpenImmersion i.hom.left := hi
    have : IsOpenImmersion j.hom.left := hj
    have : QuasiCompact k.hom.left := hqk
    have : QuasiCompact ll.hom.left := hql
    have : QuasiCompact i.hom.left := hqi
    have : QuasiCompact j.hom.left := hqj
    have : IsProper r.hom.left := hr
    have : IsProper p.hom.left := hp₀
    have : IsProper q.hom.left := hq
    change (ProperOpenPull Λ q.hom.left).map
        ((properOpenShriekComp Λ i.hom.left j.hom.left).hom.app M) ≫
      (properOpenAlpha Λ (k.hom.left ≫ ll.hom.left) r.hom.left q.hom.left
        (i.hom.left ≫ j.hom.left) (congrArg (fun f ↦ f.hom.left) h)).app M ≫
      (properOpenShriekComp Λ k.hom.left ll.hom.left).inv.app
        ((ProperOpenPull Λ r.hom.left).obj M) = _
    exact ordinary_horizontal Λ k.hom.left ll.hom.left i.hom.left j.hom.left
      r.hom.left p.hom.left q.hom.left
      (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
      (congrArg (fun f ↦ f.hom.left) h)
      (hp.2.1 A.obj.left B.obj.left E₀.obj.left C₀.obj.left D.obj.left F.obj.left
        k.hom.left ll.hom.left i.hom.left j.hom.left r.hom.left p.hom.left q.hom.left
        (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
        (congrArg (fun f ↦ f.hom.left) h)).1 M

end AlgebraicGeometry.ProEtale.AmbientProperOpen
