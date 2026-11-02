/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjectionCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-! # Coefficient compatibility for a constituent of compact-support refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

attribute [local instance] fieldSheafAbelian
attribute [local instance] fieldSheafGrothendieck
attribute [local instance] fieldSheafBigColimits
attribute [local instance] fieldSheafCoequalizers
attribute [local instance] fieldSheafMonoidalPreadditive
attribute [local instance] fieldModuleAbelian
attribute [local instance] fieldModuleGrothendieck
attribute [local instance] fieldModuleKInjectiveResolutions
attribute [local instance] fieldModuleDerivedCategory
attribute [local instance] fieldModuleColimits
attribute [local instance] fieldModuleBigColimits
attribute [local instance] fieldSheafFlatResolution
attribute [local instance] fieldModuleFlatResolution
attribute [local instance] fieldModuleCountableCoproducts
attribute [local instance] fieldModuleIntegerColimits
attribute [local instance] fieldModuleIntegerExactColimits
attribute [local instance] fieldTensorColimits
attribute [local instance] fieldTensorColimitsRight
attribute [local instance] fieldGradedTensor
attribute [local instance] fieldGradedFour
attribute [local instance] fieldGradedLeft
attribute [local instance] fieldGradedRight
attribute [local instance] fieldExtendScalarsKFlat

namespace WeilConjectures.CompactSupportCondensedRealization

attribute [local irreducible] condensedScalar condensedPushScalar condensedOpenScalar
  CondensedRing.lowerStar CondensedRing.upperStar CondensedRing.openImmersionLowerShriek
  fieldPushComp fieldProperOpen

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] [FlatCoefficientMap a]

private def constructibleInclusion
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u}) :
    BoundedConstructible (condensedRingObj Λ₀ W) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ₀ W)) where
  obj K := K.obj
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private def preWhisker {B C E : Type*} [Category B] [Category C] [Category E]
    {F G : B ⥤ C} (α : F ⟶ G) (T : C ⥤ E) :=
  Functor.whiskerRight α T

private def restrictNat {B C E : Type*} [Category B] [Category C] [Category E]
    {F G : C ⥤ E} (p : F ⟶ G) (I : B ⥤ C) :=
  Functor.whiskerLeft I p

private def properCompRaw {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (e : f ≫ g = h) :
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
        (CondensedRing.lowerStar Λ g).rightDerivedFunctor ⟶
      (CondensedRing.lowerStar Λ h).rightDerivedFunctor :=
  (fieldPushComp Λ f g).hom ≫ eqToHom (congrArg (fieldDerivedLowerStar Λ) e)

private theorem properCompRaw_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (e : f ≫ g = h) :
    properCompRaw (Λ := Λ) f g e =
      (fieldPushComp Λ f g).hom ≫ eqToHom (congrArg (fieldDerivedLowerStar Λ) e) := by
  rfl

private theorem paste_component {C : Type*} [Category C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C}
    {A : O₀ ⟶ O₁} {B : O₁ ⟶ O₂} {C₁ : O₂ ⟶ O₃} {D : O₃ ⟶ O₄}
    {F : O₁ ⟶ O₅} {G : O₅ ⟶ O₆} {H : O₆ ⟶ O₃}
    {J : O₀ ⟶ O₇} {L : O₇ ⟶ O₅} {M : O₆ ⟶ O₈} {N : O₈ ⟶ O₄}
    (hc : B ≫ C₁ = F ≫ G ≫ H) (hn : A ≫ F = J ≫ L)
    (hq : M ≫ N = H ≫ D) :
    A ≫ B ≫ C₁ ≫ D = J ≫ L ≫ G ≫ M ≫ N := by
  calc
    _ = A ≫ (B ≫ C₁) ≫ D := by simp only [Category.assoc]
    _ = A ≫ (F ≫ G ≫ H) ≫ D := by rw [hc]
    _ = (A ≫ F) ≫ G ≫ (H ≫ D) := by simp only [Category.assoc]
    _ = (J ≫ L) ≫ G ≫ (M ≫ N) := by rw [hn, ← hq]
    _ = _ := by simp only [Category.assoc]

private theorem fold_map_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {W X Y Z : C} {P Q : D}
    (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) (p : P ⟶ F.obj W) (q : F.obj Z ⟶ Q) :
    p ≫ F.map u ≫ F.map v ≫ F.map w ≫ q = p ≫ F.map (u ≫ v ≫ w) ≫ q := by
  simp only [F.map_comp, Category.assoc]

/-- The scalar-compositor square, kept as an equation of natural transformations. -/
private def compositorLaw
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (P : C ⥤ D) (R : D ⥤ E) (S : C ⥤ E)
    (P' : C' ⥤ D') (R' : D' ⥤ E') (S' : C' ⥤ E')
    (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (cmp : P ⋙ R ⟶ S) (cmp' : P' ⋙ R' ⟶ S')
    (pf : P ⋙ TD ⟶ TC ⋙ P') (pg : R ⋙ TE ⟶ TD ⋙ R')
    (ph : S ⋙ TE ⟶ TC ⋙ S') : Prop :=
  Functor.whiskerRight cmp TE ≫ ph =
    (Functor.associator P R TE).hom ≫ Functor.whiskerLeft P pg ≫
      (Functor.associator P TD R').inv ≫ Functor.whiskerRight pf R' ≫
      (Functor.associator TC P' R').hom ≫ Functor.whiskerLeft TC cmp'

private theorem compositorLaw_app
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (P : C ⥤ D) (R : D ⥤ E) (S : C ⥤ E)
    (P' : C' ⥤ D') (R' : D' ⥤ E') (S' : C' ⥤ E')
    (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (cmp : P ⋙ R ⟶ S) (cmp' : P' ⋙ R' ⟶ S')
    (pf : P ⋙ TD ⟶ TC ⋙ P') (pg : R ⋙ TE ⟶ TD ⋙ R')
    (ph : S ⋙ TE ⟶ TC ⋙ S')
    (hc : compositorLaw P R S P' R' S' TC TD TE cmp cmp' pf pg ph) (L : C) :
    TE.map (cmp.app L) ≫ ph.app L =
      pg.app (P.obj L) ≫ R'.map (pf.app L) ≫ cmp'.app (TC.obj L) := by
  have h := congr_app hc L
  simpa only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using h

private theorem mate_composition
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {Lf : D ⥤ C} {Rf : C ⥤ D} {Lg : E ⥤ D} {Rg : D ⥤ E}
    {Lh : E ⥤ C} {Rh : C ⥤ E}
    {Lf' : D' ⥤ C'} {Rf' : C' ⥤ D'} {Lg' : E' ⥤ D'} {Rg' : D' ⥤ E'}
    {Lh' : E' ⥤ C'} {Rh' : C' ⥤ E'}
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
    (af' : Lf' ⊣ Rf') (ag' : Lg' ⊣ Rg') (ah' : Lh' ⊣ Rh')
    {TC : C ⥤ C'} {TD : D ⥤ D'} {TE : E ⥤ E'}
    (sf : TwoSquare TD Lf Lf' TC) (sg : TwoSquare TE Lg Lg' TD)
    (sh : TwoSquare TE Lh Lh' TC)
    (cf : Lh ⟶ Lg ⋙ Lf) (cf' : Lh' ⟶ Lg' ⋙ Lf')
    (pf : Rf ⋙ TD ⟶ TC ⋙ Rf') (pg : Rg ⋙ TE ⟶ TD ⋙ Rg')
    (ph : Rh ⋙ TE ⟶ TC ⋙ Rh')
    (hf : pf = mateEquiv af af' sf) (hg : pg = mateEquiv ag ag' sg)
    (hh : ph = mateEquiv ah ah' sh)
    (hs : sh.whiskerLeft cf = (sg.vComp sf).whiskerRight cf') :
    compositorLaw Rf Rg Rh Rf' Rg' Rh' TC TD TE
      (conjugateEquiv (ag.comp af) ah cf)
      (conjugateEquiv (ag'.comp af') ah' cf') pf pg ph := by
  have hm := congrArg (mateEquiv (ag.comp af) ah') hs
  rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
    mateEquiv_hcomp, ← hf, ← hg, ← hh] at hm
  simpa only [compositorLaw, TwoSquare, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, TwoSquare.natTrans, TwoSquare.mk, Category.assoc] using hm

private theorem pushScalar_comp_raw {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    compositorLaw
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ (f ≫ g)).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' (f ≫ g)).rightDerivedFunctor
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor
      (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor
      (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor
      (conjugateEquiv
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).comp
          (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f))
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
        (CondensedRing.leftDerivedUpperStarComp Λ f g).hom)
      (conjugateEquiv
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ' g).comp
          (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f))
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' (f ≫ g))
        (CondensedRing.leftDerivedUpperStarComp Λ' f g).hom)
      (CondensedRing.derivedPushHom a f) (CondensedRing.derivedPushHom a g)
      (CondensedRing.derivedPushHom a (f ≫ g)) := by
  let sqH := TwoSquare.mk _ _ _ _ (CondensedRing.derivedPullIso a (f ≫ g)).inv
  let sqG := TwoSquare.mk _ _ _ _ (CondensedRing.derivedPullIso a g).inv
  let sqF := TwoSquare.mk _ _ _ _ (CondensedRing.derivedPullIso a f).inv
  have h : sqH.whiskerLeft (CondensedRing.leftDerivedUpperStarComp Λ f g).hom =
      (sqG.vComp sqF).whiskerRight (CondensedRing.leftDerivedUpperStarComp Λ' f g).hom := by
    ext M
    have hs := CondensedRing.squareCompatible_leftDerivedUpperStarComp a f g M
    have hi : (CondensedRing.derivedPullIso a (f ≫ g)).inv.app M ≫
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) =
        (CondensedRing.leftDerivedUpperStarComp Λ' f g).hom.app
            ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.obj M) ≫
          (Functor.pasteSquareIso (CondensedRing.derivedPullIso a g)
            (CondensedRing.derivedPullIso a f)).inv.app M := by
      apply (cancel_epi ((CondensedRing.derivedPullIso a (f ≫ g)).hom.app M)).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      rw [← hs]
      simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    simpa only [TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj,
      TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      sqH, sqG, sqF, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.pasteSquareIso_inv_app, Category.assoc] using hi
  exact mate_composition
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' (f ≫ g))
    sqF sqG sqH _ _ _ _ _
    (CondensedRing.derivedPushHom_eq_mateEquiv a f)
    (CondensedRing.derivedPushHom_eq_mateEquiv a g)
    (CondensedRing.derivedPushHom_eq_mateEquiv a (f ≫ g)) h

-- Named presentations retain the same natural-transformation equation.

private theorem pushScalar_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    compositorLaw
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ (f ≫ g)).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' (f ≫ g)).rightDerivedFunctor
      (condensedScalar a X) (condensedScalar a Y) (condensedScalar a Z)
      (fieldPushComp Λ f g).hom (fieldPushComp Λ' f g).hom
      (condensedPushScalar a f) (condensedPushScalar a g)
      (condensedPushScalar a (f ≫ g)) := by
  exact pushScalar_comp_raw a f g

-- Equality induction transports the whole compositor square.

private theorem pushScalar_comp_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (e : f ≫ g = h) :
    compositorLaw
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ h).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' h).rightDerivedFunctor
      (condensedScalar a X) (condensedScalar a Y) (condensedScalar a Z)
      ((fieldPushComp Λ f g).hom ≫
        eqToHom (congrArg (fieldDerivedLowerStar Λ) e))
      ((fieldPushComp Λ' f g).hom ≫
        eqToHom (congrArg (fieldDerivedLowerStar Λ') e))
      (condensedPushScalar a f) (condensedPushScalar a g)
      (condensedPushScalar a h) := by
  cases e
  have hc := pushScalar_comp a f g
  unfold compositorLaw at hc ⊢
  simpa only [eqToHom_refl, Category.comp_id] using hc

-- Match the typed wrappers before taking any component.

private theorem pushScalar_comp_transport_raw {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (e : f ≫ g = h) :
    compositorLaw
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ h).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' f).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' g).rightDerivedFunctor
      (CondensedRing.lowerStar Λ' h).rightDerivedFunctor
      (condensedScalar a X) (condensedScalar a Y) (condensedScalar a Z)
      (properCompRaw (Λ := Λ) f g e) (properCompRaw (Λ := Λ') f g e)
      (condensedPushScalar a f) (condensedPushScalar a g)
      (condensedPushScalar a h) := by
  exact pushScalar_comp_transport a f g e

private def properOpenNatRaw {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (constructibleInclusion Λ X) ⋙
        (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory ⟶
      ((constructibleInclusion Λ X) ⋙
        (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory) ⋙
        (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor :=
  fieldProperOpenNat Λ r

private theorem fieldRefinementNat_eq_assemble {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    fieldRefinementNat Λ r =
      assembleLiftNat
        ((constructibleInclusion Λ X) ⋙
          (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory)
        ((constructibleInclusion Λ X) ⋙
          (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory)
        (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
        (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
        (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
        (properOpenNatRaw (Λ := Λ) r)
        (properCompRaw (Λ := Λ) r.hom d.g r.hom_g) := by
  rfl

private theorem pasteScalar_app
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (J : C ⥤ D) (R : D ⥤ E) (J' : C' ⥤ D') (R' : D' ⥤ E')
    (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (p : R ⋙ TE ⟶ TD ⋙ R') (q : J ⋙ TD ⟶ TC ⋙ J') (K : C) :
    (pasteScalar J R J' R' TC TD TE p q).app K =
      p.app (J.obj K) ≫ R'.map (q.app K) := by
  simp only [pasteScalar, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

private theorem projection_eq_paste {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    condensedProjection a c = pasteScalar
      (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
      (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
      (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
      (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor
      (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a Y)
      (condensedPushScalar a c.g) (condensedOpenScalar a c.i).hom := by
  rfl

private def refinementNatRaw {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (constructibleInclusion Λ X) ⋙
      ((CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor) ⟶
    (constructibleInclusion Λ X) ⋙
      ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor) := fieldRefinementNat Λ r

private theorem refinementNatRaw_eq_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    refinementNatRaw (Λ := Λ) r = fieldRefinement Λ r := by
  rfl

private theorem refinementNatRaw_eq_assemble {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    refinementNatRaw (Λ := Λ) r =
      assembleLiftNat
        ((constructibleInclusion Λ X) ⋙
          (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory)
        ((constructibleInclusion Λ X) ⋙
          (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory)
        (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
        (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
        (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
        (properOpenNatRaw (Λ := Λ) r)
        (properCompRaw (Λ := Λ) r.hom d.g r.hom_g) := by
  exact fieldRefinementNat_eq_assemble (Λ := Λ) r

private theorem assembled_component
    {B C D E H : Type*} [Category B] [Category C] [Category D]
    [Category E] [Category H]
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (S : E ⥤ H)
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P) (cmp : P ⋙ R ⟶ S)
    (α : I ⋙ (J ⋙ R) ⟶ I ⋙ (K ⋙ S))
    (ha : α = assembleLiftNat (I ⋙ J) (I ⋙ K) P R S lift cmp)
    (M : B) (v : J.obj (I.obj M) ⟶ P.obj (K.obj (I.obj M)))
    (hv : lift.app M = v) :
    α.app M = R.map v ≫ cmp.app (K.obj (I.obj M)) := by
  rw [ha]
  change R.map (lift.app M) ≫ cmp.app (K.obj (I.obj M)) = _
  rw [hv]

private theorem assembled_projection
    {B C D E H C' E' H' : Type*}
    [Category B] [Category C] [Category D] [Category E] [Category H]
    [Category C'] [Category E'] [Category H']
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (S : E ⥤ H)
    (T : H ⥤ H') (TC : C ⥤ C') (TE : E ⥤ E')
    (K' : C' ⥤ E') (S' : E' ⥤ H')
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P) (cmp : P ⋙ R ⟶ S)
    (α : I ⋙ (J ⋙ R) ⟶ I ⋙ (K ⋙ S))
    (ha : α = assembleLiftNat (I ⋙ J) (I ⋙ K) P R S lift cmp)
    (p : S ⋙ T ⟶ TE ⋙ S') (q : K ⋙ TE ⟶ TC ⋙ K')
    (proj : (K ⋙ S) ⋙ T ⟶ TC ⋙ (K' ⋙ S'))
    (hp : proj = pasteScalar K S K' S' TC TE T p q)
    (M : B) (v : J.obj (I.obj M) ⟶ P.obj (K.obj (I.obj M)))
    (hv : lift.app M = v) :
    T.map (α.app M) ≫ proj.app (I.obj M) =
      T.map (R.map v) ≫ T.map (cmp.app (K.obj (I.obj M))) ≫
        p.app (K.obj (I.obj M)) ≫ S'.map (q.app (I.obj M)) := by
  rw [assembled_component I J K P R S lift cmp α ha M v hv, hp]
  rw [pasteScalar_app, T.map_comp]
  simp only [Category.assoc]

private theorem assembled_factorization
    {B C D E H C' D' E' H' : Type*}
    [Category B] [Category C] [Category D] [Category E] [Category H]
    [Category C'] [Category D'] [Category E'] [Category H']
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (S : E ⥤ H)
    (T : H ⥤ H') (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (K' : C' ⥤ E') (P' : E' ⥤ D') (R' : D' ⥤ H') (S' : E' ⥤ H')
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P) (cmp : P ⋙ R ⟶ S)
    (cmp' κ : P' ⋙ R' ⟶ S') (hκ : cmp' = κ)
    (α : I ⋙ (J ⋙ R) ⟶ I ⋙ (K ⋙ S))
    (ha : α = assembleLiftNat (I ⋙ J) (I ⋙ K) P R S lift cmp)
    (pR : R ⋙ T ⟶ TD ⋙ R') (pP : P ⋙ TD ⟶ TE ⋙ P')
    (pS : S ⋙ T ⟶ TE ⋙ S') (q : K ⋙ TE ⟶ TC ⋙ K')
    (hc : compositorLaw P R S P' R' S' TE TD T cmp cmp' pP pR pS)
    (proj : (K ⋙ S) ⋙ T ⟶ TC ⋙ (K' ⋙ S'))
    (hp : proj = pasteScalar K S K' S' TC TE T pS q)
    (M : B) (v : J.obj (I.obj M) ⟶ P.obj (K.obj (I.obj M)))
    (hv : lift.app M = v) :
    T.map (α.app M) ≫ proj.app (I.obj M) =
      pR.app (J.obj (I.obj M)) ≫
        R'.map (TD.map v ≫ pP.app (K.obj (I.obj M)) ≫
          P'.map (q.app (I.obj M))) ≫ κ.app (K'.obj (TC.obj (I.obj M))) := by
  have he := assembled_projection I J K P R S T TC TE K' S'
    lift cmp α ha pS q proj hp M v hv
  have hn := pR.naturality v
  have hq := cmp'.naturality (q.app (I.obj M))
  have hcM := compositorLaw_app P R S P' R' S' TE TD T cmp cmp' pP pR pS
    hc (K.obj (I.obj M))
  have h := he.trans ((paste_component hcM hn hq).trans
    (fold_map_three R' (TD.map v) (pP.app (K.obj (I.obj M)))
      (P'.map (q.app (I.obj M))) (pR.app (J.obj (I.obj M)))
      (cmp'.app (K'.obj (TC.obj (I.obj M))))))
  simpa only [hκ] using h

private theorem factorization_naturality
    {B C D E H C' D' E' H' : Type*}
    [Category B] [Category C] [Category D] [Category E] [Category H]
    [Category C'] [Category D'] [Category E'] [Category H']
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (T : H ⥤ H') (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (K' : C' ⥤ E') (P' : E' ⥤ D') (R' : D' ⥤ H') (S' : E' ⥤ H')
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P)
    (pR : R ⋙ T ⟶ TD ⋙ R') (pP : P ⋙ TD ⟶ TE ⋙ P')
    (q : K ⋙ TE ⟶ TC ⋙ K') (κ : P' ⋙ R' ⟶ S')
    {M N : B} (f : M ⟶ N) :
    ((I ⋙ (J ⋙ R)) ⋙ T).map f ≫ (pR.app (J.obj (I.obj N)) ≫
        R'.map (TD.map (lift.app N) ≫ pP.app (K.obj (I.obj N)) ≫
          P'.map (q.app (I.obj N))) ≫ κ.app (K'.obj (TC.obj (I.obj N)))) =
      (pR.app (J.obj (I.obj M)) ≫
        R'.map (TD.map (lift.app M) ≫ pP.app (K.obj (I.obj M)) ≫
          P'.map (q.app (I.obj M))) ≫ κ.app (K'.obj (TC.obj (I.obj M)))) ≫
        (I ⋙ (TC ⋙ (K' ⋙ S'))).map f := by
  let pasted : (I ⋙ (J ⋙ R)) ⋙ T ⟶ I ⋙ (TC ⋙ (K' ⋙ S')) :=
    Functor.whiskerLeft (I ⋙ J) pR ≫
      Functor.whiskerRight
        (Functor.whiskerRight lift TD ≫
          Functor.whiskerLeft I (pasteScalar K P K' P' TC TE TD pP q)) R' ≫
      Functor.whiskerLeft ((I ⋙ TC) ⋙ K') κ
  have h := pasted.naturality f
  simpa only [pasted, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, pasteScalar_app] using h

private def factorizationNat
    {B C D E H C' D' E' H' : Type*}
    [Category B] [Category C] [Category D] [Category E] [Category H]
    [Category C'] [Category D'] [Category E'] [Category H']
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (T : H ⥤ H') (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (K' : C' ⥤ E') (P' : E' ⥤ D') (R' : D' ⥤ H') (S' : E' ⥤ H')
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P)
    (pR : R ⋙ T ⟶ TD ⋙ R') (pP : P ⋙ TD ⟶ TE ⋙ P')
    (q : K ⋙ TE ⟶ TC ⋙ K') (κ : P' ⋙ R' ⟶ S') :
    (I ⋙ (J ⋙ R)) ⋙ T ⟶ I ⋙ (TC ⋙ (K' ⋙ S')) where
  app M := pR.app (J.obj (I.obj M)) ≫
        R'.map (TD.map (lift.app M) ≫ pP.app (K.obj (I.obj M)) ≫
          P'.map (q.app (I.obj M))) ≫ κ.app (K'.obj (TC.obj (I.obj M)))
  naturality _ _ f := factorization_naturality I J K P R T TC TD TE K' P' R' S' lift pR pP q κ f

private theorem factorizationNat_app
    {B C D E H C' D' E' H' : Type*}
    [Category B] [Category C] [Category D] [Category E] [Category H]
    [Category C'] [Category D'] [Category E'] [Category H']
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (T : H ⥤ H') (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (K' : C' ⥤ E') (P' : E' ⥤ D') (R' : D' ⥤ H') (S' : E' ⥤ H')
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P)
    (pR : R ⋙ T ⟶ TD ⋙ R') (pP : P ⋙ TD ⟶ TE ⋙ P')
    (q : K ⋙ TE ⟶ TC ⋙ K') (κ : P' ⋙ R' ⟶ S') (M : B) :
    (factorizationNat I J K P R T TC TD TE K' P' R' S' lift pR pP q κ).app M =
      pR.app (J.obj (I.obj M)) ≫
        R'.map (TD.map (lift.app M) ≫ pP.app (K.obj (I.obj M)) ≫
          P'.map (q.app (I.obj M))) ≫ κ.app (K'.obj (TC.obj (I.obj M))) := by
  rfl

private theorem assembled_factorization_nat
    {B C D E H C' D' E' H' : Type*}
    [Category B] [Category C] [Category D] [Category E] [Category H]
    [Category C'] [Category D'] [Category E'] [Category H']
    (I : B ⥤ C) (J : C ⥤ D) (K : C ⥤ E) (P : E ⥤ D)
    (R : D ⥤ H) (S : E ⥤ H)
    (T : H ⥤ H') (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (K' : C' ⥤ E') (P' : E' ⥤ D') (R' : D' ⥤ H') (S' : E' ⥤ H')
    (lift : I ⋙ J ⟶ (I ⋙ K) ⋙ P) (cmp : P ⋙ R ⟶ S)
    (cmp' κ : P' ⋙ R' ⟶ S') (hκ : cmp' = κ)
    (α : I ⋙ (J ⋙ R) ⟶ I ⋙ (K ⋙ S))
    (ha : α = assembleLiftNat (I ⋙ J) (I ⋙ K) P R S lift cmp)
    (pR : R ⋙ T ⟶ TD ⋙ R') (pP : P ⋙ TD ⟶ TE ⋙ P')
    (pS : S ⋙ T ⟶ TE ⋙ S') (q : K ⋙ TE ⟶ TC ⋙ K')
    (hc : compositorLaw P R S P' R' S' TE TD T cmp cmp' pP pR pS)
    (proj : (K ⋙ S) ⋙ T ⟶ TC ⋙ (K' ⋙ S'))
    (hp : proj = pasteScalar K S K' S' TC TE T pS q)
    : Functor.whiskerRight α T ≫ Functor.whiskerLeft I proj =
      factorizationNat I J K P R T TC TD TE K' P' R' S' lift pR pP q κ := by
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    factorizationNat_app]
  exact assembled_factorization I J K P R S T TC TD TE K' P' R' S'
    lift cmp cmp' κ hκ α ha pR pP pS q hc proj hp M (lift.app M) rfl

private theorem natApp_heq_all
    {B B' : Type x} {E E' : Type y}
    [b : Category.{v} B] [b' : Category.{v} B']
    [e : Category.{w} E] [e' : Category.{w} E']
    {F G : B ⥤ E} {F' G' : B' ⥤ E'}
    (α : F ⟶ G) (β : F' ⟶ G') (M : B) (N : B')
    (hB : B = B') (hE : E = E') (hb : HEq b b') (he : HEq e e')
    (hF : HEq F F') (hG : HEq G G') (hα : HEq α β) (hM : HEq M N) :
    HEq (α.app M) (β.app N) := by
  cases hB
  cases hE
  cases hb
  cases he
  cases hF
  cases hG
  cases hα
  cases hM
  rfl

private def nativeProjectionPart {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  restrictNat (condensedProjection a c) (constructibleInclusion Λ X)

private def nativeLeft {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :=
  preWhisker (fieldRefinement Λ r) (condensedScalar a Y) ≫ nativeProjectionPart a c

private def rawRight {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :=
  factorizationNat (C := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (constructibleInclusion Λ X)
    (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (condensedScalar a Y) (condensedScalar a X)
    (condensedScalar a d.Z) (condensedScalar a c.Z)
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor
    (fieldDerivedLowerStar Λ' c.g)
    (properOpenNatRaw (Λ := Λ) r) (condensedPushScalar a d.g)
    (condensedPushScalar a r.hom) (condensedOpenScalar a c.i).hom
    ((fieldPushComp Λ' r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g))

private theorem rawRight_app {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    type_of% (factorizationNat_app (C := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (constructibleInclusion Λ X)
    (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (condensedScalar a Y) (condensedScalar a X)
    (condensedScalar a d.Z) (condensedScalar a c.Z)
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor
    (fieldDerivedLowerStar Λ' c.g)
    (properOpenNatRaw (Λ := Λ) r) (condensedPushScalar a d.g)
    (condensedPushScalar a r.hom) (condensedOpenScalar a c.i).hom
    ((fieldPushComp Λ' r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g)) K) :=
  factorizationNat_app (C := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (constructibleInclusion Λ X)
    (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (condensedScalar a Y) (condensedScalar a X)
    (condensedScalar a d.Z) (condensedScalar a c.Z)
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor
    (fieldDerivedLowerStar Λ' c.g)
    (properOpenNatRaw (Λ := Λ) r) (condensedPushScalar a d.g)
    (condensedPushScalar a r.hom) (condensedOpenScalar a c.i).hom
    ((fieldPushComp Λ' r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g)) K

private def nativeRight {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) : type_of% (nativeLeft a r) :=
  rawRight a r

private theorem refinement_eq_assemble {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    type_of% ((refinementNatRaw_eq_refinement (Λ := Λ) r).symm.trans
      (refinementNatRaw_eq_assemble (Λ := Λ) r)) :=
  (refinementNatRaw_eq_refinement (Λ := Λ) r).symm.trans
    (refinementNatRaw_eq_assemble (Λ := Λ) r)

-- Freeze this functor presentation before supplying the next transformation.

private theorem factorization_functors {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (_K : BoundedConstructible (condensedRingObj Λ X)) :
    type_of% (assembled_factorization_nat
    (C := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (constructibleInclusion Λ X)
    (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (condensedScalar a Y) (condensedScalar a X)
    (condensedScalar a d.Z) (condensedScalar a c.Z)
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor
    (fieldDerivedLowerStar Λ' c.g)
    (properOpenNatRaw (Λ := Λ) r) (properCompRaw (Λ := Λ) r.hom d.g r.hom_g)
    (properCompRaw (Λ := Λ') r.hom d.g r.hom_g)
    ((fieldPushComp Λ' r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g))
    (properCompRaw_eq (Λ := Λ') r.hom d.g r.hom_g)) :=
  assembled_factorization_nat (C := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (constructibleInclusion Λ X)
    (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (condensedScalar a Y) (condensedScalar a X)
    (condensedScalar a d.Z) (condensedScalar a c.Z)
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor
    (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor
    (fieldDerivedLowerStar Λ' c.g)
    (properOpenNatRaw (Λ := Λ) r) (properCompRaw (Λ := Λ) r.hom d.g r.hom_g)
    (properCompRaw (Λ := Λ') r.hom d.g r.hom_g)
    ((fieldPushComp Λ' r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g))
    (properCompRaw_eq (Λ := Λ') r.hom d.g r.hom_g)

-- Freeze this functor presentation before supplying the next transformation.

private theorem factorization_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    type_of% (factorization_functors a r K
    (fieldRefinement Λ r) (refinement_eq_assemble (Λ := Λ) r)) :=
  factorization_functors a r K
    (fieldRefinement Λ r) (refinement_eq_assemble (Λ := Λ) r)

-- Freeze this functor presentation before supplying the next transformation.

private theorem factorization_mates {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    type_of% (factorization_refinement a r K
    (condensedPushScalar a d.g) (condensedPushScalar a r.hom)
    (condensedPushScalar a c.g) (condensedOpenScalar a c.i).hom) :=
  factorization_refinement a r K
    (condensedPushScalar a d.g) (condensedPushScalar a r.hom)
    (condensedPushScalar a c.g) (condensedOpenScalar a c.i).hom

-- Freeze this functor presentation before supplying the next transformation.

private theorem factorization_compositor {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    type_of% (factorization_mates a r K (pushScalar_comp_transport_raw a r.hom d.g r.hom_g)) :=
  factorization_mates a r K (pushScalar_comp_transport_raw a r.hom d.g r.hom_g)

-- Freeze this functor presentation before supplying the next transformation.

private theorem factorization_projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    type_of% (factorization_compositor a r K (condensedProjection a c) (projection_eq_paste a c)) :=
  factorization_compositor a r K (condensedProjection a c) (projection_eq_paste a c)

private theorem native_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    nativeLeft a r = nativeRight a r := by
  with_unfolding_all exact factorization_projection a r K

/-- The proper coefficient square pasted with a compactification refinement.

Source: the proper-image mate pasting of compact-support realization Steps 15--16
(blueprint: lem-pur-condensed-push-scalar-composition).

Proof: the refinement component is the proper direct image of its normalized
open lift, followed by the pushforward compositor transported along `r.hom_g`.
The projection component is the proper scalar mate followed by the proper image
of the open scalar comparison. Expand these two component formulas and apply
functoriality of scalar extension. The proper scalar mate respects composition
of direct images: on the restriction side, both underived pastes are the same
section map, with the same coefficient action by coefficient naturality. Derive
this identity using the canonical right-derived comparisons; exact coefficient
restriction preserves K-injective complexes because its scalar-extension left
adjoint is exact. Uniqueness identifies these comparisons with the right-adjoint
mates of the pullback compositors, namely `fieldPushComp`. Taking scalar mates
therefore gives the proper coefficient compositor square. Transport it along
`r.hom_g` by equality induction. Substitute it into the expanded refinement
component. Naturality of `condensedPushScalar a d.g` moves the scalar image of
the normalized lift past that mate. Naturality of the target compositor in the
open scalar comparison moves that comparison before the compositor. Finally
combine the three maps inside the final proper direct image by functoriality.
This gives exactly the displayed paste. No scalar-extended constructibility
hypothesis or coefficient compatibility of the normalized lift is used here. -/
theorem condensedPushScalar_refinement_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (condensedScalar a Y).map ((fieldRefinement Λ r).app K) ≫
        (condensedProjection a c).app K.obj =
      (condensedPushScalar a d.g).app
          ((CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj) ≫
        (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map
          ((condensedScalar a d.Z).map (fieldProperOpen Λ r K) ≫
            (condensedPushScalar a r.hom).app
              ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
            (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor.map
              ((condensedOpenScalar a c.i).hom.app K.obj)) ≫
        ((fieldPushComp Λ' r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g)).app
            ((CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory.obj
              ((condensedScalar a X).obj K.obj)) := by
  have h := congrArg (fun (z : type_of% (nativeLeft a r)) => z.1 K)
    (native_factorization a r K)
  have hr := rawRight_app a r K
  refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq h)
    (HEq.trans ?_ (HEq.trans (heq_of_eq hr) ?_))))
  · with_unfolding_all rfl
  -- Preserve both category presentations before evaluating a component.
  · run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← Lean.instantiateMVars (← goal.getType)
      let some (_, lhs, _, rhs) := target.heq? | throwError "not HEq"
      let unpack (z : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
        let z := z.consumeMData
        let args := z.getAppArgs
        let fn := z.getAppFn
        let (α, M) ← match fn with
          | .proj ``NatTrans 0 α => pure (α, args[0]!)
          | .const ``NatTrans.app _ => pure (args[args.size - 2]!, args[args.size - 1]!)
          | _ => throwError "not a component: {fn}"
        let ty ← Lean.Meta.whnf (← Lean.Meta.inferType α)
        unless ty.getAppFn.isConstOf ``NatTrans do
          throwError "not NatTrans: {ty}"
        return ty.getAppArgs ++ #[α, M]
      let l ← unpack lhs
      let r ← unpack rhs
      let transport ← Lean.Meta.mkConstWithFreshMVarLevels ``natApp_heq_all
      let proof := Lean.mkAppN transport #[l[0]!, r[0]!, l[2]!, r[2]!,
        l[1]!, r[1]!, l[3]!, r[3]!, l[4]!, l[5]!, r[4]!, r[5]!,
        l[6]!, r[6]!, l[7]!, r[7]!]
      let goals ← goal.apply proof { synthAssignedInstances := false }
      Lean.Elab.Tactic.setGoals goals
    all_goals with_unfolding_all rfl
  -- Keep instance arguments in congruence, transporting the structures before their objects.
  · dsimp only [Functor.comp_obj]
    run_tac
      let mut pending := (← Lean.Elab.Tactic.getGoals).toArray
      let mut leaves : Array Lean.MVarId := #[]
      for _ in [:16] do
        if pending.isEmpty then break
        let mut next : Array Lean.MVarId := #[]
        for goal in pending do
          let (more, stuck) ← goal.withContext do
            if ← goal.isAssigned then return (#[], #[])
            let (_, goal) ← goal.intros
            let goal ← goal.eqOfHEq
            let target ← Lean.instantiateMVars (← goal.getType)
            let some (_, lhs, _, rhs) := target.heq? | return (#[], #[goal])
            let lhs := lhs.consumeMData
            let rhs := rhs.consumeMData
            if lhs == rhs then
              goal.hrefl
              return (#[], #[])
            if (← Lean.Meta.isProof lhs) && (← Lean.Meta.isProof rhs) then
              if ← goal.proofIrrelHeq then return (#[], #[])
            let lhsType ← Lean.Meta.inferType lhs
            let fn := lhs.getAppFn
            let args := lhs.getAppArgs
            if lhsType.isSort || lhsType.getAppFn.isConstOf ``CategoryTheory.Functor ||
                lhsType.getAppFn.isConstOf ``NatTrans ||
                (Lean.isClass (← Lean.getEnv) lhsType.getAppFn.constName!) ||
                fn != rhs.getAppFn || args.isEmpty || args.size != rhs.getAppNumArgs then
              let closed ← Lean.observing? do
                Lean.Meta.withTransparency .all <| goal.hrefl
              if closed.isSome then return (#[], #[])
              return (#[], #[goal])
            let result ← Lean.observing? do
              let cthm ← Lean.Meta.mkHCongrWithArity fn args.size
              goal.apply cthm.proof { synthAssignedInstances := false }
            match result with
            | some goals => return (goals.toArray, #[])
            | none => return (#[], #[goal])
          next := next ++ more
          leaves := leaves ++ stuck
        pending := next
      let remaining := leaves ++ pending
      Lean.Elab.Tactic.setGoals remaining.toList

end WeilConjectures.CompactSupportCondensedRealization
