/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperOpenLaws
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionMixed
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor upperStarComp lowerStarComp
  upperStarLowerStarAdjunction
structure MateLaws (openData : OpenLaws Λ) where
  restriction_isIso : ∀ {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    (sq : CommSq j p r i), IsAdmissibleSquare j p r i → IsIso (restriction Λ openData.units sq)
  /-- Vertical mixed pasting, with canonical direct-image compositors at both ends. -/
  gamma_vertical : ∀ {U W Y Z V T : Scheme.{u}}
    {j : U ⟶ W} {i : Y ⟶ Z} {k : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k)
    (_h₁ : IsAdmissibleSquare j p₁ r₁ i) (_h₂ : IsAdmissibleSquare i p₂ r₂ k)
    (K : D Λ U),
    (gamma Λ openData.units q).app K =
      (J Λ k).map ((rComp Λ p₁ p₂).inv.app K) ≫
      (gamma Λ openData.units q₂).app ((R Λ p₁).obj K) ≫
      (R Λ r₂).map ((gamma Λ openData.units q₁).app K) ≫
      (rComp Λ r₁ r₂).hom.app ((J Λ j).obj K)
  /-- Horizontal mixed pasting, with canonical open compositors at both ends. -/
  gamma_horizontal : ∀ {U W V Y Z T : Scheme.{u}}
    {j₁ : U ⟶ W} {j₂ : W ⟶ V} {i₁ : Y ⟶ Z} {i₂ : Z ⟶ T}
    {p : U ⟶ Y} {r : W ⟶ Z} {s : V ⟶ T}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact j₁] [QuasiCompact j₂] [QuasiCompact i₁] [QuasiCompact i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂))
    (_h₁ : IsAdmissibleSquare j₁ p r i₁) (_h₂ : IsAdmissibleSquare j₂ r s i₂)
    (K : D Λ U),
    (gamma Λ openData.units q).app K =
      (jComp Λ i₁ i₂).inv.app ((R Λ p).obj K) ≫
      (J Λ i₂).map ((gamma Λ openData.units q₁).app K) ≫
      (gamma Λ openData.units q₂).app ((J Λ j₁).obj K) ≫
      (R Λ s).map ((jComp Λ j₁ j₂).hom.app K)
  /-- Identity vertical morphisms give identity comparisons. -/
  gamma_vertical_id : ∀ {U W : Scheme.{u}} (j : U ⟶ W)
    [IsOpenImmersion j] [QuasiCompact j] (sq : CommSq j (𝟙 U) (𝟙 W) j)
    (K : D Λ U),
    (gamma Λ openData.units sq).app K =
      (J Λ j).map ((rId Λ U).hom.app K) ≫ (rId Λ W).inv.app ((J Λ j).obj K)
  /-- Identity horizontal opens give identity comparisons. -/
  gamma_horizontal_id : ∀ {U Y : Scheme.{u}} (p : U ⟶ Y)
    (sq : CommSq (𝟙 U) p p (𝟙 Y)) (K : D Λ U),
    (gamma Λ openData.units sq).app K =
      (jId Λ Y).hom.app ((R Λ p).obj K) ≫ (R Λ p).map ((jId Λ U).inv.app K)
  /-- Arbitrary-base-change cube (c), on all unbounded objects and without inverting Ex. -/
  cube : ∀ {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact j'] [QuasiCompact i']
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (_hQ : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) (K : D Λ U),
    (P Λ b).map ((gamma Λ openData.units q).app K) ≫
      (derivedDirectImageOpenRestriction Λ qr.toCommSq).app ((J Λ j).obj K) ≫
      (R Λ r').map ((openData.B qj).hom.app K) =
    (openData.B qi).hom.app ((R Λ p).obj K) ≫
      (J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K) ≫
      (gamma Λ openData.units q').app ((P Λ aU).obj K)


private abbrev Q {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar Λ f).rightDerivedFunctor

-- These proof-local aliases expose the same endpoints as the native derived adjunctions.
private def RC {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Q Λ f ⋙ Q Λ g ≅ Q Λ (f ≫ g) := rComp Λ f g

private def RI (X : Scheme.{u}) : Q Λ (𝟙 X) ≅ 𝟭 (D Λ X) := rId Λ X

private def L (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] (sq : CommSq j p r i) :
    (J Λ j ⋙ Q Λ r) ⋙ P Λ i ⟶ Q Λ p :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J Λ j) (derivedDirectImageOpenRestriction Λ sq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (units.unitIso j).inv (Q Λ p) ≫ (Functor.leftUnitor _).hom

private def G (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i) :
    Q Λ p ⋙ J Λ i ⟶ J Λ j ⋙ Q Λ r :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (comparisonInverse (L Λ units sq)) (J Λ i) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J Λ j ⋙ Q Λ r)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).counit ≫
    (Functor.rightUnitor _).hom

private theorem identity_square_normalize
    {C E : Type*} [Category C] [Category E]
    (F H₀ H₁ : C ⥤ E) {I₀ : C ⥤ C} {I₁ : E ⥤ E}
    (e₀ : I₀ ≅ 𝟭 C) (e₁ : I₁ ≅ 𝟭 E)
    (h₀ : H₀ = F) (h₁ : H₁ = F) (hw : H₀ = H₁) :
    (eqToIso h₀ ≪≫ F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight e₀.symm F).symm ≪≫
        eqToIso hw ≪≫ eqToIso h₁ ≪≫ F.rightUnitor.symm ≪≫
          Functor.isoWhiskerLeft F e₁.symm =
      Functor.isoWhiskerRight e₀ F ≪≫ Functor.isoWhiskerLeft F e₁.symm := by
  subst H₀ H₁
  apply Iso.ext
  ext M
  simp

private theorem ordinarySquare_id
    {U Y : Scheme.{u}} (p : U ⟶ Y) (sq : CommSq (𝟙 U) p p (𝟙 Y)) :
    openCoherencePullbackSquare Λ sq =
      Functor.isoWhiskerRight (upperStarId Λ Y) (upperStar Λ p) ≪≫
        Functor.isoWhiskerLeft (upperStar Λ p) (upperStarId Λ U).symm := by
  simpa only [openCoherencePullbackSquare, upperStarComp_id_left,
    upperStarComp_id_right, upperStarCongr] using
    identity_square_normalize (upperStar Λ p) _ _ (upperStarId Λ Y) (upperStarId Λ U)
      (congrArg (upperStar Λ) (Category.comp_id p))
      (congrArg (upperStar Λ) (Category.id_comp p))
      (congrArg (upperStar Λ) sq.w.symm)

private theorem ordinarySquare_flip
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq j p r i) :
    openCoherencePullbackSquare Λ sq.flip = (openCoherencePullbackSquare Λ sq).symm := by
  apply Iso.ext
  simp only [openCoherencePullbackSquare, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv, Category.assoc]

private theorem derivedSquare_flip
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq j p r i) :
    derivedOpenCoherencePullbackSquare Λ sq.flip =
      (derivedOpenCoherencePullbackSquare Λ sq).symm := by
  change (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (openCoherencePullbackSquare Λ sq.flip) ≪≫
      Functor.mapDerivedCategoryCompIso _ _ = _
  rw [ordinarySquare_flip Λ sq]
  apply Iso.ext
  simp only [derivedOpenCoherencePullbackSquare, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem mate_identity_square
    {C E : Type*} [Category C] [Category E]
    {F : C ⥤ E} {G : E ⥤ C} (a : F ⊣ G)
    {I₀ : C ⥤ C} {I₁ : E ⥤ E} (e₀ : I₀ ≅ 𝟭 C) (e₁ : I₁ ≅ 𝟭 E) :
    (mateEquiv a a (TwoSquare.mk _ _ _ _
      (Functor.isoWhiskerRight e₀ F ≪≫ Functor.isoWhiskerLeft F e₁.symm).hom)).natTrans =
      Functor.whiskerLeft G e₀.hom ≫ Functor.whiskerRight e₁.inv G := by
  let t := TwoSquare.mk (𝟭 C) F F (𝟭 E)
    ((Functor.leftUnitor F).hom ≫ (Functor.rightUnitor F).inv)
  have he : TwoSquare.mk _ _ _ _
      (Functor.isoWhiskerRight e₀ F ≪≫ Functor.isoWhiskerLeft F e₁.symm).hom =
        (t.whiskerTop e₀.hom).whiskerBottom e₁.inv := by
    ext M
    simp [t, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  rw [he, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]
  ext M
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

private theorem derived_identity_square
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    (F : C ⥤ E) (I₀ : C ⥤ C) (I₁ : E ⥤ E)
    [F.Additive] [I₀.Additive] [I₁.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits I₀] [PreservesFiniteColimits I₀]
    [PreservesFiniteLimits I₁] [PreservesFiniteColimits I₁]
    (e₀ : I₀ ≅ 𝟭 C) (e₁ : I₁ ≅ 𝟭 E) :
    (Functor.mapDerivedCategoryCompIso I₀ F).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.isoWhiskerRight e₀ F ≪≫ Functor.isoWhiskerLeft F e₁.symm) ≪≫
        Functor.mapDerivedCategoryCompIso F I₁ =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso e₀ ≪≫ Functor.mapDerivedCategoryIdIso C)
        F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e₁ ≪≫ Functor.mapDerivedCategoryIdIso E).symm := by
  have hr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e₀ F
  have hl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e₁.symm
  have hu := Functor.mapDerivedCategoryCompIso_id_comp F
  have hv := Functor.mapDerivedCategoryCompIso_comp_id F
  have hr' := congrArg (fun t ↦ (Functor.mapDerivedCategoryCompIso I₀ F).inv ≫ t ≫
    Functor.whiskerRight (Functor.mapDerivedCategoryIdIso C).hom F.mapDerivedCategory) hr
  simp only [Category.assoc, hu, Iso.inv_hom_id_assoc] at hr'
  erw [Category.comp_id] at hr'
  have hv' : (Functor.mapDerivedCategoryCompIso F (𝟭 E)).hom =
      Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryIdIso E).inv := by
    apply (cancel_mono
      (Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryIdIso E).hom)).1
    rw [hv]
    ext M
    simp
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc, hl, hv', ← hr',
    Functor.whiskerRight_comp, Functor.whiskerLeft_comp]

private theorem derivedSquare_id
    {U Y : Scheme.{u}} (p : U ⟶ Y) (sq : CommSq (𝟙 U) p p (𝟙 Y)) :
    derivedOpenCoherencePullbackSquare Λ sq =
      Functor.isoWhiskerRight (pId Λ Y) (P Λ p) ≪≫
        Functor.isoWhiskerLeft (P Λ p) (pId Λ U).symm := by
  rw [derivedOpenCoherencePullbackSquare, ordinarySquare_id]
  exact derived_identity_square (upperStar Λ p) _ _ _ _

private theorem restrictionExchange_id
    {U Y : Scheme.{u}} (p : U ⟶ Y) (sq : CommSq (𝟙 U) p p (𝟙 Y)) :
    derivedDirectImageOpenRestriction Λ sq =
      Functor.whiskerLeft (Q Λ p) (pId Λ Y).hom ≫
        Functor.whiskerRight (pId Λ U).inv (Q Λ p) := by
  rw [derivedDirectImageOpenRestriction, derivedSquare_id]
  exact mate_identity_square _ _ _

private theorem restrictionExchange_vertical_id
    {U W : Scheme.{u}} (j : U ⟶ W) (sq : CommSq j (𝟙 U) (𝟙 W) j) (M : D Λ W) :
    (derivedDirectImageOpenRestriction Λ sq).app M ≫
      (RI Λ U).hom.app ((P Λ j).obj M) = (P Λ j).map ((RI Λ W).hom.app M) := by
  have hs := derivedSquare_id Λ j sq.flip
  rw [derivedSquare_flip Λ sq] at hs
  have ha (N : D Λ W) :
      (derivedOpenCoherencePullbackSquare Λ sq).hom.app N ≫
        (P Λ j).map ((pId Λ W).hom.app N) = (pId Λ U).hom.app ((P Λ j).obj N) := by
    have he := congrArg (fun e ↦ e.inv.app N) hs
    simp only [Iso.symm_inv, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app] at he
    rw [he, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hh := mate_identity_vertical
    (upperStarLowerStarAdjunction Λ (𝟙 W)).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ (𝟙 U)).mapDerivedCategoryRightDerivedAdjunction
    (pId Λ W) (pId Λ U) (P Λ j)
    (derivedOpenCoherencePullbackSquare Λ sq).hom ha M
  simpa only [RI, rId, conjugateIsoEquiv_iso_symm, derivedDirectImageOpenRestriction] using hh

private theorem restrictionExchange_horizontal
    {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {j : Y' ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X}
    {j' : Y'' ⟶ Y'} {f'' : X'' ⟶ Y''} {i' : X'' ⟶ X'}
    (sq : CommSq i f' f j) (sq' : CommSq i' f'' f' j') :
    DirectImageSuccessiveRestriction Λ sq sq' := by
  have h := exactSquare_horiz_inv Λ sq sq'
  rw [exactSquare_eq, exactSquare_eq, exactSquare_eq, exactComp_eq, exactComp_eq] at h
  have hm := congrArg (fun α ↦ (mateEquiv
    (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ f'').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ α)).natTrans) h
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _
    (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction] at hm
  intro K
  have hc := NatTrans.congr_app hm K
  simpa only [derivedDirectImageOpenRestriction, Iso.symm_inv, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hc.symm

private theorem exactNatIso_change
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ) hfg) ≪≫ upperStarComp Λ f g) =
      eqToIso (congrArg (fun h ↦ P Λ h) hfg) ≪≫
        Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g) := by
  subst fg
  simp only [eqToIso_refl, Iso.refl_trans]

private theorem pComp_assoc
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (K : D Λ Z) :
    (pComp Λ (f ≫ g) h).hom.app K ≫
        (pComp Λ f g).hom.app ((P Λ h).obj K) =
      eqToHom (congrArg (fun a ↦ (P Λ a).obj K) (Category.assoc f g h)) ≫
        (pComp Λ f (g ≫ h)).hom.app K ≫
        (P Λ f).map ((pComp Λ g h).hom.app K) := by
  have hh := NatTrans.congr_app
    (exactComp_assoc Λ f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl) K
  simp only [exactComp, ordinaryComp, Functor.mapDerivedCategoryTriangleIso] at hh
  rw [exactNatIso_change Λ f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)] at hh
  simp only [exactNatIso_change, Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, eqToIso.hom, Functor.comp_obj,
    eqToHom_refl, Category.id_comp,
    Category.assoc] at hh
  simpa only [pComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    eqToHom_refl, Category.id_comp] using hh.symm

private theorem pComp_square
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq j p r i) :
    derivedOpenCoherencePullbackSquare Λ sq =
      (pComp Λ p i).symm ≪≫ eqToIso (congrArg (fun a ↦ P Λ a) sq.w.symm) ≪≫
        pComp Λ j r := by
  have hh := congrArg Iso.inv (exactSquare_eq Λ sq)
  simp only [exactSquare, exactComp, ordinaryComp,
    Functor.mapDerivedCategoryTriangleIso] at hh
  rw [exactNatIso_change Λ p i (j ≫ r) sq.w] at hh
  simp only [exactNatIso_change, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp] at hh
  apply Iso.ext
  simpa only [pComp, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    eqToIso.hom, Category.assoc] using hh.symm

private lemma exactCube_trans_eqToIso_trans_hom_app {C D : Type*} [Category C] [Category D]
    {F F' G H : C ⥤ D} (α : G ≅ F) (h : F = F') (β : F' ≅ H) (K : C) :
    (α ≪≫ eqToIso h ≪≫ β).hom.app K =
      α.hom.app K ≫ eqToHom (Functor.congr_obj h K) ≫ β.hom.app K := by
  subst h
  simp


private lemma exactCube_map_comp_map_aux {C D : Type*} {_ : Category C} {_ : Category D} (H : D ⥤ C)
    {y₀ y₁ y₂ y₃ : D} (c₁ : y₀ ⟶ y₁) (c₁' : y₁ ⟶ y₀) (hc₁ : c₁ ≫ c₁' = 𝟙 _) (θ : y₁ ⟶ y₃)
    (E : y₀ ⟶ y₂) (c₂ : y₂ ⟶ y₃) (hθ : θ = c₁' ≫ E ≫ c₂) :
    H.map c₁ ≫ H.map θ = H.map E ≫ H.map c₂ := by
  rw [hθ, ← H.map_comp, reassoc_of% hc₁, H.map_comp]

/-- The diagram chase behind `map_pullbackSquareComparison_hom_app`. -/
private lemma exactCube_map_square_aux {C : Type*} {_ : Category C} {x₀ x₁ w₀ w₁ w₂ w₃ : C}
    (c₀ : x₀ ⟶ w₀) (m₁ : w₀ ⟶ w₁) (mθ : w₁ ⟶ w₃) (mE : w₀ ⟶ w₂) (m₂ : w₂ ⟶ w₃)
    (hm : m₁ ≫ mθ = mE ≫ m₂) (E' : x₀ ⟶ x₁) (c₀' : x₁ ⟶ w₂) (hN : c₀ ≫ mE = E' ≫ c₀') :
    c₀ ≫ m₁ ≫ mθ = E' ≫ c₀' ≫ m₂ := by
  rw [hm, reassoc_of% hN]

/-- The diagram chase behind `pullbackSquareComparison_hom_app_obj`. -/
private lemma exactCube_square_app_obj_aux {C : Type*} [Category C]
    {u₁ u₂ u₃ u₄ v₁ v₂ w₁ w₂ z₁ z₂ : C} (p₁₂ : u₁ = u₂) (p₁₃ : u₁ = u₃) (p₃₄ : u₃ = u₄)
    (p₂₄ : u₂ = u₄) (m₁ : u₂ ⟶ v₁) (m₂ : v₁ ⟶ z₁) (a₁ : u₁ ⟶ w₁) (a₂ : w₁ ⟶ z₁)
    (a₂' : z₁ ⟶ w₁) (ha₂ : a₂ ≫ a₂' = 𝟙 _)
    (A₁ : a₁ ≫ a₂ = eqToHom p₁₂ ≫ m₁ ≫ m₂) (θ : z₁ ⟶ z₂) (E₃ : w₁ ⟶ w₂) (b₁ : u₃ ⟶ w₂)
    (b₂ : w₂ ⟶ z₂) (hθ : θ = a₂' ≫ E₃ ≫ b₂) (N : a₁ ≫ E₃ = eqToHom p₁₃ ≫ b₁)
    (n₁ : u₄ ⟶ v₂) (n₂ : v₂ ⟶ z₂) (A₂ : b₁ ≫ b₂ = eqToHom p₃₄ ≫ n₁ ≫ n₂) :
    m₁ ≫ m₂ ≫ θ = eqToHom p₂₄ ≫ n₁ ≫ n₂ := by
  have h : m₁ ≫ m₂ = eqToHom p₁₂.symm ≫ a₁ ≫ a₂ := by
    rw [A₁]
    simp
  rw [reassoc_of% h, hθ, reassoc_of% ha₂, reassoc_of% N, A₂]
  simp

/-- The diagram chase behind `pullbackSquareComparison_cube`: six morphisms `t₁, …, t₆` (the
triple composition isomorphisms of the six paths through the cube) related by the faces. -/
private lemma exactCube_cube_aux {C : Type*} [Category C]
    {o₁ o₂ o₃ o₄ o₅ o₆ v₁ v₂ v₃ v₄ v₅ v₆ y₁ y₂ y₃ y₄ y₅ y₆ : C}
    (t₁ : o₁ ⟶ v₁) (t₁' : v₁ ⟶ y₁) [IsIso t₁] [IsIso t₁'] (t₂ : o₂ ⟶ v₂) (t₂' : v₂ ⟶ y₂)
    (t₃ : o₃ ⟶ v₃) (t₃' : v₃ ⟶ y₃) (t₄ : o₄ ⟶ v₄) (t₄' : v₄ ⟶ y₄)
    (t₅ : o₅ ⟶ v₅) (t₅' : v₅ ⟶ y₅) (t₆ : o₆ ⟶ v₆) (t₆' : v₆ ⟶ y₆)
    (p₁₂ : o₁ = o₂) (p₂₃ : o₂ = o₃) (p₃₄ : o₃ = o₄) (p₁₅ : o₁ = o₅) (p₅₆ : o₅ = o₆)
    (p₆₄ : o₆ = o₄) (θ₁ : y₁ ⟶ y₂) (θ₂ : y₂ ⟶ y₃) (θ₃ : y₃ ⟶ y₄) (θ₄ : y₁ ⟶ y₅)
    (θ₅ : y₅ ⟶ y₆) (θ₆ : y₆ ⟶ y₄)
    (h₁ : t₁ ≫ t₁' ≫ θ₁ = eqToHom p₁₂ ≫ t₂ ≫ t₂') (h₂ : t₂ ≫ t₂' ≫ θ₂ = eqToHom p₂₃ ≫ t₃ ≫ t₃')
    (h₃ : t₃ ≫ t₃' ≫ θ₃ = eqToHom p₃₄ ≫ t₄ ≫ t₄') (h₄ : t₁ ≫ t₁' ≫ θ₄ = eqToHom p₁₅ ≫ t₅ ≫ t₅')
    (h₅ : t₅ ≫ t₅' ≫ θ₅ = eqToHom p₅₆ ≫ t₆ ≫ t₆')
    (h₆ : t₆ ≫ t₆' ≫ θ₆ = eqToHom p₆₄ ≫ t₄ ≫ t₄') :
    θ₁ ≫ θ₂ ≫ θ₃ = θ₄ ≫ θ₅ ≫ θ₆ := by
  rw [← cancel_epi t₁', ← cancel_epi t₁, reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄,
    reassoc_of% h₅, h₆]
  simp

private theorem pComp_congr_right
    {R S T : Scheme.{u}} (a : R ⟶ S) {h h' : S ⟶ T} (e : h = h') (K : D Λ T) :
    (pComp Λ a h).hom.app K ≫
        (P Λ a).map (eqToHom (congrArg (fun f ↦ (P Λ f).obj K) e)) =
      eqToHom (congrArg (fun f ↦ (P Λ f).obj K) (congrArg (a ≫ ·) e)) ≫
        (pComp Λ a h').hom.app K := by
  subst e
  rw [eqToHom_refl, eqToHom_refl, (P Λ a).map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem pComp_congr_left
    {R S T : Scheme.{u}} {h h' : R ⟶ S} (e : h = h') (b : S ⟶ T) (K : D Λ T) :
    (pComp Λ h b).hom.app K ≫
        eqToHom (congrArg (fun f ↦ (P Λ f).obj ((P Λ b).obj K)) e) =
      eqToHom (congrArg (fun f ↦ (P Λ f).obj K) (congrArg (· ≫ b) e)) ≫
        (pComp Λ h' b).hom.app K := by
  subst e
  rw [eqToHom_refl, eqToHom_refl]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem exactCube_comparison_hom_app
    {C E : Type*} [Category C] [Category E]
    {F F' G H : C ⥤ E} {e : G ≅ H}
    (α : G ≅ F) (h : F = F') (β : F' ≅ H)
    (he : e = α ≪≫ eqToIso h ≪≫ β) (K : C) :
    e.hom.app K = α.hom.app K ≫ eqToHom (Functor.congr_obj h K) ≫ β.hom.app K := by
  rw [he]
  exact exactCube_trans_eqToIso_trans_hom_app α h β K

private theorem exactSquare_hom_app
    {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g) (K : D Λ Y) :
    (derivedOpenCoherencePullbackSquare Λ sq).hom.app K =
      (pComp Λ p' g).inv.app K ≫
        eqToHom (congrArg (fun f ↦ (P Λ f).obj K) sq.w.symm) ≫
        (pComp Λ g' p).hom.app K :=
  exactCube_comparison_hom_app _ _ _ (pComp_square Λ sq) K

private theorem map_exactSquare_hom_app
    {X Y X' Y' A : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (a : A ⟶ X') (K : D Λ Y) :
    (pComp Λ a (p' ≫ g)).hom.app K ≫
        (P Λ a).map ((pComp Λ p' g).hom.app K) ≫
        (P Λ a).map ((derivedOpenCoherencePullbackSquare Λ sq).hom.app K) =
      eqToHom (congrArg (fun f ↦ (P Λ f).obj K) (congrArg (a ≫ ·) sq.w.symm)) ≫
        (pComp Λ a (g' ≫ p)).hom.app K ≫
        (P Λ a).map ((pComp Λ g' p).hom.app K) :=
  exactCube_map_square_aux _ _ _ _ _
    (exactCube_map_comp_map_aux (P Λ a) _ _ ((pComp Λ p' g).hom_inv_id_app K) _ _ _
      (exactSquare_hom_app Λ sq K)) _ _ (pComp_congr_right Λ a sq.w.symm K)

private theorem exactSquare_hom_app_obj
    {X Y X' Y' V : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (b : Y ⟶ V) (K : D Λ V) :
    (pComp Λ p' (g ≫ b)).hom.app K ≫
        (P Λ p').map ((pComp Λ g b).hom.app K) ≫
        (derivedOpenCoherencePullbackSquare Λ sq).hom.app ((P Λ b).obj K) =
      eqToHom (congrArg (fun f ↦ (P Λ f).obj K)
        (by rw [reassoc_of% sq.w] : p' ≫ g ≫ b = g' ≫ p ≫ b)) ≫
        (pComp Λ g' (p ≫ b)).hom.app K ≫
        (P Λ g').map ((pComp Λ p b).hom.app K) :=
  exactCube_square_app_obj_aux _ _ _ _ _ _ _ _ _ ((pComp Λ p' g).hom_inv_id_app _)
    (pComp_assoc Λ p' g b K) _ _ _ _
    (exactSquare_hom_app Λ sq ((P Λ b).obj K))
    (pComp_congr_left Λ sq.w.symm b K) _ _ (pComp_assoc Λ g' p b K)

set_option maxHeartbeats 1000000 in
-- Instantiating all six faces of the derived cube has large dependent types.
private theorem exactSquare_cube
    {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (qj : CommSq aU j' j aW) (qi : CommSq aY i' i b)
    (qr : CommSq aW r' r b) (qp : CommSq aU p' p aY) (K : D Λ Z) :
    (derivedOpenCoherencePullbackSquare Λ q').hom.app ((P Λ b).obj K) ≫
        (P Λ j').map ((derivedOpenCoherencePullbackSquare Λ qr).hom.app K) ≫
        (derivedOpenCoherencePullbackSquare Λ qj).hom.app ((P Λ r).obj K) =
      (P Λ p').map ((derivedOpenCoherencePullbackSquare Λ qi).hom.app K) ≫
        (derivedOpenCoherencePullbackSquare Λ qp).hom.app ((P Λ i).obj K) ≫
        (P Λ aU).map ((derivedOpenCoherencePullbackSquare Λ q).hom.app K) :=
  exactCube_cube_aux (h₁ := exactSquare_hom_app_obj Λ q' b K)
    (h₂ := map_exactSquare_hom_app Λ qr j' K)
    (h₃ := exactSquare_hom_app_obj Λ qj r K)
    (h₄ := map_exactSquare_hom_app Λ qi p' K)
    (h₅ := exactSquare_hom_app_obj Λ qp i K)
    (h₆ := map_exactSquare_hom_app Λ q aU K)

private theorem restrictionExchange_vertical
    {U W Y Z V T : Scheme.{u}}
    {j : U ⟶ W} {i : Y ⟶ Z} {k : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k) (M : D Λ W) :
    (P Λ k).map ((RC Λ r₁ r₂).inv.app M) ≫
        (derivedDirectImageOpenRestriction Λ q₂).app ((Q Λ r₁).obj M) ≫
        (Q Λ p₂).map ((derivedDirectImageOpenRestriction Λ q₁).app M) =
      (derivedDirectImageOpenRestriction Λ q).app M ≫
        (RC Λ p₁ p₂).inv.app ((P Λ j).obj M) := by
  have hs : (TwoSquare.vComp (derivedOpenCoherencePullbackSquare Λ q₂).hom
      (derivedOpenCoherencePullbackSquare Λ q₁).hom).whiskerLeft
        (pComp Λ r₁ r₂).inv =
      TwoSquare.whiskerRight
        (derivedOpenCoherencePullbackSquare Λ (q₁.vert_comp q₂)).hom
        (pComp Λ p₁ p₂).inv := exactSquare_vert_inv Λ q₁ q₂
  have hm := congrArg (mateEquiv
    (upperStarLowerStarAdjunction Λ (r₁ ≫ r₂)).mapDerivedCategoryRightDerivedAdjunction
    ((upperStarLowerStarAdjunction Λ p₂).mapDerivedCategoryRightDerivedAdjunction.comp
      (upperStarLowerStarAdjunction Λ p₁).mapDerivedCategoryRightDerivedAdjunction)) hs
  rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
    mateEquiv_hcomp] at hm
  · have hc := congrArg (fun t ↦ t.natTrans.app M) hm
    simpa only [derivedDirectImageOpenRestriction, RC, rComp, Iso.symm_inv, Iso.symm_hom,
      conjugateIsoEquiv_apply_hom, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hc


set_option maxHeartbeats 1000000 in
-- The four derived adjunctions produce large dependent mate expressions.
private theorem restrictionExchange_cube
    {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (qj : CommSq aU j' j aW) (qi : CommSq aY i' i b)
    (qr : CommSq aW r' r b) (qp : CommSq aU p' p aY) (M : D Λ W) :
    (P Λ aY).map ((derivedDirectImageOpenRestriction Λ q).app M) ≫
        (derivedDirectImageOpenRestriction Λ qp).app ((P Λ j).obj M) ≫
        (Q Λ p').map ((derivedOpenCoherencePullbackSquare Λ qj).inv.app M) =
      (derivedOpenCoherencePullbackSquare Λ qi).inv.app ((Q Λ r).obj M) ≫
        (P Λ i').map ((derivedDirectImageOpenRestriction Λ qr).app M) ≫
        (derivedDirectImageOpenRestriction Λ q').app ((P Λ aW).obj M) := by
  have hc (K : D Λ Z) := (exactSquare_cube Λ q q' qj qi qr qp K).symm
  exact exchangeMate_cube
    (upperStarLowerStarAdjunction Λ r).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ r').mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p').mapDerivedCategoryRightDerivedAdjunction
    (P Λ b) (P Λ aW) (P Λ aY) (P Λ aU)
    (derivedOpenCoherencePullbackSquare Λ qr).symm
    (derivedOpenCoherencePullbackSquare Λ qi).symm
    (derivedOpenCoherencePullbackSquare Λ qj).symm
    (derivedOpenCoherencePullbackSquare Λ qp).symm
    (derivedOpenCoherencePullbackSquare Λ q).hom
    (derivedOpenCoherencePullbackSquare Λ q').hom hc M

private theorem B_unit (openData : OpenLaws Λ)
    {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b) (K : D Λ U) :
    (openData.units.unitIso j').hom.app ((P Λ a).obj K) ≫
        (P Λ j').map ((openData.B sq).inv.app K) =
      (P Λ a).map ((openData.units.unitIso j).hom.app K) ≫
        (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).inv.app ((J Λ j).obj K) := by
  have h := unit_mateEquiv_symm
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j')
    (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).inv) K
  simpa only [openData.units.normalized, openData.B_normalized, openMap,
    TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj, Functor.comp_obj] using h.symm

private theorem B_unit_inv (openData : OpenLaws Λ)
    {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b) (K : D Λ U) :
    (P Λ j').map ((openData.B sq).hom.app K) ≫
        (openData.units.unitIso j').inv.app ((P Λ a).obj K) =
      (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).hom.app ((J Λ j).obj K) ≫
        (P Λ a).map ((openData.units.unitIso j).inv.app K) := by
  apply (cancel_epi ((P Λ a).map ((openData.units.unitIso j).hom.app K) ≫
    (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).inv.app ((J Λ j).obj K))).1
  simp only [Category.assoc]
  conv_lhs => rw [← Category.assoc, ← Category.assoc, ← B_unit Λ openData sq K]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_id,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  simp only [Functor.id_obj]

private theorem isIso_map_mate_app
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ E} {U₂ : E ⥤ B}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ E} {R₂ : E ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : F₁ ⊣ U₁) (a₄ : F₂ ⊣ U₂)
    (α : TwoSquare F₁ L₁ L₂ F₂) [IsIso α.natTrans]
    [IsIso a₃.unit] (b : B) [IsIso (a₄.unit.app b)] :
    IsIso (U₁.map ((mateEquiv a₁ a₂ α).natTrans.app b)) := by
  have hβ : IsIso (mateEquiv a₄ a₃ (mateEquiv a₁ a₂ α)).natTrans := by
    rw [iterated_mateEquiv_conjugateEquiv]
    infer_instance
  have h := unit_mateEquiv a₄ a₃ (mateEquiv a₁ a₂ α) b
  have h' : U₁.map ((mateEquiv a₁ a₂ α).natTrans.app b) =
      inv (a₃.unit.app _) ≫ R₁.map (a₄.unit.app b) ≫
        (mateEquiv a₄ a₃ (mateEquiv a₁ a₂ α)).natTrans.app _ := by
    rw [IsIso.eq_inv_comp]
    exact h.symm
  rw [h']
  infer_instance

private theorem restrictionExchange_clopen
    {U V Y : Scheme.{u}} (s : U ⟶ V) (p : U ⟶ Y) (q : V ⟶ Y)
    [IsOpenImmersion s] (hs : IsClosed (Set.range s))
    (sq : CommSq s p q (𝟙 Y)) (K : D Λ U) :
    IsIso ((derivedDirectImageOpenRestriction Λ sq).app ((J Λ s).obj K)) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ s
  have : IsIso a.unit := by
    change IsIso (openImmersionLowerShriekUpperStarAdjunction Λ s
      ).mapDerivedCategoryAdjunction.unit
    infer_instance
  let ff := a.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let b := (WeilConjectures.CompactSupportCondensedRealization.clopenExtensionRightAdjunction
    Λ s hs).mapDerivedCategoryAdjunction
  have : IsIso b.counit := b.counit_isIso_of_R_fully_faithful
  have : IsIso (b.unit.app ((J Λ s).obj K)) := b.isIso_unit_app_of_iso (Iso.refl _)
  let c := (upperStarLowerStarAdjunction Λ (𝟙 Y)).mapDerivedCategoryRightDerivedAdjunction
  have : (P Λ (𝟙 Y)).IsEquivalence := Functor.isEquivalence_of_iso (pId Λ Y).symm
  have : IsIso c.unit := inferInstance
  have h := isIso_map_mate_app
    (upperStarLowerStarAdjunction Λ q).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction c b
    (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom)
    ((J Λ s).obj K)
  have : (Q Λ (𝟙 Y)).IsEquivalence := Functor.isEquivalence_of_iso (RI Λ Y).symm
  have : IsIso ((Q Λ (𝟙 Y)).map
      ((derivedDirectImageOpenRestriction Λ sq).app ((J Λ s).obj K))) := h
  exact isIso_of_reflects_iso _ (Q Λ (𝟙 Y))

private theorem supportLift_open_and_closed
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsProper p] [IsProper r]
    (sq : CommSq j p r i) :
    IsOpenImmersion (pullback.lift j p sq.w) ∧
      IsClosedImmersion (pullback.lift j p sq.w) := by
  let s : U ⟶ pullback r i := pullback.lift j p sq.w
  have hs : s ≫ pullback.fst r i = j := pullback.lift_fst _ _ _
  have ht : s ≫ pullback.snd r i = p := pullback.lift_snd _ _ _
  have : IsOpenImmersion (s ≫ pullback.fst r i) := hs.symm ▸ inferInstance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s (pullback.fst r i)
  have : IsProper (s ≫ pullback.snd r i) := ht.symm ▸ inferInstance
  have : IsProper s := IsProper.of_comp s (pullback.snd r i)
  exact ⟨inferInstance, IsClosedImmersion.of_isPreimmersion s
    (Scheme.Hom.isClosedMap s).isClosed_range⟩

private theorem restriction_app (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] (sq : CommSq j p r i) (K : D Λ U) :
    (L Λ units sq).app K =
      (derivedDirectImageOpenRestriction Λ sq).app ((J Λ j).obj K) ≫
        (Q Λ p).map ((units.unitIso j).inv.app K) := by
  simp only [L, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id]

private theorem comparisonInverse_eq_inv
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B : C} (f : A ⟶ B) [IsIso f] : comparisonInverse f = inv f := by
  classical
  simp only [comparisonInverse, dif_pos (inferInstance : IsIso f)]

private theorem gamma_transpose (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i) (K : D Λ U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _
      ((G Λ units sq).app K) = (comparisonInverse (L Λ units sq)).app K := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
  simp only [G, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id]
  change a.homEquiv _ _
    ((a.homEquiv _ _).symm ((comparisonInverse (L Λ units sq)).app K)) = _
  exact (a.homEquiv _ _).apply_symm_apply _

private theorem gamma_transpose_restriction (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i)
    [IsIso (L Λ units sq)] (K : D Λ U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _
      ((G Λ units sq).app K) ≫ (L Λ units sq).app K = 𝟙 _ := by
  rw [gamma_transpose, comparisonInverse_eq_inv]
  rw [← NatTrans.comp_app, IsIso.inv_hom_id]
  rfl

private theorem gamma_map_restriction (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i)
    [IsIso (L Λ units sq)] (K : D Λ U) :
    (P Λ i).map ((G Λ units sq).app K) ≫ (L Λ units sq).app K =
      (units.unitIso i).inv.app ((Q Λ p).obj K) := by
  apply (cancel_epi ((units.unitIso i).hom.app ((Q Λ p).obj K))).1
  rw [Iso.hom_inv_id_app]
  have h := gamma_transpose_restriction Λ units sq K
  simpa only [Adjunction.homEquiv_unit, units.normalized, Category.assoc,
    Functor.id_obj, Functor.comp_obj] using h

private theorem gamma_eq_of_transpose (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i)
    [IsIso (L Λ units sq)] (K : D Λ U)
    (f : (J Λ i).obj ((Q Λ p).obj K) ⟶ (Q Λ r).obj ((J Λ j).obj K))
    (hf : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _ f ≫
      (L Λ units sq).app K = 𝟙 _) : (G Λ units sq).app K = f := by
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _).injective
  apply (cancel_mono ((L Λ units sq).app K)).1
  exact (gamma_transpose_restriction Λ units sq K).trans hf.symm

private theorem restriction_isIso_cartesian (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : IsPullback j p r i) :
    IsIso (L Λ units sq.toCommSq) := by
  have := (derivedOpenRestrictionNormalization Λ sq).derived_isIso
  unfold L
  infer_instance

private theorem restrictionExchange_isIso_congr
    {U W Y Z : Scheme.{u}} {j j' : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z}
    {i i' : Y ⟶ Z} (sq : CommSq j p r i) (sq' : CommSq j' p r i')
    (hj : j' = j) (hi : i' = i) (M : D Λ W)
    (h : IsIso ((derivedDirectImageOpenRestriction Λ sq').app M)) :
    IsIso ((derivedDirectImageOpenRestriction Λ sq).app M) := by
  subst j' i'
  exact h

set_option maxHeartbeats 1000000 in
-- Native derived endpoints need additional unification time.
private theorem restriction_isIso_support (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i)
    (hc : IsClosed (Set.range (pullback.lift j p sq.w))) :
    IsIso (L Λ units sq) := by
  let s : U ⟶ pullback r i := pullback.lift j p sq.w
  let t := pullback.fst r i
  let q := pullback.snd r i
  have hst : s ≫ t = j := pullback.lift_fst _ _ _
  have hsq : s ≫ q = p := pullback.lift_snd _ _ _
  have : IsOpenImmersion (s ≫ t) := hst.symm ▸ inferInstance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s t
  let as := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ s
  let atOp := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ t
  let aj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j
  have : IsIso atOp.unit := by
    change IsIso (openImmersionLowerShriekUpperStarAdjunction Λ t
      ).mapDerivedCategoryAdjunction.unit
    infer_instance
  let k : P Λ j ≅ P Λ t ⋙ P Λ s :=
    eqToIso (congrArg (fun f ↦ P Λ f) hst.symm) ≪≫ pComp Λ s t
  let ec : J Λ j ≅ J Λ s ⋙ J Λ t :=
    aj.leftAdjointUniq ((as.comp atOp).ofNatIsoRight k.symm)
  let sq₁ : CommSq s p q (𝟙 Y) := ⟨by simpa using hsq⟩
  let sq₂ := (IsPullback.of_hasPullback r i).toCommSq
  have : IsIso (derivedDirectImageOpenRestriction Λ sq₂) :=
    (derivedOpenRestrictionNormalization Λ (IsPullback.of_hasPullback r i)).derived_isIso
  have hK (K : D Λ U) : IsIso ((L Λ units sq).app K) := by
    let M := (J Λ j).obj K
    let eM : (P Λ t).obj M ≅ (J Λ s).obj K :=
      (P Λ t).mapIso (ec.app K) ≪≫ (asIso (atOp.unit.app ((J Λ s).obj K))).symm
    have hi := restrictionExchange_clopen Λ s p q hc sq₁ K
    have : IsIso ((derivedDirectImageOpenRestriction Λ sq₁).app ((P Λ t).obj M)) :=
      (NatTrans.isIso_app_iff_of_iso (derivedDirectImageOpenRestriction Λ sq₁) eM).mpr hi
    have he := restrictionExchange_horizontal Λ sq₂ sq₁ M
    have hi' : IsIso ((derivedDirectImageOpenRestriction Λ
        (sq₁.horiz_comp sq₂)).app M) := by
      rw [← he]
      infer_instance
    have : IsIso ((derivedDirectImageOpenRestriction Λ sq).app M) := by
      exact restrictionExchange_isIso_congr Λ sq (sq₁.horiz_comp sq₂)
        hst (Category.id_comp i) M hi'
    rw [restriction_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private theorem restriction_isIso_proper (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsProper p] [IsProper r]
    (sq : CommSq j p r i) : IsIso (L Λ units sq) := by
  have := (supportLift_open_and_closed sq).2
  exact restriction_isIso_support Λ units sq
    (Scheme.Hom.isClosedMap (pullback.lift j p sq.w)).isClosed_range

private theorem jComp_unit (units : OpenUnits Λ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (K : D Λ X) :
    (units.unitIso (f ≫ g)).hom.app K ≫
        (pComp Λ f g).hom.app ((J Λ (f ≫ g)).obj K) =
      (units.unitIso f).hom.app K ≫
        (P Λ f).map ((units.unitIso g).hom.app ((J Λ f).obj K)) ≫
        (P Λ f).map ((P Λ g).map ((jComp Λ f g).hom.app K)) := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ f).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ g)
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (f ≫ g)
  have hc : conjugateIsoEquiv b a (jComp Λ f g) = pComp Λ f g := by
    rw [jComp, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply, Iso.symm_symm_eq]
  have hh := unit_conjugateEquiv b a (jComp Λ f g).hom K
  change b.unit.app K ≫ (conjugateIsoEquiv b a (jComp Λ f g)).hom.app _ = _ at hh
  rw [hc] at hh
  simpa only [a, b, Adjunction.comp_unit_app, Functor.comp_map, units.normalized,
    Category.assoc] using hh

private theorem jComp_unit_inv (units : OpenUnits Λ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (K : D Λ X) :
    (units.unitIso (f ≫ g)).inv.app K =
      (pComp Λ f g).hom.app ((J Λ (f ≫ g)).obj K) ≫
        (P Λ f).map ((P Λ g).map ((jComp Λ f g).inv.app K)) ≫
        (P Λ f).map ((units.unitIso g).inv.app ((J Λ f).obj K)) ≫
        (units.unitIso f).inv.app K := by
  apply (cancel_epi ((units.unitIso (f ≫ g)).hom.app K)).1
  rw [Iso.hom_inv_id_app, ← Category.assoc, ← Category.assoc,
    ← Category.assoc, jComp_unit]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (units.unitIso f).hom_inv_id_app K |>.symm

private theorem jComp_unit_inv_map (units : OpenUnits Λ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (K : D Λ X) :
    (units.unitIso (f ≫ g)).hom.app K ≫
        (P Λ (f ≫ g)).map ((jComp Λ f g).inv.app K) ≫
        (pComp Λ f g).hom.app ((J Λ g).obj ((J Λ f).obj K)) =
      (units.unitIso f).hom.app K ≫
        (P Λ f).map ((units.unitIso g).hom.app ((J Λ f).obj K)) := by
  have hn := (pComp Λ f g).hom.naturality ((jComp Λ f g).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn, ← Category.assoc, jComp_unit]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option maxHeartbeats 1000000 in
-- Native derived endpoints need additional unification time.
private theorem restriction_horizontal_components (units : OpenUnits Λ)
    {U W V Y Z T : Scheme.{u}}
    {j₁ : U ⟶ W} {j₂ : W ⟶ V} {i₁ : Y ⟶ Z} {i₂ : Z ⟶ T}
    {p : U ⟶ Y} {r : W ⟶ Z} {s : V ⟶ T}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂)) (K : D Λ U) :
    (L Λ units q).app K =
      (pComp Λ i₁ i₂).hom.app ((Q Λ s).obj ((J Λ (j₁ ≫ j₂)).obj K)) ≫
        (P Λ i₁).map ((P Λ i₂).map ((Q Λ s).map ((jComp Λ j₁ j₂).inv.app K))) ≫
        (P Λ i₁).map ((L Λ units q₂).app ((J Λ j₁).obj K)) ≫
        (L Λ units q₁).app K := by
  let M := (J Λ (j₁ ≫ j₂)).obj K
  have he := restrictionExchange_horizontal Λ q₂ q₁ M
  have hu : (pComp Λ j₁ j₂).inv.app M ≫ (units.unitIso (j₁ ≫ j₂)).inv.app K =
      (P Λ j₁).map ((P Λ j₂).map ((jComp Λ j₁ j₂).inv.app K)) ≫
        (P Λ j₁).map ((units.unitIso j₂).inv.app ((J Λ j₁).obj K)) ≫
        (units.unitIso j₁).inv.app K := by
    rw [jComp_unit_inv, Iso.inv_hom_id_app_assoc]
  have hn₁ := (derivedDirectImageOpenRestriction Λ q₁).naturality
    ((P Λ j₂).map ((jComp Λ j₁ j₂).inv.app K))
  have hn₂ := (derivedDirectImageOpenRestriction Λ q₁).naturality
    ((units.unitIso j₂).inv.app ((J Λ j₁).obj K))
  have hn₃ := (derivedDirectImageOpenRestriction Λ q₂).naturality
    ((jComp Λ j₁ j₂).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂ hn₃
  rw [restriction_app]
  rw [← he]
  simp only [Category.assoc]
  change (pComp Λ i₁ i₂).hom.app ((Q Λ s).obj M) ≫
    (P Λ i₁).map ((derivedDirectImageOpenRestriction Λ q₂).app M) ≫
    (derivedDirectImageOpenRestriction Λ q₁).app ((P Λ j₂).obj M) ≫
    (Q Λ p).map ((pComp Λ j₁ j₂).inv.app M) ≫
    (Q Λ p).map ((units.unitIso (j₁ ≫ j₂)).inv.app K) = _
  rw [← Functor.map_comp, hu]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn₁, ← reassoc_of% hn₂]
  rw [← Functor.map_comp_assoc, ← hn₃, Functor.map_comp]
  simp only [restriction_app, Functor.map_comp, Category.assoc]
  rfl

private theorem restriction_isIso_horizontal (units : OpenUnits Λ)
    {U W V Y Z T : Scheme.{u}}
    {j₁ : U ⟶ W} {j₂ : W ⟶ V} {i₁ : Y ⟶ Z} {i₂ : Z ⟶ T}
    {p : U ⟶ Y} {r : W ⟶ Z} {s : V ⟶ T}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    [IsIso (L Λ units q₁)] [IsIso (L Λ units q₂)]
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂)) : IsIso (L Λ units q) := by
  have hK (K : D Λ U) : IsIso ((L Λ units q).app K) := by
    rw [restriction_horizontal_components Λ units q₁ q₂ q]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

set_option maxHeartbeats 4000000 in
-- Native derived endpoints need additional unification time.
private theorem gamma_horizontal_proof (units : OpenUnits Λ)
    {U W V Y Z T : Scheme.{u}}
    {j₁ : U ⟶ W} {j₂ : W ⟶ V} {i₁ : Y ⟶ Z} {i₂ : Z ⟶ T}
    {p : U ⟶ Y} {r : W ⟶ Z} {s : V ⟶ T}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    [IsIso (L Λ units q₁)] [IsIso (L Λ units q₂)]
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂)) (K : D Λ U) :
    (G Λ units q).app K =
      (jComp Λ i₁ i₂).inv.app ((Q Λ p).obj K) ≫
        (J Λ i₂).map ((G Λ units q₁).app K) ≫
        (G Λ units q₂).app ((J Λ j₁).obj K) ≫
        (Q Λ s).map ((jComp Λ j₁ j₂).hom.app K) := by
  have := restriction_isIso_horizontal Λ units q₁ q₂ q
  apply gamma_eq_of_transpose Λ units q K
  let v := (J Λ i₂).map ((G Λ units q₁).app K) ≫
    (G Λ units q₂).app ((J Λ j₁).obj K) ≫
    (Q Λ s).map ((jComp Λ j₁ j₂).hom.app K)
  have hn := (pComp Λ i₁ i₂).hom.naturality v
  dsimp only [Functor.comp_map] at hn
  rw [Adjunction.homEquiv_unit, restriction_horizontal_components Λ units q₁ q₂ q]
  rw [(P Λ (i₁ ≫ i₂)).map_comp]
  simp only [Category.assoc]
  change _ ≫ (P Λ (i₁ ≫ i₂)).map ((jComp Λ i₁ i₂).inv.app _) ≫
    (P Λ (i₁ ≫ i₂)).map v ≫ _ = _
  rw [reassoc_of% hn]
  rw [← units.normalized,
    reassoc_of% (jComp_unit_inv_map Λ units i₁ i₂ ((Q Λ p).obj K))]
  dsimp only [v]
  simp only [Functor.map_comp, Category.assoc]
  have hc :
      (P Λ i₁).map ((P Λ i₂).map ((Q Λ s).map ((jComp Λ j₁ j₂).hom.app K))) ≫
        (P Λ i₁).map ((P Λ i₂).map ((Q Λ s).map ((jComp Λ j₁ j₂).inv.app K))) =
        𝟙 _ := by
    rw [← (P Λ i₁).map_comp, ← (P Λ i₂).map_comp, ← (Q Λ s).map_comp,
      Iso.hom_inv_id_app, (Q Λ s).map_id, (P Λ i₂).map_id, (P Λ i₁).map_id]
  rw [reassoc_of% hc]
  have hn₂ := (units.unitIso i₂).hom.naturality ((G Λ units q₁).app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn₂
  rw [← Functor.map_comp_assoc, ← hn₂, Functor.map_comp]
  have h₂ := gamma_transpose_restriction Λ units q₂ ((J Λ j₁).obj K)
  rw [Adjunction.homEquiv_unit, ← units.normalized] at h₂
  have hm₂ := congrArg (fun t ↦ (P Λ i₁).map t) h₂
  simp only [Functor.map_comp, Category.assoc] at hm₂
  erw [CategoryTheory.Functor.map_id] at hm₂
  simp only [Category.assoc]
  rw [reassoc_of% hm₂]
  have h₁ := gamma_transpose_restriction Λ units q₁ K
  simpa only [Adjunction.homEquiv_unit, units.normalized, Category.assoc,
    Functor.comp_obj, Functor.id_obj] using h₁

private theorem jId_transpose (X : Scheme.{u}) (K : D Λ X) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).homEquiv _ _
      ((jId Λ X).hom.app K) = (pId Λ X).inv.app K := by
  apply (cancel_mono ((pId Λ X).hom.app K)).1
  rw [Iso.inv_hom_id_app]
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
      (pId Λ X)) Adjunction.id K
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  exact h

private theorem jId_hom_from_unit (units : OpenUnits Λ) (X : Scheme.{u}) (K : D Λ X) :
    (pId Λ X).inv.app ((J Λ (𝟙 X)).obj K) ≫ (units.unitIso (𝟙 X)).inv.app K =
      (jId Λ X).hom.app K := by
  have h := jId_transpose Λ X K
  rw [Adjunction.homEquiv_unit] at h
  have hn := (pId Λ X).hom.naturality ((jId Λ X).hom.app K)
  dsimp only [Functor.id_map] at hn
  have hu : (units.unitIso (𝟙 X)).hom.app K ≫
      (pId Λ X).hom.app ((J Λ (𝟙 X)).obj K) ≫ (jId Λ X).hom.app K = 𝟙 _ := by
    rw [units.normalized]
    rw [← hn, ← Category.assoc, h]
    exact (pId Λ X).inv_hom_id_app K
  have hh := congrArg (fun t ↦ (pId Λ X).inv.app ((J Λ (𝟙 X)).obj K) ≫
    (units.unitIso (𝟙 X)).inv.app K ≫ t) hu
  simp only [← Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  erw [Iso.inv_hom_id_app, Category.id_comp] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

private theorem gamma_horizontal_id_proof (units : OpenUnits Λ)
    {U Y : Scheme.{u}} (p : U ⟶ Y) (sq : CommSq (𝟙 U) p p (𝟙 Y)) (K : D Λ U) :
    (G Λ units sq).app K =
      (jId Λ Y).hom.app ((Q Λ p).obj K) ≫ (Q Λ p).map ((jId Λ U).inv.app K) := by
  have hp : IsPullback (𝟙 U) p p (𝟙 Y) := IsPullback.of_horiz_isIso ⟨sq.w⟩
  have := restriction_isIso_cartesian Λ units hp
  apply gamma_eq_of_transpose Λ units sq K
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← Adjunction.homEquiv_unit, jId_transpose]
  have hn := (pId Λ Y).inv.naturality ((Q Λ p).map ((jId Λ U).inv.app K))
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  simp only [L, restrictionExchange_id, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.id_comp]
  erw [Category.comp_id]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  rw [jId_hom_from_unit, Iso.inv_hom_id_app]
  exact (Q Λ p).map_id K

private theorem gamma_vertical_id_proof (units : OpenUnits Λ)
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (sq : CommSq j (𝟙 U) (𝟙 W) j) (K : D Λ U) :
    (G Λ units sq).app K =
      (J Λ j).map ((RI Λ U).hom.app K) ≫ (RI Λ W).inv.app ((J Λ j).obj K) := by
  have hp : IsPullback j (𝟙 U) (𝟙 W) j := IsPullback.of_vert_isIso sq
  have := restriction_isIso_cartesian Λ units hp
  apply gamma_eq_of_transpose Λ units sq K
  have he := restrictionExchange_vertical_id Λ j sq ((J Λ j).obj K)
  have hex : (derivedDirectImageOpenRestriction Λ sq).app ((J Λ j).obj K) =
      (P Λ j).map ((RI Λ W).hom.app ((J Λ j).obj K)) ≫
        (RI Λ U).inv.app ((P Λ j).obj ((J Λ j).obj K)) := by
    apply (cancel_mono ((RI Λ U).hom.app ((P Λ j).obj ((J Λ j).obj K)))).1
    rw [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact he
  rw [Adjunction.homEquiv_unit, restriction_app, hex]
  simp only [Category.assoc]
  change _ ≫ (P Λ j).map ((J Λ j).map ((RI Λ U).hom.app K) ≫
    (RI Λ W).inv.app ((J Λ j).obj K)) ≫
    (P Λ j).map ((RI Λ W).hom.app ((J Λ j).obj K)) ≫ _ = _
  rw [(P Λ j).map_comp]
  simp only [Category.assoc]
  have hc : (P Λ j).map ((RI Λ W).inv.app ((J Λ j).obj K)) ≫
      (P Λ j).map ((RI Λ W).hom.app ((J Λ j).obj K)) = 𝟙 _ := by
    rw [← (P Λ j).map_comp, Iso.inv_hom_id_app, (P Λ j).map_id]
  rw [reassoc_of% hc]
  have hn := (units.unitIso j).hom.naturality ((RI Λ U).hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [← units.normalized]
  rw [← reassoc_of% hn]
  have hm := (RI Λ U).inv.naturality ((units.unitIso j).inv.app K)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hm ⊢
  rw [← hm, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]

private theorem supportLift_vertical_closed
    {U W Y Z V T : Scheme.{u}}
    {j : U ⟶ W} {i : Y ⟶ Z} {k : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k)
    [IsClosedImmersion (pullback.lift j p₁ q₁.w)]
    [IsClosedImmersion (pullback.lift i p₂ q₂.w)] :
    IsClosed (Set.range (pullback.lift j (p₁ ≫ p₂) q.w)) := by
  let s₂ := pullback.lift i p₂ q₂.w
  let v : pullback r₁ i ⟶ pullback (r₁ ≫ r₂) k :=
    pullback.lift (pullback.fst r₁ i) (pullback.snd r₁ i ≫ p₂) (by
      rw [← Category.assoc, pullback.condition, Category.assoc, q₂.w,
        ← Category.assoc])
  let t : pullback (r₁ ≫ r₂) k ⟶ pullback r₂ k :=
    pullback.lift (pullback.fst (r₁ ≫ r₂) k ≫ r₁)
      (pullback.snd (r₁ ≫ r₂) k) (by
        simpa only [Category.assoc] using (pullback.condition (f := r₁ ≫ r₂) (g := k)))
  have hv : v ≫ t = pullback.snd r₁ i ≫ s₂ := by
    apply pullback.hom_ext <;> simp [v, t, s₂, Category.assoc, pullback.condition]
  have hc (c : PullbackCone t s₂) :
      (c.fst ≫ pullback.fst (r₁ ≫ r₂) k) ≫ r₁ = c.snd ≫ i := by
    have h := congrArg (fun f ↦ f ≫ pullback.fst r₂ k) c.condition
    simpa [t, s₂, Category.assoc] using h
  have hd (c : PullbackCone t s₂) :
      c.fst ≫ pullback.snd (r₁ ≫ r₂) k = c.snd ≫ p₂ := by
    have h := congrArg (fun f ↦ f ≫ pullback.snd r₂ k) c.condition
    simpa [t, s₂, Category.assoc] using h
  have hb : IsPullback v (pullback.snd r₁ i) t s₂ := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hv
      (fun c ↦ pullback.lift (c.fst ≫ pullback.fst (r₁ ≫ r₂) k) c.snd (hc c))
      (fun c ↦ ?_) (fun c ↦ ?_) (fun c m hm hn ↦ ?_))
    · apply pullback.hom_ext <;> simp [v, Category.assoc, hd]
    · simp
    · apply pullback.hom_ext
      · have h := congrArg (fun f ↦ f ≫ pullback.fst (r₁ ≫ r₂) k) hm
        simpa [v, Category.assoc] using h
      · simpa using hn
  have : IsClosedImmersion v :=
    (show MorphismProperty Scheme from @IsClosedImmersion).of_isPullback hb.flip
      inferInstance
  have he : pullback.lift j p₁ q₁.w ≫ v = pullback.lift j (p₁ ≫ p₂) q.w := by
    apply pullback.hom_ext <;> simp [v, Category.assoc]
  have : IsClosedImmersion (pullback.lift j (p₁ ≫ p₂) q.w) :=
    he ▸ inferInstance
  exact (Scheme.Hom.isClosedMap (pullback.lift j (p₁ ≫ p₂) q.w)).isClosed_range

private theorem supportLift_admissible_closed
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i)
    (h : IsAdmissibleSquare j p r i) :
    IsClosedImmersion (pullback.lift j p sq.w) := by
  rcases h with h | ⟨hp, hr⟩
  · have he : pullback.lift j p sq.w = h.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    rw [he]
    infer_instance
  · have := hp
    have := hr
    exact (supportLift_open_and_closed sq).2

private theorem restriction_isIso_admissible (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i)
    (h : IsAdmissibleSquare j p r i) : IsIso (L Λ units sq) := by
  rcases h with h | ⟨hp, hr⟩
  · exact restriction_isIso_cartesian Λ units h
  · have := hp
    have := hr
    exact restriction_isIso_proper Λ units sq

set_option maxHeartbeats 1000000 in
-- Normalize the canonical derived compositors and their naturality equations.
private theorem restriction_vertical_components (units : OpenUnits Λ)
    {U W Y Z V T : Scheme.{u}}
    {j : U ⟶ W} {i : Y ⟶ Z} {k : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k) (K : D Λ U) :
    (P Λ k).map ((RC Λ r₁ r₂).hom.app ((J Λ j).obj K)) ≫
        (L Λ units q).app K =
      (derivedDirectImageOpenRestriction Λ q₂).app ((Q Λ r₁).obj ((J Λ j).obj K)) ≫
        (Q Λ p₂).map ((L Λ units q₁).app K) ≫
        (RC Λ p₁ p₂).hom.app K := by
  have he := restrictionExchange_vertical Λ q₁ q₂ q ((J Λ j).obj K)
  have hh := congrArg (fun f ↦
    (P Λ k).map ((RC Λ r₁ r₂).hom.app ((J Λ j).obj K)) ≫ f ≫
      (RC Λ p₁ p₂).hom.app ((P Λ j).obj ((J Λ j).obj K))) he
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  have hn := (RC Λ p₁ p₂).hom.naturality ((units.unitIso j).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [restriction_app]
  rw [← Category.assoc, ← hh]
  simp only [Category.assoc]
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]

set_option maxHeartbeats 4000000 in
-- The vertical transpose combines four derived comparisons and their units.
private theorem gamma_vertical_proof (units : OpenUnits Λ)
    {U W Y Z V T : Scheme.{u}}
    {j : U ⟶ W} {i : Y ⟶ Z} {k : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k)
    (h₁ : IsAdmissibleSquare j p₁ r₁ i) (h₂ : IsAdmissibleSquare i p₂ r₂ k)
    (K : D Λ U) :
    (G Λ units q).app K =
      (J Λ k).map ((RC Λ p₁ p₂).inv.app K) ≫
      (G Λ units q₂).app ((Q Λ p₁).obj K) ≫
      (Q Λ r₂).map ((G Λ units q₁).app K) ≫
      (RC Λ r₁ r₂).hom.app ((J Λ j).obj K) := by
  have := restriction_isIso_admissible Λ units q₁ h₁
  have := restriction_isIso_admissible Λ units q₂ h₂
  have := supportLift_admissible_closed q₁ h₁
  have := supportLift_admissible_closed q₂ h₂
  have := restriction_isIso_support Λ units q (supportLift_vertical_closed q₁ q₂ q)
  apply gamma_eq_of_transpose Λ units q K
  rw [Adjunction.homEquiv_unit, ← units.normalized]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (units.unitIso k).hom.naturality ((RC Λ p₁ p₂).inv.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [restriction_vertical_components Λ units q₁ q₂ q]
  have hn₂ := (derivedDirectImageOpenRestriction Λ q₂).naturality
    ((G Λ units q₁).app K)
  dsimp only [Functor.comp_map] at hn₂
  rw [reassoc_of% hn₂]
  rw [← Functor.map_comp_assoc, gamma_map_restriction Λ units q₁]
  rw [← reassoc_of% (restriction_app Λ units q₂ ((Q Λ p₁).obj K))]
  have h₂' := gamma_transpose_restriction Λ units q₂ ((Q Λ p₁).obj K)
  rw [Adjunction.homEquiv_unit, ← units.normalized] at h₂'
  rw [reassoc_of% h₂']
  simp only [Iso.inv_hom_id_app]

private theorem admissible_baseChange
    {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    (_q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (h : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) :
    IsAdmissibleSquare j' p' r' i' := by
  rcases h with h | ⟨hp, hr⟩
  · left
    have ho := qp.paste_horiz h
    rw [qj.w, qi.w] at ho
    exact ho.of_right q'.w qr
  · right
    exact ⟨(show MorphismProperty Scheme from @IsProper).of_isPullback qp hp,
      (show MorphismProperty Scheme from @IsProper).of_isPullback qr hr⟩

set_option maxHeartbeats 1000000 in
-- The cube calculation combines six concrete derived natural transformations.
private theorem restriction_cube_components (openData : OpenLaws Λ)
    {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) (K : D Λ U) :
    (derivedOpenCoherencePullbackSquare Λ qi.toCommSq).inv.app
        ((Q Λ r).obj ((J Λ j).obj K)) ≫
      (P Λ i').map ((derivedDirectImageOpenRestriction Λ qr.toCommSq).app
        ((J Λ j).obj K)) ≫
      (P Λ i').map ((Q Λ r').map ((openData.B qj).hom.app K)) ≫
      (L Λ openData.units q').app ((P Λ aU).obj K) =
    (P Λ aY).map ((L Λ openData.units q).app K) ≫
      (derivedDirectImageOpenRestriction Λ qp.toCommSq).app K := by
  have he := restrictionExchange_cube Λ q q' qj.toCommSq qi.toCommSq
    qr.toCommSq qp.toCommSq ((J Λ j).obj K)
  have hn := (derivedDirectImageOpenRestriction Λ q').naturality
    ((openData.B qj).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [restriction_app]
  rw [reassoc_of% hn, ← Functor.map_comp, B_unit_inv Λ openData qj]
  simp only [Functor.map_comp]
  rw [← reassoc_of% he, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn' := (derivedDirectImageOpenRestriction Λ qp.toCommSq).naturality
    ((openData.units.unitIso j).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn'
  rw [← hn']
  simp only [restriction_app, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 4000000 in
-- Transposing and cancelling the cube expands several concrete derived comparisons.
private theorem gamma_cube_proof (openData : OpenLaws Λ)
    {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (hQ : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) (K : D Λ U) :
    (P Λ b).map ((G Λ openData.units q).app K) ≫
        (derivedDirectImageOpenRestriction Λ qr.toCommSq).app ((J Λ j).obj K) ≫
        (Q Λ r').map ((openData.B qj).hom.app K) =
      (openData.B qi).hom.app ((Q Λ p).obj K) ≫
        (J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K) ≫
        (G Λ openData.units q').app ((P Λ aU).obj K) := by
  have := restriction_isIso_admissible Λ openData.units q hQ
  have := restriction_isIso_admissible Λ openData.units q'
    (admissible_baseChange q q' hQ qj qi qr qp)
  apply (cancel_epi ((openData.B qi).inv.app ((Q Λ p).obj K))).1
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i').homEquiv _ _).injective
  apply (cancel_mono ((L Λ openData.units q').app ((P Λ aU).obj K))).1
  have hr : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i').homEquiv _ _
      ((J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K) ≫
        (G Λ openData.units q').app ((P Λ aU).obj K)) ≫
      (L Λ openData.units q').app ((P Λ aU).obj K) =
      (derivedDirectImageOpenRestriction Λ qp.toCommSq).app K := by
    rw [Adjunction.homEquiv_naturality_left, Category.assoc]
    have ht := gamma_transpose_restriction Λ openData.units q' ((P Λ aU).obj K)
    dsimp only [Functor.comp_obj, Functor.id_obj] at ht ⊢
    rw [ht, Category.comp_id]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj] at hr ⊢
  rw [hr]
  rw [Adjunction.homEquiv_unit, ← openData.units.normalized]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, B_unit Λ openData qi]
  have hn := (derivedOpenCoherencePullbackSquare Λ qi.toCommSq).inv.naturality
    ((G Λ openData.units q).app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, restriction_cube_components Λ openData q q' qj qi qr qp]
  have ht := gamma_transpose_restriction Λ openData.units q K
  rw [Adjunction.homEquiv_unit, ← openData.units.normalized] at ht
  have hm := congrArg (fun t ↦ (P Λ aY).map t) ht
  simp only [Functor.map_comp, Category.assoc] at hm
  erw [CategoryTheory.Functor.map_id] at hm
  rw [reassoc_of% hm]

/-- Proper/open restriction, mate-pasting, identities, and cube coherence for a fixed
open-law package. The proof uses clopen support gluing and adjunction mate calculus.
(blueprint: lem-zl-condensed-open-proper-pasting) -/
theorem condensedOpenProperMateLaws (_hΛ : IsAdmissibleCoefficient Λ)
    (openData : OpenLaws Λ) : Nonempty (MateLaws Λ openData) := by
  refine ⟨{
    restriction_isIso := ?_
    gamma_vertical := ?_
    gamma_horizontal := ?_
    gamma_vertical_id := ?_
    gamma_horizontal_id := ?_
    cube := ?_ }⟩
  · intros
    apply restriction_isIso_admissible Λ openData.units
    assumption
  · intros
    apply gamma_vertical_proof Λ openData.units <;> assumption
  · intro U W V Y Z T j₁ j₂ i₁ i₂ p r s _ _ _ _ _ _ _ _ q₁ q₂ q h₁ h₂ K
    have := restriction_isIso_admissible Λ openData.units q₁ h₁
    have := restriction_isIso_admissible Λ openData.units q₂ h₂
    exact gamma_horizontal_proof Λ openData.units q₁ q₂ q K
  · intros
    apply gamma_vertical_id_proof
  · intros
    apply gamma_horizontal_id_proof
  · intros
    apply gamma_cube_proof Λ openData <;> assumption

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
