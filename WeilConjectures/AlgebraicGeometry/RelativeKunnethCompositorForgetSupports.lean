/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import all WeilConjectures.AlgebraicGeometry.ProperShriekCompCompForgetSupports
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar

/-! # The compact-support compositor and forgetting supports -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] CategoryTheory.conjugateEquiv
  leftDerivedUpperStarComp derivedUpperStarLowerStarAdjunction
  derivedOpenImmersionLowerShriekToLowerStar openImmersionLowerShriekLowerStarExchange
  mapDerivedCategoryOpenImmersionLowerShriekComp mapDerivedCategoryOpenImmersionLowerShriekCongr

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Forgetting supports commutes with the compatible compactification compositor.
Source: the proper-identification clause of thm-sf-kunneth-relative.
(blueprint: lem-sf-relative-kunneth-compositor-forget-supports).

Proof: expand the open/proper tower compositor. The open comparison respects composition
by the composite adjunction counit. The exchange followed by forgetting the open support
is the ordinary direct-image exchange. Naturality and the ordinary compositor pentagon
identify the resulting three direct-image factors. Properness of the original maps is
unnecessary for this calculation of the forward forget-supports maps. -/
theorem relativeKunneth_compactification_comp_forgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S)
    (d : Compactification f) (e : Compactification (p ≫ d.i))
    (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) (d.comp e)).app E =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A) e.restrict).app E) ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) d).app
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  let B := ModuleCat.{u + 1} A
  simp only [rightDerivedLowerShriekOfCompactificationCompIso,
    compactificationForgetSupports, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc,
    star_comp_iso_hom]
  have ho := open_compare_comp_congr A e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst E
  have ho' := congrArg (fun t ↦ (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor.map t) ho
  simp only [Functor.map_comp] at ho'
  erw [reassoc_of% ho']
  erw [← (rightDerivedLowerStarComp B e.g d.g).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [star_comp_hom]
  erw [← (rightDerivedLowerStarCompHom B e.g d.g (e.g ≫ d.g) rfl).naturality_assoc,
    ← (rightDerivedLowerStarCompHom B e.g d.g (e.g ≫ d.g) rfl).naturality_assoc]
  simp only [Functor.comp_map]
  have h1 := rightDerivedLowerStarCompHom_assoc_app B e.i e.g d.g
    (p ≫ d.i) (e.g ≫ d.g) (p ≫ f) e.comm rfl
    (by rw [Category.assoc, ← d.comm]) E
  erw [h1]
  have h2 := rightDerivedLowerStarCompHom_assoc_app B e.restrict.i
    (pullback.fst e.g d.i) e.g e.i (e.restrict.g ≫ d.i) (p ≫ d.i)
    e.restrict_i_fst.symm e.isPullback_restrict.w e.comm E
  have h2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) h2
  simp only [Functor.map_comp] at h2'
  erw [← reassoc_of% h2']
  have hn := (rightDerivedLowerStarCompHom B (pullback.fst e.g d.i) e.g
    (e.restrict.g ≫ d.i) e.isPullback_restrict.w).naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E)
  have hn' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hn
  simp only [Functor.comp_map, Functor.map_comp] at hn'
  erw [reassoc_of% hn']
  have hx := exchange_inclusion A (pullback.fst e.g d.i) e.restrict.g e.g d.i
    e.isPullback_restrict ((openImmersionLowerShriek B e.restrict.i).mapDerivedCategory.obj E)
  have hx' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hx
  simp only [Functor.map_comp, star_comp_iso_hom] at hx'
  erw [reassoc_of% hx']
  have hn2 := (rightDerivedLowerStarCompHom B e.restrict.g d.i
    (e.restrict.g ≫ d.i) rfl).naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E)
  have hn2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hn2
  simp only [Functor.comp_map, Functor.map_comp] at hn2'
  erw [← reassoc_of% hn2']
  have h3 := rightDerivedLowerStarCompHom_assoc_app B e.restrict.i e.restrict.g d.i
    p (e.restrict.g ≫ d.i) (p ≫ d.i) e.restrict.comm rfl rfl E
  have h3' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) h3
  simp only [Functor.map_comp] at h3'
  erw [reassoc_of% h3']
  have ht1 := (derivedOpenImmersionLowerShriekToLowerStar B d.i).naturality
    ((lowerStar B e.restrict.g).rightDerivedFunctor.map
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E))
  have ht1' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) ht1
  simp only [Functor.map_comp] at ht1'
  erw [← reassoc_of% ht1']
  have ht2 := (derivedOpenImmersionLowerShriekToLowerStar B d.i).naturality
    ((rightDerivedLowerStarCompHom B e.restrict.i e.restrict.g p e.restrict.comm).app E)
  have ht2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) ht2
  simp only [Functor.map_comp] at ht2'
  erw [← reassoc_of% ht2']
  have h4 := rightDerivedLowerStarCompHom_assoc_app B p d.i d.g
    (p ≫ d.i) f (p ≫ f) rfl d.comm
    (by rw [Category.assoc, ← d.comm]) E
  erw [← h4]


/-- The chosen compact-support compositor respects forgetting supports.
Source: thm-sf-kunneth-relative, proper-identification clause.
(blueprint: lem-sf-relative-kunneth-compositor-forget-supports).

Proof: compute the chosen compositor using its compatible compactifications. Apply the
preceding tower calculation, then cancel the canonical refinement comparisons against
their forget-supports maps. Naturality moves the remaining comparison inside the outer
pushforward. -/
theorem relativeKunneth_comp_forgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S)
    [HasCompactification p] [HasCompactification f] [HasCompactification (p ≫ f)]
    [QuasiCompact (p ≫ f)] (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification (p ≫ f))).app E =
      (R(f)_![ModuleCat.{u + 1} A]).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A)
            (HasCompactification.compactification p)).app E) ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).app
            ((R((p)_*[ModuleCat.{u + 1} A])).obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  have : QuasiCompact p := .of_comp p f
  let d := HasCompactification.compactification f
  let e := (HasCompactification.compactification (p ≫ f)).ofComp d
  have hcomp := relativeKunneth_compactification_comp_forgetSupports A p f d e E
  have hα : (rightDerivedLowerShriekIso A (d.comp e)).hom.app E ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification (p ≫ f))).app E =
      (compactificationForgetSupports (ModuleCat.{u + 1} A) (d.comp e)).app E := by
    simpa only [rightDerivedLowerShriekIso, compactificationForgetSupports, NatTrans.comp_app,
      Functor.whiskerRight_app, Category.assoc] using
      rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar A
        (d.comp e) (HasCompactification.compactification (p ≫ f)) E
  have hβ : (rightDerivedLowerShriekIso A e.restrict).hom.app E ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification p)).app E =
      (compactificationForgetSupports (ModuleCat.{u + 1} A) e.restrict).app E := by
    simpa only [rightDerivedLowerShriekIso, compactificationForgetSupports, NatTrans.comp_app,
      Functor.whiskerRight_app, Category.assoc] using
      rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar A
        e.restrict (HasCompactification.compactification p) E
  have hβ' : (rightDerivedLowerShriekIso A e.restrict).inv.app E ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} A) e.restrict).app E =
    (compactificationForgetSupports (ModuleCat.{u + 1} A)
      (HasCompactification.compactification p)).app E := by
    rw [← hβ, Iso.inv_hom_id_app_assoc]
  simp only [rightDerivedLowerShriekCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [hα, hcomp, ← Functor.map_comp_assoc, hβ']
  rfl

/-- Equality-transported form of the chosen compositor square.
Source: thm-sf-kunneth-relative, proper-identification clause.
(blueprint: lem-sf-relative-kunneth-compositor-forget-supports).

Proof: substitute the equality of the composite map and apply the preceding calculation. -/
theorem relativeKunneth_compOfEq_forgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) (h : W ⟶ S) (w : p ≫ f = h)
    [HasCompactification p] [HasCompactification f] [HasCompactification h]
    [QuasiCompact h] (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekCompIsoApp A p f h w E).inv ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification h)).app E =
      (R(f)_![ModuleCat.{u + 1} A]).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A)
            (HasCompactification.compactification p)).app E) ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).app
            ((R((p)_*[ModuleCat.{u + 1} A])).obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f h w).hom.app E := by
  subst h
  simpa only [rightDerivedLowerShriekCompIsoApp, rightDerivedLowerShriekCompIsoOfEq,
    eqToIso_refl, Iso.refl_trans, Iso.app_inv, Functor.comp_obj] using
      relativeKunneth_comp_forgetSupports A p f E

end AlgebraicGeometry.Etale
