/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceEndpoint
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientLeftComparisonBaseChange
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality

/-! # Open cancellation for normalized section locality

Source: composition coherence Step 1, compatible-chart source calculation.
(blueprint: lem-pur-section-etale-open-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

namespace OpenCancellation

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

private abbrev pull (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

private abbrev exc (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  Etale.rightDerivedUpperShriek A f

private def comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    exc A (f ≫ g) ≅ exc A g ⋙ exc A f :=
  conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
    ((Etale.rightDerivedUpperShriekAdjunction A f).comp
      (Etale.rightDerivedUpperShriekAdjunction A g))
    (Etale.unboundedEtaleLowerShriekCompIso A f g)

private def congr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    exc A f ≅ exc A g :=
  eqToIso (by cases w; rfl)

private def rho (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    [HasCompactification f] : exc A f ≅ pull A f :=
  Etale.etaleSumRightAdjointIso A f (exc A f)
      (Etale.rightDerivedUpperShriekAdjunction A f) ≪≫
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm

private def source (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [IsSeparated f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Etale.dualizingComplex A (f ≫ g) ≅
      (pull A f).obj (Etale.dualizingComplex A g) :=
  (comp A f g).app (𝟙_ _) ≪≫ (rho A f).app (Etale.dualizingComplex A g)

section
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {W X Y Z : Scheme.{u}} [IsNoetherian W] [IsNoetherian X]
  [IsNoetherian Y] [IsNoetherian Z]

private theorem congr_conjugate {T S : Scheme.{u}} {f g : T ⟶ S}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    congr A w = conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction A f)
      (Etale.rightDerivedUpperShriekAdjunction A g)
      (Etale.unboundedEtaleLowerShriekCongr A w).symm := by
  subst g
  apply Iso.ext
  simp only [congr, eqToIso_refl, conjugateIsoEquiv_apply_hom,
    Etale.unboundedEtaleLowerShriekCongr, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
    conjugateEquiv_id]

-- Conjugate the compact-support associativity equation with the composite adjunctions.
private theorem exceptional_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)]
    (K : Etale.DerivedCategoryModule A Z) :
    (congr A (Category.assoc f g h)).hom.app K ≫
        (comp A f (g ≫ h)).hom.app K ≫
        (exc A f).map ((comp A g h).hom.app K) =
      (comp A (f ≫ g) h).hom.app K ≫
        (comp A f g).hom.app ((exc A h).obj K) := by
  let C := ModuleCat.{u + 1} A
  let af := Etale.rightDerivedUpperShriekAdjunction A f
  let ag := Etale.rightDerivedUpperShriekAdjunction A g
  let ah := Etale.rightDerivedUpperShriekAdjunction A h
  let afg := Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)
  let agh := Etale.rightDerivedUpperShriekAdjunction A (g ≫ h)
  let adjt := Etale.rightDerivedUpperShriekAdjunction A ((f ≫ g) ≫ h)
  let adjt' := Etale.rightDerivedUpperShriekAdjunction A (f ≫ g ≫ h)
  let cf := Etale.unboundedEtaleLowerShriekCompIso A f g
  let cg := Etale.unboundedEtaleLowerShriekCompIso A g h
  let cl := Etale.unboundedEtaleLowerShriekCompIso A (f ≫ g) h
  let cr := Etale.unboundedEtaleLowerShriekCompIso A f (g ≫ h)
  let e := Etale.unboundedEtaleLowerShriekCongr A (Category.assoc f g h)
  have hl := conjugateEquiv_comp adjt' adjt (afg.comp ah) e.hom cl.hom
  have hl' := conjugateEquiv_comp adjt' (afg.comp ah) ((af.comp ag).comp ah)
    (cl.hom ≫ e.hom) (Functor.whiskerRight cf.hom _)
  have hr := conjugateEquiv_comp adjt' (af.comp agh) (af.comp (ag.comp ah))
    cr.hom (Functor.whiskerLeft _ cg.hom)
  have hr' := conjugateEquiv_comp adjt' (af.comp (ag.comp ah)) ((af.comp ag).comp ah)
    (Functor.whiskerLeft _ cg.hom ≫ cr.hom) (Functor.associator _ _ _).hom
  rw [conjugateEquiv_whiskerRight] at hl'
  rw [conjugateEquiv_whiskerLeft] at hr
  rw [conjugateEquiv_associator_hom] at hr'
  have hc := Etale.unboundedEtaleLowerShriekCompIso_assoc A f g h
  change Functor.whiskerRight cf.hom _ ≫ cl.hom ≫ e.hom =
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ cg.hom ≫ cr.hom at hc
  have ht := congrArg (conjugateEquiv adjt' ((af.comp ag).comp ah)) hc
  rw [← hl', ← hl, ← hr', ← hr] at ht
  have hh := NatTrans.congr_app ht K
  have hi : (congr A (Category.assoc f g h)).hom ≫
      conjugateEquiv adjt' adjt e.hom = 𝟙 _ := by
    rw [congr_conjugate]
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    change conjugateEquiv adjt adjt' e.inv ≫ conjugateEquiv adjt' adjt e.hom = _
    exact conjugateEquiv_comm adjt adjt' e.inv_hom_id
  have hh' := congrArg (fun q ↦
    (congr A (Category.assoc f g h)).hom.app K ≫ q) hh
  simp only [NatTrans.comp_app, ← Category.assoc] at hh'
  rw [← NatTrans.comp_app, hi, NatTrans.id_app, Category.id_comp] at hh'
  simpa only [comp, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Category.assoc, C, af, ag, ah, afg, agh, adjt, adjt', cf, cg,
    cl, cr, e] using hh'.symm

omit [Finite A] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
private theorem pull_comp_transport
    {T : Scheme.{u}} (e : X ⟶ Y) (v : Y ⟶ T) (K : Etale.DerivedCategoryModule A T) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e v).hom.app K ≫
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) e).hom.app ((pull A v).obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) v).hom.app K) =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (e ≫ v)).hom.app K ≫
      (Etale.unboundedEtaleUpperStarCompIso A e v).hom.app K := by
  simp only [Etale.leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Etale.leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    Etale.unboundedEtaleUpperStarCompIso]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem rho_exact {T S : Scheme.{u}} (e : T ⟶ S)
    [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rho A e ≪≫ Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) e =
      Etale.etaleSumRightAdjointIso A e (exc A e)
        (Etale.rightDerivedUpperShriekAdjunction A e) := by
  simp only [rho, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

private theorem rho_comp (f : W ⟶ X) (g : X ⟶ Y)
    [Etale f] [IsSeparated f] [QuasiCompact f]
    [Etale g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : Etale.DerivedCategoryModule A Y) :
    (rho A (f ≫ g)).hom.app K ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K =
      (comp A f g).hom.app K ≫
        (rho A f).hom.app ((exc A g).obj K) ≫ (pull A f).map ((rho A g).hom.app K) := by
  let C := ModuleCat.{u + 1} A
  have hc := Etale.etaleSumRightAdjoint_comp A f g
    (exc A f)
    (exc A g)
    (exc A (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A g)
    (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)) K
  rw [← rho_exact A (f ≫ g), ← rho_exact A f, ← rho_exact A g] at hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc
  let d := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C f).app
      ((pull A g).obj K) ≪≫ (Etale.upperStar C f).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C g).app K)
  apply (cancel_mono d.hom).1
  change _ ≫ ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C f).hom.app
    ((pull A g).obj K) ≫ (Etale.upperStar C f).mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C g).hom.app K)) = _
  rw [Category.assoc, pull_comp_transport A f g K, hc]
  rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory C f).hom.naturality_assoc]
  simp only [Etale.etaleSumRightAdjointCompIso, comp, d, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, C, pull, Category.assoc]

private theorem source_comp (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [Etale f] [IsSeparated f] [QuasiCompact f]
    [Etale g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] :
    (congr A (Category.assoc f g h)).app (𝟙_ _) ≪≫
        source A f (g ≫ h) ≪≫ (pull A f).mapIso (source A g h) =
      source A (f ≫ g) h ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app
          (Etale.dualizingComplex A h) := by
  apply Iso.ext
  simp only [source, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← (rho A f).hom.naturality_assoc]
  rw [reassoc_of% exceptional_assoc A f g h]
  dsimp only [Functor.comp_obj, Etale.dualizingComplex]
  rw [← rho_comp A f g]

private theorem congr_refl {T S : Scheme.{u}} (f : T ⟶ S) [HasCompactification f] :
    congr A (rfl : f = f) = Iso.refl _ := rfl

private theorem congr_symm {T S : Scheme.{u}} {f g : T ⟶ S}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    congr A w.symm = (congr A w).symm := by
  subst g
  rfl

private theorem source_comp_eq (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (h' : X ⟶ Z) (h'' : W ⟶ Z)
    [Etale f] [IsSeparated f] [QuasiCompact f]
    [Etale g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification h] [HasCompactification h'] [HasCompactification h'']
    [HasCompactification (g ≫ h)] [HasCompactification (f ≫ h')]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)]
    (w : h' = g ≫ h) (w' : h'' = f ≫ h') :
    ((congr A (show h'' = (f ≫ g) ≫ h by rw [w', w, Category.assoc])).app (𝟙_ _) ≪≫
      source A (f ≫ g) h) ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app
          (Etale.dualizingComplex A h) =
      ((congr A w').app (𝟙_ _) ≪≫ source A f h') ≪≫
        (pull A f).mapIso ((congr A w).app (𝟙_ _) ≪≫ source A g h) := by
  subst h'
  subst h''
  rw [congr_symm A (Category.assoc f g h)]
  apply Iso.ext
  have hc := source_comp A f g h
  have hh := congrArg (fun q ↦
    ((congr A (Category.assoc f g h)).app (𝟙_ _)).inv ≫ q.hom) hc
  simpa only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    congr_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.mapIso_hom,
    Functor.map_comp, Functor.map_id, Etale.dualizingComplex, exc, pull] using hh.symm

-- The inverse-locality factorization is determined by the same counit equation.
private def restriction
    {U V B : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian B]
    (v : U ⟶ V) [Etale v] [IsSeparated v] [QuasiCompact v]
    (h : V ⟶ B) (q : U ⟶ B) [HasCompactification v]
    [HasCompactification h] [HasCompactification q] [HasCompactification (v ≫ h)]
    (hv : q = v ≫ h) (r : B ⟶ U) (z : B ⟶ V) (hz : z = r ≫ v) :
    Etale.sectionInvariant A q r ≅ Etale.sectionInvariant A h z :=
  (pull A r).mapIso ((congr A hv).app (𝟙_ _) ≪≫ source A v h) ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v z hz).app _).symm

-- Pull structural locality to the sections and use pullback associativity.
private theorem restriction_comp
    {U V T B : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian T] [IsNoetherian B]
    (v : V ⟶ T) (e : U ⟶ V)
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [Etale e] [IsSeparated e] [QuasiCompact e]
    (h : T ⟶ B) (q : V ⟶ B) (p : U ⟶ B)
    [HasCompactification v] [HasCompactification e] [HasCompactification (e ≫ v)]
    [HasCompactification h] [HasCompactification q] [HasCompactification p]
    [HasCompactification (v ≫ h)] [HasCompactification (e ≫ q)]
    [HasCompactification ((e ≫ v) ≫ h)] [HasCompactification (e ≫ v ≫ h)]
    (hv : q = v ≫ h) (he : p = e ≫ q)
    (z : B ⟶ T) (r : B ⟶ V) (s : B ⟶ U)
    (hz : z = r ≫ v) (hr : r = s ≫ e) :
    restriction A (e ≫ v) h p (by rw [he, hv, Category.assoc]) s z
        (by rw [hz, hr, Category.assoc]) =
      restriction A e q p he s r hr ≪≫ restriction A v h q hv r z hz := by
  exact SectionRestriction.section_comp A v e z r s hz hr
    (Etale.dualizingComplex A h) (Etale.dualizingComplex A q)
    (Etale.dualizingComplex A p) _ _ _ (source_comp_eq A e v h q p hv he)

end

end OpenCancellation

end WeilConjectures.PurityFiniteSetting
