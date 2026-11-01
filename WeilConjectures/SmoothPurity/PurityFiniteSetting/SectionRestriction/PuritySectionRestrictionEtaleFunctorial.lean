/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-! # Functoriality in ordinary-etale section coordinates

Source: blueprint latest, sec-smooth-purity, orientation charts Step 3 and
composition coherence Step 1 (blueprint: lem-pur-section-restriction-etale-functorial).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

local notation "exc" => AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.exceptional

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

section
variable (P : PurityFiniteSetting.{u})
  {W X Y Z : Scheme.{u}}
  [W.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [Y.Over (Spec (.of P.field.k))] [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (W ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

private theorem exceptional_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).hom.app K ≫
        (comp P f (g ≫ h)).hom.app K ≫
        (exc P f).map ((comp P g h).hom.app K) =
      (comp P (f ≫ g) h).hom.app K ≫
        (comp P f g).hom.app ((exc P h).obj K) := by
  let := fieldSchemeNoetherian P W
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := fieldSchemeNoetherian P Z
  let := compactification P f
  let := compactification P g
  let := compactification P h
  let := compactification P (f ≫ g)
  let := compactification P (g ≫ h)
  let := compactification P ((f ≫ g) ≫ h)
  let := compactification P (f ≫ g ≫ h)
  let A := ModuleCat.{u + 1} P.Coefficient
  let af := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
  let ag := Etale.rightDerivedUpperShriekAdjunction P.Coefficient g
  let ah := Etale.rightDerivedUpperShriekAdjunction P.Coefficient h
  let afg := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (f ≫ g)
  let agh := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (g ≫ h)
  let adjt := Etale.rightDerivedUpperShriekAdjunction P.Coefficient ((f ≫ g) ≫ h)
  let adjt' := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (f ≫ g ≫ h)
  let cf := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient f g
  let cg := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient g h
  let cl := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient (f ≫ g) h
  let cr := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient f (g ≫ h)
  let e := Etale.unboundedEtaleLowerShriekCongr P.Coefficient (Category.assoc f g h)
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
  have hc := Etale.unboundedEtaleLowerShriekCompIso_assoc P.Coefficient f g h
  change Functor.whiskerRight cf.hom _ ≫ cl.hom ≫ e.hom =
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ cg.hom ≫ cr.hom at hc
  have ht := congrArg (conjugateEquiv adjt' ((af.comp ag).comp ah)) hc
  rw [← hl', ← hl, ← hr', ← hr] at ht
  have hh := NatTrans.congr_app ht K
  have hi : (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).hom ≫
      conjugateEquiv adjt' adjt e.hom = 𝟙 _ := by
    simp only [AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.congr,
      conjugateIsoEquiv_apply_hom]
    change conjugateEquiv adjt adjt'
      (Etale.unboundedEtaleLowerShriekCongr P.Coefficient
        (Category.assoc f g h).symm).hom ≫ conjugateEquiv adjt' adjt e.hom = _
    rw [← lowerCongr_symm P.Coefficient (Category.assoc f g h)]
    exact conjugateEquiv_comm adjt adjt' e.inv_hom_id
  have hh' := congrArg (fun q ↦
    (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).hom.app K ≫ q) hh
  simp only [NatTrans.comp_app, ← Category.assoc] at hh'
  rw [← NatTrans.comp_app, hi, NatTrans.id_app, Category.id_comp] at hh'
  simpa only [comp, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Category.assoc, A, af, ag, ah, afg, agh, adjt, adjt', cf, cg,
    cl, cr, e] using hh'.symm

private theorem rho_comp (f : W ⟶ X) (g : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Etale g]
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (rho P (f ≫ g)).hom.app K ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app K =
      (comp P f g).hom.app K ≫
        (rho P f).hom.app ((exc P g).obj K) ≫ (pull P f).map ((rho P g).hom.app K) := by
  let := fieldSchemeNoetherian P W
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := compactification P f
  let := compactification P g
  let := compactification P (f ≫ g)
  let C := ModuleCat.{u + 1} P.Coefficient
  have hc := Etale.etaleSumRightAdjoint_comp P.Coefficient f g
    (exc P f)
    (exc P g)
    (exc P (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient g)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (f ≫ g)) K
  rw [← rho_exact P (f ≫ g), ← rho_exact P f, ← rho_exact P g] at hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc
  let d := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C f).app
      ((pull P g).obj K) ≪≫ (Etale.upperStar C f).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C g).app K)
  apply (cancel_mono d.hom).1
  change _ ≫ ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C f).hom.app
    ((pull P g).obj K) ≫ (Etale.upperStar C f).mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C g).hom.app K)) = _
  rw [Category.assoc, pull_comp_transport P f g K, hc]
  rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory C f).hom.naturality_assoc]
  simp only [Etale.etaleSumRightAdjointCompIso, comp, d, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, C, pull, Category.assoc]

private theorem source_comp (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Etale g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).app (𝟙_ _) ≪≫
        sourceEtale P f (g ≫ h) ≪≫ (pull P f).mapIso (sourceEtale P g h) =
      sourceEtale P (f ≫ g) h ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).app
          (omega P h) := by
  apply Iso.ext
  simp only [sourceEtale, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← (rho P f).hom.naturality_assoc]
  rw [reassoc_of% exceptional_assoc P f g h]
  dsimp only [Functor.comp_obj, omega, Etale.dualizingComplex]
  rw [← rho_comp P f g]

private theorem congr_refl (f : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    congr P f f rfl = Iso.refl _ := by
  apply Iso.ext
  simp only [AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.congr,
    conjugateIsoEquiv_apply_hom, Etale.unboundedEtaleLowerShriekCongr,
    Iso.refl_hom, conjugateEquiv_id]

private theorem congr_symm (f g : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (w : f = g) :
    congr P g f w.symm = (congr P f g w).symm := by
  subst g
  rw [congr_refl]
  rfl

private theorem source_comp_eq (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (h' : X ⟶ Z) (h'' : W ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))] [h'.IsOver (Spec (.of P.field.k))]
    [h''.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Etale g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [IsSeparated h''] [LocallyOfFiniteType h''] [QuasiCompact h'']
    (w : h' = g ≫ h) (w' : h'' = f ≫ h') :
    ((congr P h'' ((f ≫ g) ≫ h)
        (by rw [w', w, Category.assoc])).app (𝟙_ _) ≪≫
      sourceEtale P (f ≫ g) h) ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).app
          (omega P h) =
      ((congr P h'' (f ≫ h') w').app (𝟙_ _) ≪≫ sourceEtale P f h') ≪≫
        (pull P f).mapIso
          ((congr P h' (g ≫ h) w).app (𝟙_ _) ≪≫ sourceEtale P g h) := by
  subst h'
  subst h''
  rw [congr_symm P _ _ (Category.assoc f g h)]
  apply Iso.ext
  have hc := source_comp P f g h
  have hh := congrArg (fun q ↦
    ((congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).app (𝟙_ _)).inv ≫
      q.hom) hc
  dsimp only [omega, coefficientUnit,
    AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.exceptional,
    Etale.dualizingComplex] at hh ⊢
  simpa only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    congr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.mapIso_hom,
    Functor.map_comp, (pull P f).map_id] using hh.symm

end

private theorem section_comp (A : Type (u + 1)) [CommRing A]
    {B X₀ X₁ X₂ : Scheme.{u}} (a : X₁ ⟶ X₀) (b : X₂ ⟶ X₁)
    (s₀ : B ⟶ X₀) (s₁ : B ⟶ X₁) (s₂ : B ⟶ X₂)
    (ha : s₀ = s₁ ≫ a) (hb : s₁ = s₂ ≫ b)
    (K₀ : Etale.DerivedCategoryModule A X₀)
    (K₁ : Etale.DerivedCategoryModule A X₁)
    (K₂ : Etale.DerivedCategoryModule A X₂)
    (ea : K₁ ≅ (Etale.upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj K₀)
    (eb : K₂ ≅ (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj K₁)
    (eab : K₂ ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) (b ≫ a)).leftDerivedFunctor.obj K₀)
    (he : eab ≪≫ (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b a).app K₀ =
      eb ≪≫ (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.mapIso ea) :
    (Etale.upperStar (ModuleCat.{u + 1} A) s₂).leftDerivedFunctor.mapIso eab ≪≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₂ (b ≫ a) s₀
          (by rw [ha, hb, Category.assoc])).app K₀).symm =
      ((Etale.upperStar (ModuleCat.{u + 1} A) s₂).leftDerivedFunctor.mapIso eb ≪≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₂ b s₁ hb).app K₁).symm) ≪≫
      ((Etale.upperStar (ModuleCat.{u + 1} A) s₁).leftDerivedFunctor.mapIso ea ≪≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₁ a s₀ ha).app K₀).symm) := by
  let C := ModuleCat.{u + 1} A
  have hc := Etale.leftDerivedUpperStarComp_assoc'_app C s₂ b a s₁ (b ≫ a) s₀
    hb rfl ha K₀
  have hn := (Etale.leftDerivedUpperStarComp C s₂ b s₁ hb).inv.naturality ea.hom
  have hh := congrArg Iso.hom he
  dsimp only [C] at hc hn
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc] at hh ⊢
  apply (cancel_mono ((Etale.leftDerivedUpperStarComp C s₁ a s₀ ha).hom.app K₀ ≫
    (Etale.leftDerivedUpperStarComp C s₂ b s₁ hb).hom.app
      ((Etale.upperStar C a).leftDerivedFunctor.obj K₀))).1
  dsimp only [C]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, hh]
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Functor.comp_obj, Category.comp_id]

private theorem restrictionEtale_comp (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ}
    (X'' X' X : Pair B d) (b : EtaleMap X'' X') (a : EtaleMap X' X) :
    restrictionEtale P aB (b.comp a) =
      restrictionEtale P aB b ≪≫ restrictionEtale P aB a := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let := SmoothOfRelativeDimension.smooth d X''.g
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  let : X.V.Over (Spec (.of P.field.k)) := ⟨X.g ≫ aB⟩
  let : X'.V.Over (Spec (.of P.field.k)) := ⟨X'.g ≫ aB⟩
  let : X''.V.Over (Spec (.of P.field.k)) := ⟨X''.g ≫ aB⟩
  let : X.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : X'.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : X''.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : a.map.IsOver (Spec (.of P.field.k)) := ⟨by
    change a.map ≫ (X.g ≫ aB) = X'.g ≫ aB
    rw [← Category.assoc, a.over_eq]⟩
  let : b.map.IsOver (Spec (.of P.field.k)) := ⟨by
    change b.map ≫ (X'.g ≫ aB) = X''.g ≫ aB
    rw [← Category.assoc, b.over_eq]⟩
  let : LocallyOfFiniteType (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.g ≫ aB))
  let : QuasiCompact (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X.g ≫ aB))
  let : LocallyOfFiniteType (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X'.g ≫ aB))
  let : QuasiCompact (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X'.g ≫ aB))
  let : LocallyOfFiniteType (X''.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X''.g ≫ aB))
  let : QuasiCompact (X''.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X''.g ≫ aB))
  have he := source_comp_eq P b.map a.map X.g X'.g X''.g
    a.over_eq.symm b.over_eq.symm
  exact section_comp P.Coefficient a.map b.map X.s X'.s X''.s
    a.section_eq.symm b.section_eq.symm (omega P X.g) (omega P X'.g) (omega P X''.g)
    _ _ _ he

/-- The ordinary-etale restriction formula preserves identities and composites.
Source: blueprint orientation charts Step 3 and composition coherence Step 1
(blueprint: lem-pur-section-restriction-etale-functorial).
Proof: write E(a,g) as the specified exceptional compositor at the coefficient unit
followed by rho(a) at omega(g), inserting the congruence g' = a g. Conjugating
compact-support associativity gives the associator of the exceptional compositor.
The composition law for rho and its naturality identify E(ba,g) with
E(b,ag) followed by Lb*E(a,g), through the pullback compositor. Pull back by the
second section. Threefold pullback coherence and the section equations cancel
the intermediate compositors. The identity laws of rho, exceptional composition,
and pullback give the first clause. This uses the fixed finite coefficients and
works also in dimension zero and on the empty base; no orientation is chosen. -/
theorem restrictionEtale_functorial (P : PurityFiniteSetting.{u}) :
    ∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
      [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB] (d : ℕ),
      (∀ X : Pair B d, restrictionEtale P aB (EtaleMap.id X) = Iso.refl _) ∧
      (∀ (X'' X' X : Pair B d) (b : EtaleMap X'' X') (a : EtaleMap X' X),
        restrictionEtale P aB (b.comp a) =
          restrictionEtale P aB b ≪≫ restrictionEtale P aB a) := by
  intro B aB _ _ _ d
  have hc := restrictionEtale_comp P aB (d := d)
  refine ⟨?_, hc⟩
  intro X
  have hid : (EtaleMap.id X).comp (EtaleMap.id X) = EtaleMap.id X := by
    simp only [EtaleMap.comp, EtaleMap.id, Category.id_comp]
  have h := hc X X X (EtaleMap.id X) (EtaleMap.id X)
  rw [hid] at h
  apply Iso.ext
  apply (cancel_epi (restrictionEtale P aB (EtaleMap.id X)).hom).1
  simpa only [Iso.trans_hom, Iso.refl_hom, Category.comp_id] using
    (congrArg Iso.hom h).symm

end WeilConjectures.PurityFiniteSetting.SectionRestriction
