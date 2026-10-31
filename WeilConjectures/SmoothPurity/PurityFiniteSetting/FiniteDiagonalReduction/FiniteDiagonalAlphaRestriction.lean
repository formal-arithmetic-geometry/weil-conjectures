/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.RestrictionGeometry.FiniteDiagonalRestrictionGeometry
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleRhoUnitSquare
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DualizingUnitComposite
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalExchangeNaturality
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleAlphaSquare
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! # Alpha open restriction

Source: orientation charts, Steps 1--4.
(blueprint: lem-pur-finite-diagonal-alpha-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open RestrictionGeometry

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  ProEtale.upperStar ProEtale.comparisonUpperStar
  chartDualizingUnit diagonalDualizingComparison Dnc.sourceComparison

attribute [local implicit_reducible] Etale.dualizingComplex Dnc.sourceEtale
  Dnc.sourceSection SectionRestriction.sectionEtale
  diagonalPair mixedPair sourceSquare ambientRestriction

open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

private theorem pullSquare_eq (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} (a : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (b : Y' ⟶ Y) (sq : CommSq a f' f b)
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (ProEtale.DualizingLocality.pullSquare P a f' f b sq).app K =
      Etale.sectionCoherencePullbackIso P.Coefficient a f f' b sq.w K := by
  exact Etale.sectionPullback_endpoint P.Coefficient a f f' b
    (f' ≫ b) (a ≫ f) sq.w.symm rfl rfl sq.w K

private theorem source_identity (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (congr P f (𝟙 X ≫ f) (Category.id_comp f).symm).app (𝟙_ _) ≪≫
        sourceEtale P (𝟙 X) f =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X).symm.app
        (omega P f) := by
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := compactification P f
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := Etale.dualizingComplex P.Coefficient f
  rw [SectionRestriction.sourceEtale_locality_congr P (𝟙 X) f f (Category.id_comp f)]
  let E := Etale.sectionStructuralLocalityIso P.Coefficient (𝟙 X) f f
    (Category.id_comp f)
  change E.symm = (Etale.leftDerivedUpperStarId C X).symm.app K
  have aux (c : X ⟶ X) [Etale c] [IsSeparated c]
      [LocallyOfFiniteType c] [QuasiCompact c]
      [c.IsOver (Spec (.of P.field.k))] (hc : c = 𝟙 X ≫ 𝟙 X) :
      (pull P (𝟙 X)).mapIso E ≪≫ E =
        (Etale.leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) c hc).symm.app K ≪≫
          Etale.sectionStructuralLocalityIso P.Coefficient c f f
            (by rw [hc, Category.assoc, Category.id_comp, Category.id_comp]) := by
    subst c
    exact locality_comp P (𝟙 X) (𝟙 X) f f f
      (Category.id_comp f).symm (Category.id_comp f).symm
  have hs := aux (𝟙 X) (Category.id_comp (𝟙 X)).symm
  have hh : (pull P (𝟙 X)).map E.hom ≫ E.hom =
      (Etale.leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp _).symm).inv.app K ≫ E.hom := by
    exact congrArg Iso.hom hs
  have he : (pull P (𝟙 X)).map E.hom =
      (Etale.leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp _).symm).inv.app K := (cancel_mono E.hom).mp hh
  have hu := Etale.leftDerivedUpperStarComp_id_left_hom_app C (𝟙 X) K
  have hu' : (Etale.leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp _).symm).inv.app K =
      (Etale.leftDerivedUpperStarId C X).hom.app ((pull P (𝟙 X)).obj K) := by
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _).symm).hom.app K)).mp
    simpa only [Iso.hom_inv_id_app] using hu.symm
  have hn := (Etale.leftDerivedUpperStarId C X).hom.naturality E.hom
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [he, hu'] at hn
  have hid : E = (Etale.leftDerivedUpperStarId C X).app K := by
    apply Iso.ext
    exact ((cancel_epi ((Etale.leftDerivedUpperStarId C X).hom.app
      ((pull P (𝟙 X)).obj K))).mp hn).symm
  exact congrArg Iso.symm hid

private theorem restriction_congr_left (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (f g : X ⟶ Y) (h : X' ⟶ Y')
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [Etale a] [IsSeparated a] [QuasiCompact a]
    [Etale b] [IsSeparated b] [QuasiCompact b]
    (w : f = g) (sq : CommSq a h f b) (sq' : CommSq a h g b) :
    (pull P a).mapIso ((congr P f g w).app (𝟙_ _)) ≪≫
        ProEtale.DualizingLocality.restriction P g h a b sq' =
      ProEtale.DualizingLocality.restriction P f h a b sq := by
  subst g
  rw [SectionRestriction.congr_refl]
  change (pull P a).mapIso (Iso.refl _) ≪≫ _ = _
  simp only [CategoryTheory.Functor.mapIso_refl]
  exact Iso.refl_trans _

private theorem restriction_factor (P : PurityFiniteSetting.{u})
    {W Q R B B' : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))] [Q.Over (Spec (.of P.field.k))]
    [R.Over (Spec (.of P.field.k))] [B.Over (Spec (.of P.field.k))]
    [B'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Q ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B' ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (Q ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B' ↘ Spec (.of P.field.k))]
    (d : ℕ) (f : W ⟶ B) (g : Q ⟶ B') (h : R ⟶ B')
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d g]
    (t : R ⟶ Q) (m : Q ⟶ W) (j : B' ⟶ B)
    [t.IsOver (Spec (.of P.field.k))] [m.IsOver (Spec (.of P.field.k))]
    [j.IsOver (Spec (.of P.field.k))]
    [IsOpenImmersion t] [QuasiCompact t]
    [IsOpenImmersion m] [QuasiCompact m]
    [IsOpenImmersion j] [QuasiCompact j]
    (ht : t ≫ g = h) (hm : m ≫ f = g ≫ j) :
    letI := compactification P g
    letI := compactification P h
    letI := fieldSchemeNoetherian P Q
    letI := fieldSchemeNoetherian P R
    letI := fieldSchemeNoetherian P B'
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) t m).app
        (omega P f) ≪≫
      (pull P t).mapIso (ProEtale.DualizingLocality.restriction P f g m j ⟨hm⟩) ≪≫
      Etale.sectionStructuralLocalityIso P.Coefficient t g h ht =
    ProEtale.DualizingLocality.restriction P f h (t ≫ m) j
      ⟨by rw [Category.assoc, hm, ← Category.assoc, ht]⟩ := by
  subst h
  let := compactification P g
  let := compactification P (t ≫ g)
  let := fieldSchemeNoetherian P Q
  let := fieldSchemeNoetherian P R
  let := fieldSchemeNoetherian P B'
  let C := ModuleCat.{u + 1} P.Coefficient
  have he := (ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality P).2.2.2.2.2.2.1
    (𝟙 W) f d t g d (t ≫ m) m j
    ⟨by simp⟩ ⟨hm⟩
  let cg := (congr P f (𝟙 W ≫ f) (Category.id_comp f).symm).app (𝟙_ _)
  have hc := congrArg Iso.hom (restriction_congr_left P f (𝟙 W ≫ f) (t ≫ g)
    (t ≫ m) j (Category.id_comp f).symm
    ⟨by rw [Category.assoc, hm, ← Category.assoc]⟩
    ((show CommSq (t ≫ m) t (𝟙 W) m from ⟨by simp⟩).vert_comp ⟨hm⟩))
  have he' := congrArg (fun z ↦ (pull P (t ≫ m)).map cg.hom ≫ z) he
  have hi := congrArg Iso.hom (source_identity P f)
  change (pull P (t ≫ m)).map cg.hom ≫
      (ProEtale.DualizingLocality.restriction P (𝟙 W ≫ f) (t ≫ g) (t ≫ m) j
        ((show CommSq (t ≫ m) t (𝟙 W) m from ⟨by simp⟩).vert_comp ⟨hm⟩)).hom =
      (ProEtale.DualizingLocality.restriction P f (t ≫ g) (t ≫ m) j
        ⟨by rw [Category.assoc, hm, ← Category.assoc]⟩).hom at hc
  change cg.hom ≫ (sourceEtale P (𝟙 W) f).hom = _ at hi
  erw [← CategoryTheory.Functor.map_comp_assoc] at he'
  rw [hi] at he'
  rw [reassoc_of% hc] at he'
  rw [SectionRestriction.sourceEtale_locality P t g] at he'
  have hu := Etale.leftDerivedUpperStarComp_id_right_hom_app C (t ≫ m) (omega P f)
  have hu' : (pull P (t ≫ m)).map
      ((Etale.leftDerivedUpperStarId C W).inv.app (omega P f)) =
      (Etale.leftDerivedUpperStarComp C (t ≫ m) (𝟙 W) (t ≫ m)
        (Category.comp_id _).symm).hom.app (omega P f) := by
    apply (cancel_mono ((pull P (t ≫ m)).map
      ((Etale.leftDerivedUpperStarId C W).hom.app (omega P f)))).mp
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    exact hu.symm
  simp only [ProEtale.DualizingLocality.pullSquare, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Category.assoc] at he'
  rw [hu'] at he'
  change (Etale.leftDerivedUpperStarComp C (t ≫ m) (𝟙 W) (t ≫ m)
      (Category.comp_id _).symm).hom.app (omega P f) ≫
      (Etale.leftDerivedUpperStarComp C (t ≫ m) (𝟙 W) (t ≫ m)
        (Category.comp_id _).symm).inv.app (omega P f) ≫
      (Etale.leftDerivedUpperStarComp C t m).hom.app (omega P f) ≫
      (pull P t).map (ProEtale.DualizingLocality.restriction P f g m j ⟨hm⟩).hom =
    (ProEtale.DualizingLocality.restriction P f (t ≫ g) (t ≫ m) j
      ⟨by rw [Category.assoc, hm, ← Category.assoc]⟩).hom ≫
      (Etale.sectionStructuralLocalityIso P.Coefficient t g (t ≫ g) rfl).inv at he'
  rw [Iso.hom_inv_id_app_assoc] at he'
  apply Iso.ext
  have he' := congrArg (fun z ↦ z ≫
    (Etale.sectionStructuralLocalityIso P.Coefficient t g (t ≫ g) rfl).hom) he'
  simpa only [Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using he'

variable {X Y : Scheme.{u}} [IsNoetherian X]
variable (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
variable [SmoothOfRelativeDimension d (f.resLE V.1 U.1 hUV)]
variable (P : PurityFiniteSetting.{u})
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

private def ordinaryAlpha :=
  let := Dnc.compactifiable P f aY
  let := (P.comparedDiagonalBaseChange d f (f ≫ aY) aY rfl).2.2.2.1
  P.diagonalComparedRestriction f
    (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f).flip))

private def ordinaryRestriction :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI := Dnc.compactifiable P f aY
  let h := f.resLE V.1 U.1 hUV
  letI : IsAffine U.1.toScheme := U.2
  letI : IsAffine V.1.toScheme := V.2
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aY⟩
  letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  letI : U.1.toScheme.Over (Spec (.of P.field.k)) := ⟨U.1.ι ≫ f ≫ aY⟩
  letI : V.1.toScheme.Over (Spec (.of P.field.k)) := ⟨V.1.ι ≫ aY⟩
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aY))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ aY))
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (aY))
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (aY))
  letI : LocallyOfFiniteType (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.1.ι ≫ f ≫ aY))
  letI : QuasiCompact (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.1.ι ≫ f ≫ aY))
  letI : LocallyOfFiniteType (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.1.ι ≫ aY))
  letI : QuasiCompact (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (V.1.ι ≫ aY))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : U.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : V.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h.IsOver (Spec (.of P.field.k)) := ⟨by
    change h ≫ V.1.ι ≫ aY = U.1.ι ≫ f ≫ aY
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]⟩
  letI := Dnc.compactifiable P h (V.1.ι ≫ aY)
  ProEtale.DualizingLocality.restriction P f h U.1.ι V.1.ι
    ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩

private def ordinarySource :=
  let := SmoothOfRelativeDimension.smooth d (diagonalPair d f).g
  let := SmoothOfRelativeDimension.smooth d (mixedPair d f U).g
  let aU := (f.resLE V.1 U.1 hUV) ≫ V.1.ι ≫ aY
  let := Dnc.compactifiable P (diagonalPair d f).g (f ≫ aY)
  let := Dnc.compactifiable P (mixedPair d f U).g aU
  let := Dnc.invertibleExponent P ((diagonalPair d f).g ≫ f ≫ aY)
  Dnc.sectionBaseChange P.Coefficient d (diagonalPair d f).g
      (sourceSquare d f U).square (diagonalPair d f).s (mixedPair d f U).s
      (sourceSquare d f U).section_eq ≪≫
    (SectionRestriction.restrictionEtale P aU (ambientRestriction d f U V hUV)).symm

omit [IsSeparated aY] in
set_option maxRecDepth 10000 in
-- Matching the canonical compactification presentations needs a larger recursion limit.
set_option maxHeartbeats 800000 in
-- The ordinary comparison carries several explicit compactification dictionaries.
private theorem ordinary_square [_hSepaY : IsSeparated aY] :
    (pull P U.1.ι).mapIso (ordinaryAlpha d f P aY) ≪≫
        ordinaryRestriction f U V hUV P aY =
      ordinarySource d f U V hUV P aY ≪≫
        ordinaryAlpha d (f.resLE V.1 U.1 hUV) P (V.1.ι ≫ aY) := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  let h := f.resLE V.1 U.1 hUV
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  let : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aY⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let : U.1.toScheme.Over (Spec (.of P.field.k)) := ⟨U.1.ι ≫ f ≫ aY⟩
  let : V.1.toScheme.Over (Spec (.of P.field.k)) := ⟨V.1.ι ≫ aY⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aY))
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ aY))
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (aY))
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (aY))
  let : LocallyOfFiniteType (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.1.ι ≫ f ≫ aY))
  let : QuasiCompact (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.1.ι ≫ f ≫ aY))
  let : LocallyOfFiniteType (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.1.ι ≫ aY))
  let : QuasiCompact (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (V.1.ι ≫ aY))
  let : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : U.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : V.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : h.IsOver (Spec (.of P.field.k)) := ⟨by
    change h ≫ V.1.ι ≫ aY = U.1.ι ≫ f ≫ aY
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]⟩
  let := Dnc.compactifiable P h (V.1.ι ≫ aY)
  let C := ModuleCat.{u + 1} P.Coefficient
  let p := pullback.fst f f
  let q := pullback.snd f f
  let p' := pullback.fst h h
  let q' := pullback.snd h h
  let m := mixedMap d f U
  let t := ambientMap d f U V hUV
  let H := t ≫ m
  have hm : m ≫ p = (mixedPair d f U).g ≫ U.1.ι :=
    (sourceSquare d f U).square.w
  have ht : t ≫ (mixedPair d f U).g = p' :=
    (ambientRestriction d f U V hUV).over_eq
  have hq : H ≫ q = q' ≫ U.1.ι := by
    dsimp only [H, t, m, ambientMap, mixedMap, mixedPair, q, q', h]
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hp : H ≫ p = p' ≫ U.1.ι := by
    rw [Category.assoc, hm, ← Category.assoc, ht]
  have hd : pullback.diagonal h ≫ H = U.1.ι ≫ pullback.diagonal f := by
    dsimp only [p, p'] at hp
    dsimp only [q, q'] at hq
    apply pullback.hom_ext <;>
      simp only [Category.assoc, hp, hq, pullback.diagonal_fst,
        pullback.diagonal_snd, pullback.diagonal_fst_assoc,
        pullback.diagonal_snd_assoc, Category.comp_id]
  let z := (mixedPair d f U).g
  let := SmoothOfRelativeDimension.smooth d z
  let := SmoothOfRelativeDimension.smooth d p
  let : IsOpenImmersion m := MorphismProperty.of_isPullback
    (sourceSquare d f U).square.flip inferInstance
  let : QuasiCompact m := MorphismProperty.of_isPullback
    (sourceSquare d f U).square.flip inferInstance
  let : IsOpenImmersion t := MorphismProperty.of_isPullback
    (ambientSquare d f U V hUV).flip inferInstance
  let : QuasiCompact t := MorphismProperty.of_isPullback
    (ambientSquare d f U V hUV).flip inferInstance
  let : (pullback f f).Over (Spec (.of P.field.k)) := ⟨p ≫ f ≫ aY⟩
  let : (mixedPair d f U).V.Over (Spec (.of P.field.k)) :=
    ⟨z ≫ U.1.ι ≫ f ≫ aY⟩
  let : (pullback h h).Over (Spec (.of P.field.k)) := ⟨p' ≫ U.1.ι ≫ f ≫ aY⟩
  let : LocallyOfFiniteType ((pullback f f) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ f ≫ aY))
  let : QuasiCompact ((pullback f f) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (p ≫ f ≫ aY))
  let : LocallyOfFiniteType ((mixedPair d f U).V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (z ≫ U.1.ι ≫ f ≫ aY))
  let : QuasiCompact ((mixedPair d f U).V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (z ≫ U.1.ι ≫ f ≫ aY))
  let : LocallyOfFiniteType ((pullback h h) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (p' ≫ U.1.ι ≫ f ≫ aY))
  let : QuasiCompact ((pullback h h) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (p' ≫ U.1.ι ≫ f ≫ aY))
  let : p.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : q.IsOver (Spec (.of P.field.k)) := ⟨by
    change q ≫ f ≫ aY = p ≫ f ≫ aY
    rw [← Category.assoc, ← Category.assoc, pullback.condition]⟩
  let : z.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : p'.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : q'.IsOver (Spec (.of P.field.k)) := ⟨by
    change q' ≫ U.1.ι ≫ f ≫ aY = p' ≫ U.1.ι ≫ f ≫ aY
    simp only [← Scheme.Hom.resLE_comp_ι f hUV, ← Category.assoc]
    rw [pullback.condition]⟩
  let : m.IsOver (Spec (.of P.field.k)) := ⟨by
    change m ≫ p ≫ f ≫ aY = z ≫ U.1.ι ≫ f ≫ aY
    simpa only [Category.assoc, z] using congrArg (fun k ↦ k ≫ f ≫ aY) hm⟩
  let : t.IsOver (Spec (.of P.field.k)) := ⟨by
    change t ≫ z ≫ U.1.ι ≫ f ≫ aY = p' ≫ U.1.ι ≫ f ≫ aY
    rw [← Category.assoc, ht]⟩
  let := fieldSchemeNoetherian P (pullback f f)
  let := fieldSchemeNoetherian P (mixedPair d f U).V
  let := fieldSchemeNoetherian P (pullback h h)
  let := compactification P p
  let : HasCompactification (diagonalPair d f).g :=
    inferInstanceAs (HasCompactification p)
  let := compactification P z
  let := compactification P p'
  let := (P.comparedDiagonalBaseChange d f (f ≫ aY) aY rfl).2.2.2.1
  let := (P.comparedDiagonalBaseChange d h (h ≫ V.1.ι ≫ aY)
    (V.1.ι ≫ aY) rfl).2.2.2.1
  let c := ProEtale.DualizingLocality.restriction P p p' H U.1.ι ⟨hp⟩
  let r := ProEtale.DualizingLocality.restriction P f h U.1.ι V.1.ι
    ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩
  have hb := (ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality P).2.2.2.2.2.2.2.1
    f d p d f q h d p' d h q' U.1.ι V.1.ι H U.1.ι
    (IsPullback.of_hasPullback f f).flip (IsPullback.of_hasPullback h h).flip
    ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩ ⟨hp⟩ ⟨hq⟩
    ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩
  let : HasInvertibleExponent P.Coefficient (diagonalPair d f).V :=
    Dnc.invertibleExponent P ((diagonalPair d f).g ≫ f ≫ aY)
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient (diagonalPair d f).g d (sourceSquare d f U).square
  let := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient
    (sourceSquare d f U).square).2
    (inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient
      (sourceSquare d f U).square).app (𝟙_ _))))
  let bs := asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
    (sourceSquare d f U).square)
  have hbs : (ProEtale.DualizingLocality.restriction P p z m U.1.ι
      (sourceSquare d f U).square.toCommSq).hom =
      Etale.dualizingComplexBaseChangeMap P.Coefficient (sourceSquare d f U).square := by
    let := compactification P U.1.ι
    let := compactification P (z ≫ U.1.ι)
    have hb := (ProEtale.finite_etale_dualizing_normalization P U.1.ι).smooth_base_change
      p z m (sourceSquare d f U).square
    obtain ⟨s, hs, hi, _⟩ := P.dualizingComposite_inverse z U.1.ι (eta P U.1.ι)
    have hσ : sigma P.Coefficient z U.1.ι (comp P z U.1.ι) =
        dualizingCompositeSigma P.Coefficient z U.1.ι := by
      simp only [sigma, dualizingCompositeSigma, dualizingCompositeConjugate,
        finiteExceptionalComposition, comp, Etale.dualizingComplexTensorMap, Iso.app_inv]
    rw [← hσ] at hs
    have hi' : s.inv ≫ (targetUnit P.Coefficient z U.1.ι (rho P U.1.ι)).hom =
        (comp P z U.1.ι).hom.app
            (ProEtale.FiniteEtaleNormalization.coefficientUnit
              (ModuleCat.{u + 1} P.Coefficient) X) ≫
          (ProEtale.FiniteEtaleNormalization.exceptional P z).map (eta P U.1.ι).hom := hi
    have hb' := congrArg (fun q ↦ q ≫ s.inv ≫
      (targetUnit P.Coefficient z U.1.ι (rho P U.1.ι)).hom) hb
    rw [← hs] at hb'
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] at hb'
    rw [hi'] at hb'
    simpa only [ProEtale.DualizingLocality.restriction, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc,
      ProEtale.FiniteEtaleNormalization.beta, ProEtale.FiniteEtaleNormalization.baseChange,
      Etale.dualizingComplexBaseChangeMap] using hb'.symm
  have hfactor := restriction_factor P d p z p' t m U.1.ι ht hm
  have hbs' : ProEtale.DualizingLocality.restriction P p z m U.1.ι
      (sourceSquare d f U).square.toCommSq = bs := Iso.ext hbs
  rw [hbs'] at hfactor
  have he :
      (pull P H).mapIso
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback f f).flip)) ≪≫ c =
        Etale.sectionCoherencePullbackIso P.Coefficient H q q' U.1.ι hq (omega P f) ≪≫
          (pull P q').mapIso r ≪≫
          asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback h h).flip) := by
    change (pull P H).map
        (Etale.dualizingComplexBaseChangeMap P.Coefficient
          (IsPullback.of_hasPullback f f).flip) ≫ c.hom =
      ((ProEtale.DualizingLocality.pullSquare P H q' q U.1.ι ⟨hq⟩).app
        (omega P f)).hom ≫ (pull P q').map r.hom ≫
        Etale.dualizingComplexBaseChangeMap P.Coefficient
          (IsPullback.of_hasPullback h h).flip at hb
    rw [pullSquare_eq] at hb
    apply Iso.ext
    simpa only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
      asIso_hom, Category.assoc] using hb
  have hs := section_inverse_exchange_naturality P.Coefficient U.1.ι q q' H
    (pullback.diagonal f) (pullback.diagonal h) hq hd
    (pullback.diagonal_snd f) (pullback.diagonal_snd h)
    (omega P f) (omega P h) (omega P p) (omega P p')
    (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f).flip))
    (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback h h).flip)) r c he
  have hc : ordinarySource d f U V hUV P aY =
      Etale.sectionCoherencePullbackIso P.Coefficient U.1.ι
        (pullback.diagonal f) (pullback.diagonal h) H hd.symm (omega P p) ≪≫
      (pull P (pullback.diagonal h)).mapIso c := by
    have hsf := section_factorization P.Coefficient U.1.ι (pullback.diagonal f) m t
      (mixedPair d f U).s (pullback.diagonal h)
      (sourceSquare d f U).section_eq (ambientRestriction d f U V hUV).section_eq
      (omega P p) (omega P z) (omega P p') bs
      (Etale.sectionStructuralLocalityIso P.Coefficient t z p' ht)
    dsimp only [Etale.ordinaryFinitePullback] at hsf
    rw [hfactor] at hsf
    dsimp only [ordinarySource]
    rw [SectionRestriction.restrictionEtale_locality]
    dsimp only [Dnc.sectionBaseChange, SectionRestriction.localityRestriction]
    erw [Iso.symm_symm_eq]
    dsimp only [Etale.sectionCoherencePullbackIso] at hsf ⊢
    simp only [Iso.trans_assoc] at hsf
    erw [Iso.trans_assoc, Iso.trans_assoc, Iso.trans_assoc]
    exact hsf
  rw [hc]
  exact hs.trans (Iso.trans_assoc _ _ _).symm

private theorem transport_alpha
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (A : C ⥤ D) (B : E ⥤ F) (R : D ⥤ F) (S : C ⥤ E)
    {c w v : C} {c' w' v' cm : E} {Z z : D} {Z' z' Zm : F}
    (a : c ≅ w) (a' : c' ≅ w') (u : w ≅ v) (u' : w' ≅ v')
    (δ : z ≅ A.obj v) (δ' : z' ≅ B.obj v')
    (e : Z ≅ A.obj c) (e' : Z' ≅ B.obj c') (em : Zm ≅ B.obj cm)
    (b : S.obj c ≅ cm) (l : c' ≅ cm) (r : S.obj w ≅ w')
    (cw : R.obj (A.obj w) ≅ B.obj (S.obj w))
    (cc : R.obj (A.obj c) ≅ B.obj (S.obj c))
    (hn : R.map (A.map a.inv) ≫ cc.hom = cw.hom ≫ B.map (S.map a.inv))
    (ho : S.mapIso a ≪≫ r = (b ≪≫ l.symm) ≪≫ a') :
    R.map (e ≪≫ A.mapIso (a ≪≫ u) ≪≫ δ.symm).inv ≫
        ((R.mapIso e ≪≫ cc ≪≫ B.mapIso b ≪≫ em.symm) ≪≫
          (e' ≪≫ B.mapIso l ≪≫ em.symm).symm).hom =
      (R.mapIso (δ ≪≫ (A.mapIso u).symm) ≪≫ cw ≪≫ B.mapIso r ≪≫
        B.mapIso u' ≪≫ δ'.symm).hom ≫
        (e' ≪≫ B.mapIso (a' ≪≫ u') ≪≫ δ'.symm).inv := by
  have hinv : S.map a.inv ≫ (b ≪≫ l.symm).hom = r.hom ≫ a'.inv := by
    have hi := congrArg (fun q ↦ (S.mapIso a).symm ≪≫ q ≪≫ a'.symm) ho
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
      Iso.trans_refl, Iso.trans_hom, Iso.symm_hom,
      CategoryTheory.Functor.mapIso_inv] using congrArg Iso.hom hi.symm
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
    Iso.inv_hom_id_assoc, Iso.map_hom_inv_id_assoc]
  rw [reassoc_of% hn]
  have hh := congrArg (fun q ↦ B.map q) hinv
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp] at hh
  rw [reassoc_of% hh]

attribute [local implicit_reducible] ordinaryAlpha ordinarySource ordinaryRestriction

attribute [local irreducible] diagonalComparedRestriction
  Etale.dualizingComplexBaseChangeMap Dnc.sectionBaseChange Dnc.pullComparison
  SectionRestriction.restrictionEtale

set_option maxHeartbeats 4000000 in
-- Converting the finite exceptional presentations needs a larger elaboration budget.
/-- The inverse diagonal base-change factor commutes with the actual source
comparison. Source: orientation charts Step 3; dualizing sigma-cocycle locality.
(blueprint: lem-pur-finite-diagonal-alpha-restriction).
Proof: write alpha as sourceComparison, the ordinary smooth self-product mate
pulled along the diagonal, and the two dualizing unit comparisons. Apply mate
pasting to the Cartesian sourceSquare, then apply source-etale counit locality
to ambientRestriction. The section equations identify the two pullback-composition
constraints. The ordinary source and target locality factors paste to the exact
restriction used in affineDualizingRestriction. Naturality of the site comparison
moves the ordinary square to the pro-etale category; cancel the common unit
comparison and sourceComparison factors. Taking inverse alpha gives this equation.
This argument uses no DNC or vector orientation and includes empty opens and d=0. -/
theorem alpha_square :
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine V.1.toScheme := V.2
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.1.ι).leftDerivedFunctor.map
        (P.chartDiagonalAlpha d f aY).inv ≫
      (sourceRestriction d f U V hUV P aY).hom =
    (affineDualizingRestriction P f aY U V hUV).hom ≫
      (P.chartDiagonalAlpha d (f.resLE V.1 U.1 hUV) (V.1.ι ≫ aY)).inv := by
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  let h := f.resLE V.1 U.1 hUV
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  let := Dnc.compactifiable P h (V.1.ι ≫ aY)
  let A := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let B := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U.1.toScheme).mapDerivedCategory
  let R := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    U.1.ι).leftDerivedFunctor
  let S := pull P U.1.ι
  let a := ordinaryAlpha d f P aY
  let a' := ordinaryAlpha d h P (V.1.ι ≫ aY)
  let aU := h ≫ V.1.ι ≫ aY
  let := SmoothOfRelativeDimension.smooth d (diagonalPair d f).g
  let := SmoothOfRelativeDimension.smooth d (mixedPair d f U).g
  let := Dnc.compactifiable P (diagonalPair d f).g (f ≫ aY)
  let := Dnc.compactifiable P (mixedPair d f U).g aU
  let := Dnc.invertibleExponent P ((diagonalPair d f).g ≫ f ≫ aY)
  have hn := congrArg Iso.hom (Dnc.pullComparison_naturality P U.1.ι a.symm)
  change R.map (A.map a.inv) ≫
      (Dnc.pullComparison P U.1.ι
        (Etale.sectionInvariant P.Coefficient (pullback.fst f f)
          (pullback.diagonal f))).hom =
    (Dnc.pullComparison P U.1.ι (Etale.dualizingComplex P.Coefficient f)).hom ≫
      B.map (S.map a.inv) at hn
  dsimp only [chartDiagonalAlpha, sourceRestriction, affineDualizingRestriction,
    SectionRestriction.baseComparison, SectionRestriction.restriction]
  exact transport_alpha A B R S a a' (P.chartDualizingUnit f)
    (P.chartDualizingUnit h) (P.diagonalDualizingComparison f)
    (P.diagonalDualizingComparison h)
    (Dnc.sourceComparison P d (pullback.fst f f) (f ≫ aY) (pullback.diagonal f))
    (Dnc.sourceComparison P d (pullback.fst h h) aU (pullback.diagonal h))
    (Dnc.sourceComparison P d (mixedPair d f U).g aU (mixedPair d f U).s)
    (Dnc.sectionBaseChange P.Coefficient d (diagonalPair d f).g
      (sourceSquare d f U).square (diagonalPair d f).s (mixedPair d f U).s
      (sourceSquare d f U).section_eq)
    (SectionRestriction.restrictionEtale P aU (ambientRestriction d f U V hUV))
    (ordinaryRestriction f U V hUV P aY)
    (Dnc.pullComparison P U.1.ι (Etale.dualizingComplex P.Coefficient f))
    (Dnc.pullComparison P U.1.ι
      (Etale.sectionInvariant P.Coefficient (pullback.fst f f) (pullback.diagonal f)))
    hn (ordinary_square d f U V hUV P aY)

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
