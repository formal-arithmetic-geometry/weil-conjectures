/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionConstantTrivialization
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackCompositionMonoidal

/-! # The two counit readings of the identity-section deformation

Source: DNC geometry, standard pair in rank zero
(blueprint: lem-pur-rank-zero-family-readings).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

private theorem unit_comp (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : c = a ≫ b) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a b c h).hom.app
        (𝟙_ _) ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom ≫
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) a).hom =
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) c).hom := by
  subst c
  exact (Etale.canonicalDerivedPullbackCompositionMonoidal P.Coefficient b a
    (𝟙 X) (𝟙_ _) (𝟙_ _)).2.1

namespace ZeroCalculation
open ProEtale.FiniteEtaleNormalization
variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]

private def sectionUnit (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f] (s : Y ⟶ X) :
    (pull P s).obj (omega P f) ≅ 𝟙_ _ :=
  (pull P s).mapIso (eta P f) ≪≫
    Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) s

-- Compare the dualizing-complex and exceptional-functor presentations of the unit.
set_option maxRecDepth 2048 in
private theorem source_eta (a : X ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [Etale a]
    {Z : Scheme.{u}} [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (b : Y ⟶ Z) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] [Etale b] :
    (sourceEtale P a b).hom ≫ (pull P a).map (eta P b).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) a).hom =
      (eta P (a ≫ b)).hom := by
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := fieldSchemeNoetherian P Z
  let := compactification P a
  let := compactification P b
  let := compactification P (a ≫ b)
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := coefficientUnit C Z
  have h : (rho P (a ≫ b)).hom.app K ≫
      (Etale.leftDerivedUpperStarComp C a b).hom.app K =
    (comp P a b).hom.app K ≫
      (rho P a).hom.app ((ProEtale.FiniteEtaleNormalization.exceptional P b).obj K) ≫
      (pull P a).map ((rho P b).hom.app K) := by
    have hc := Etale.etaleSumRightAdjoint_comp P.Coefficient a b
      (ProEtale.FiniteEtaleNormalization.exceptional P a)
      (ProEtale.FiniteEtaleNormalization.exceptional P b)
      (ProEtale.FiniteEtaleNormalization.exceptional P (a ≫ b))
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient a)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient b)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (a ≫ b)) K
    rw [← rho_exact P (a ≫ b), ← rho_exact P a, ← rho_exact P b] at hc
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc
    let d := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C a).app
      ((pull P b).obj K) ≪≫ (Etale.upperStar C a).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C b).app K)
    apply (cancel_mono d.hom).1
    change _ ≫ ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C a).hom.app
      ((pull P b).obj K) ≫ (Etale.upperStar C a).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C b).hom.app K)) = _
    rw [Category.assoc, pull_comp_transport P a b K, hc]
    rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory C a).hom.naturality_assoc]
    simp only [Etale.etaleSumRightAdjointCompIso, comp, d, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, C, pull, Category.assoc]
  have h' := congrArg (fun k ↦ k ≫
    (pull P a).map (Etale.leftDerivedUpperStarUnitIso C b).hom ≫
      (Etale.leftDerivedUpperStarUnitIso C a).hom) h
  have hu := unit_comp P a b (a ≫ b) rfl
  change (Etale.leftDerivedUpperStarComp C a b).hom.app K ≫
    (pull P a).map (Etale.leftDerivedUpperStarUnitIso C b).hom ≫
      (Etale.leftDerivedUpperStarUnitIso C a).hom =
        (Etale.leftDerivedUpperStarUnitIso C (a ≫ b)).hom at hu
  simp only [Category.assoc] at h'
  rw [hu] at h'
  change ((comp P a b).hom.app K ≫
    (rho P a).hom.app ((ProEtale.FiniteEtaleNormalization.exceptional P b).obj K)) ≫
      (pull P a).map ((rho P b).hom.app K ≫
        (Etale.leftDerivedUpperStarUnitIso C b).hom) ≫
        (Etale.leftDerivedUpperStarUnitIso C a).hom =
    (rho P (a ≫ b)).hom.app K ≫ (Etale.leftDerivedUpperStarUnitIso C (a ≫ b)).hom
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  exact h'.symm

private theorem section_unit_base
    {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (d : ℕ) (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    [SmoothOfRelativeDimension d f]
    (f' : X' ⟶ Y') [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f'] [Etale f']
    (a : X' ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : Y' ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (sq : IsPullback a f' f b) (s : Y ⟶ X) (s' : Y' ⟶ X')
    (hs : s' ≫ a = b ≫ s) :
    letI := compactification P f
    letI := compactification P f'
    letI := Dnc.invertibleExponent P (X ↘ Spec (.of P.field.k))
    Dnc.sectionBaseChange P.Coefficient d f sq s s' hs ≪≫ sectionUnit P f' s' =
      (pull P b).mapIso (sectionUnit P f s) ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b := by
  let := compactification P f
  let := compactification P f'
  let := Dnc.invertibleExponent P (X ↘ Spec (.of P.field.k))
  let C := ModuleCat.{u + 1} P.Coefficient
  let J := (Etale.leftDerivedUpperStarComp C b s).symm ≪≫
    Etale.leftDerivedUpperStarComp C s' a (b ≫ s) hs.symm
  have hb := (ProEtale.finite_etale_dualizing_normalization P f).eta_base_change
    f' b a sq
  have hu : J.hom.app (𝟙_ _) ≫
      (pull P s').map (Etale.leftDerivedUpperStarUnitIso C a).hom ≫
      (Etale.leftDerivedUpperStarUnitIso C s').hom =
    (pull P b).map (Etale.leftDerivedUpperStarUnitIso C s).hom ≫
      (Etale.leftDerivedUpperStarUnitIso C b).hom := by
    dsimp only [J, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    rw [Category.assoc, unit_comp P s' a (b ≫ s) hs.symm,
      ← unit_comp P b s (b ≫ s) rfl, Iso.inv_hom_id_app_assoc]
  have hn := J.hom.naturality (eta P f).hom
  dsimp only [J, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at hn hu
  simp only [Category.assoc] at hn hu
  apply Iso.ext
  dsimp only [Dnc.sectionBaseChange, sectionUnit, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  change (Etale.leftDerivedUpperStarComp C b s).inv.app _ ≫
    (Etale.leftDerivedUpperStarComp C s' a (b ≫ s) hs.symm).hom.app _ ≫
      (pull P s').map (beta P f f' b a sq ≫ (eta P f').hom) ≫ _ = _
  rw [hb]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  erw [hu]

private theorem source_eta_congr
    {Z : Scheme.{u}} [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [Etale a]
    (b : Y ⟶ Z) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] [Etale b]
    (c : X ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c] [Etale c]
    (h : c = a ≫ b) :
    ((ProEtale.FiniteEtaleNormalization.congr P c (a ≫ b) h).app (𝟙_ _) ≪≫ sourceEtale P a b).hom ≫
      (pull P a).map (eta P b).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) a).hom =
      (eta P c).hom := by
  subst c
  have hc : ProEtale.FiniteEtaleNormalization.congr P (a ≫ b) (a ≫ b) rfl = Iso.refl _ := by
    apply Iso.ext
    simp only [ProEtale.FiniteEtaleNormalization.congr, Etale.unboundedEtaleLowerShriekCongr,
      conjugateIsoEquiv_apply_hom, Iso.refl_hom, conjugateEquiv_id]
  rw [hc]
  change (Iso.refl _ ≪≫ sourceEtale P a b).hom ≫
    (pull P a).map (eta P b).hom ≫
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) a).hom = _
  rw [Iso.refl_trans]
  exact source_eta P a b

private theorem section_unit_restriction
    {X' : Scheme.{u}} [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    (f' : X' ⟶ Y) [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f'] [Etale f']
    (a : X' ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [Etale a]
    (hf : a ≫ f = f') (s : Y ⟶ X) (s' : Y ⟶ X') (hs : s' ≫ a = s) :
    let E := (ProEtale.FiniteEtaleNormalization.congr P f' (a ≫ f) hf.symm).app (𝟙_ _) ≪≫
      sourceEtale P a f
    (pull P s').mapIso E ≪≫
        ((Etale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) s' a s hs.symm).app _).symm ≪≫
        sectionUnit P f s = sectionUnit P f' s' := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let S := Etale.leftDerivedUpperStarComp C s' a s hs.symm
  let E := (ProEtale.FiniteEtaleNormalization.congr P f' (a ≫ f) hf.symm).app (𝟙_ _) ≪≫
    sourceEtale P a f
  have he := source_eta_congr P a f f' hf.symm
  have hu : S.inv.app (𝟙_ _) ≫ (Etale.leftDerivedUpperStarUnitIso C s).hom =
      (pull P s').map (Etale.leftDerivedUpperStarUnitIso C a).hom ≫
        (Etale.leftDerivedUpperStarUnitIso C s').hom := by
    rw [← unit_comp P s' a s hs.symm]
    change S.inv.app _ ≫ S.hom.app _ ≫ _ = _
    rw [Iso.inv_hom_id_app_assoc]
  have hn := S.inv.naturality (eta P f).hom
  apply Iso.ext
  dsimp only [sectionUnit, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom]
  change (pull P s').map E.hom ≫ S.inv.app _ ≫ (pull P s).map (eta P f).hom ≫ _ = _
  erw [← reassoc_of% hn]
  erw [hu]
  have he' : (E.hom ≫ (pull P a).map (eta P f).hom) ≫
      (Etale.leftDerivedUpperStarUnitIso C a).hom = (eta P f').hom := by
    simpa only [E, Category.assoc] using he
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, he']

end ZeroCalculation
private theorem iso_comparison_restriction (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ}
    {X' X : Pair B d} [Etale X.g] [Etale X'.g] (a : EtaleMap X' X)
    (sq : BaseChange (𝟙 B) X' X) (ha : sq.map = a.map) :
    baseComparison P aB aB sq ≪≫ restriction P aB a =
      baseComparison P aB aB (BaseChange.id X) := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  let : X.V.Over (Spec (.of P.field.k)) := ⟨X.g ≫ aB⟩
  let : X'.V.Over (Spec (.of P.field.k)) := ⟨X'.g ≫ aB⟩
  let : X.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : X'.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : a.map.IsOver (Spec (.of P.field.k)) := ⟨by
    change a.map ≫ (X.g ≫ aB) = X'.g ≫ aB
    rw [← Category.assoc, a.over_eq]⟩
  let : LocallyOfFiniteType (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.g ≫ aB))
  let : QuasiCompact (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X.g ≫ aB))
  let : LocallyOfFiniteType (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X'.g ≫ aB))
  let : QuasiCompact (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X'.g ≫ aB))
  let := Dnc.compactifiable P X.g aB
  let := Dnc.compactifiable P X'.g aB
  let := Dnc.invertibleExponent P (X.g ≫ aB)
  let C := ModuleCat.{u + 1} P.Coefficient
  let sq' : IsPullback a.map X'.g X.g (𝟙 B) := ha ▸ sq.square
  have hs : X'.s ≫ a.map = (𝟙 B) ≫ X.s := by simpa using a.section_eq
  have hb := ZeroCalculation.section_unit_base P d X.g X'.g a.map (𝟙 B)
    sq' X.s X'.s hs
  have hi := ZeroCalculation.section_unit_base P d X.g X.g (𝟙 X.V) (𝟙 B)
    (BaseChange.id X).square X.s X.s (BaseChange.id X).section_eq
  have hr := ZeroCalculation.section_unit_restriction P X.g X'.g a.map
    a.over_eq X.s X'.s a.section_eq
  dsimp only at hr
  rw [← Iso.trans_assoc] at hr
  change restrictionEtale P aB a ≪≫ ZeroCalculation.sectionUnit P X.g X.s =
    ZeroCalculation.sectionUnit P X'.g X'.s at hr
  have he : sectionBaseComparison P aB aB sq ≪≫ restrictionEtale P aB a =
      sectionBaseComparison P aB aB (BaseChange.id X) := by
    apply Iso.ext
    apply (cancel_mono (ZeroCalculation.sectionUnit P X.g X.s).hom).mp
    have hb' := congrArg Iso.hom hb
    have hi' := congrArg Iso.hom hi
    have hr' := congrArg Iso.hom hr
    simp only [Iso.trans_hom] at hb' hi' hr' ⊢
    rw [Category.assoc, hr']
    change (sectionBaseComparison P aB aB sq).hom ≫ _ = _
    have heq : sq = (⟨a.map, sq', hs⟩ : BaseChange (𝟙 B) X' X) := by
      cases sq
      cases ha
      rfl
    rw [heq]
    exact hb'.trans hi'.symm
  apply Iso.ext
  dsimp only [baseComparison, restriction, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc]
  have heh := congrArg Iso.hom he
  dsimp only [sectionBaseComparison] at heh
  simp only [Iso.trans_hom] at heh
  erw [heh]

private theorem reading_from_pasting (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ}
    (X : Pair B d) (Y : Pair (AffineSpace (ULift.{u} (Fin 1)) B) d)
    (Z : Pair B d) (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    (sq : BaseChange (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) Y X)
    (sqi : BaseChange i Z Y) (collapse : BaseChange (𝟙 B) Z X)
    (hm : sqi.map ≫ sq.map = collapse.map)
    (r : invariant P aB Z ≅ invariant P aB X)
    (hr : baseComparison P aB aB collapse ≪≫ r =
      baseComparison P aB aB (BaseChange.id X)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.mapIso
        (baseComparison P aB ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) sq).symm ≪≫
      (lineCounit P B i hi).app (invariant P aB X) =
    baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) aB sqi ≪≫ r := by
  let aL := (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB
  let C := ModuleCat.{u + 1} P.Coefficient
  let E := (ProEtale.upperStar C i).leftDerivedFunctor
  let e := baseComparison P aB aL sq
  let D := (ProEtale.leftDerivedUpperStarComp C i
    (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).app (invariant P aB X)
  have h := baseComparison_congr P aB aB (sqi.comp sq) collapse hi hm
  rw [baseComparison_comp P aB aL aB sq sqi] at h
  have hh := congrArg (fun z ↦ (E.mapIso e).symm ≪≫ D.symm ≪≫ z ≪≫ r) h
  simp only [D, E, e, aL, C, Iso.trans_assoc,
    Iso.symm_self_id_assoc] at hh
  have hc := hr.trans (baseComparison_id P aB X)
  rw [hc] at hh
  symm
  apply Iso.ext
  have hhh := congrArg Iso.hom hh
  simpa only [lineCounit, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_symm, Functor.mapIso_hom, Functor.mapIso_inv,
    NatTrans.comp_app, Category.assoc, D, E, e, aL, C] using hhh

private noncomputable def familyCollapse {B : Scheme.{u}} (P : PurityFiniteSetting.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    BaseChange (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)
      (familyPair (standardZero B)) (standardZero B) := by
  let Y := familyPair (standardZero B)
  letI : IsIso Y.g := (standardZeroGeometry P aB).2
  letI : IsIso (standardZero B).g := by change IsIso (𝟙 B); infer_instance
  refine ⟨Y.g ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B), ?_, ?_⟩
  · apply IsPullback.of_vert_isIso
    constructor
    change (Y.g ≫ _) ≫ 𝟙 B = Y.g ≫ _
    rw [Category.comp_id]
  · change Y.s ≫ (Y.g ≫ _) = _ ≫ 𝟙 B
    rw [← Category.assoc, Y.section_eq, Category.id_comp, Category.comp_id]

private noncomputable def normalCollapse {B : Scheme.{u}} (P : PurityFiniteSetting.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    BaseChange (𝟙 B) (normalPair P aB (standardZero B)) (standardZero B) := by
  let Z := normalPair P aB (standardZero B)
  letI : IsIso Z.g := (standardZeroGeometry P aB).1
  letI : IsIso (standardZero B).g := by change IsIso (𝟙 B); infer_instance
  refine ⟨Z.g, ?_, ?_⟩
  · apply IsPullback.of_vert_isIso
    constructor
    change Z.g ≫ 𝟙 B = Z.g ≫ 𝟙 B
    rfl
  · change Z.s ≫ Z.g = (𝟙 B) ≫ 𝟙 B
    rw [Z.section_eq, Category.id_comp]

private noncomputable def oneSquare {B : Scheme.{u}} {d : ℕ} (X : Pair B d) :
    BaseChange (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) X (familyPair X) :=
  ⟨Scheme.Hom.deformationSpaceOneFibre X.g X.s,
    Scheme.Hom.isPullback_deformationSpaceOneFibre X.g X.s,
    Scheme.Hom.comp_deformationSpaceOneFibre X.section_eq⟩

private noncomputable def zeroSquare (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d) :
    BaseChange (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)
      (normalPair P aB X) (familyPair X) :=
  ⟨X.s.ker.normalConeToDeformationSpace,
    Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace⟩

/-- The polynomial model for the zero ideal identifies both fibre readings with
the identity-section invariant. This asserts a property of the actual geometric
endpoint maps, without using delta or its normalization.
Source: latest blueprint, sk-lem-geometry, standard-pair clause (4); sk-thm-dnc,
Local construction, polynomial model x_i = t u_i with no variables
(blueprint: lem-pur-rank-zero-family-readings).

Proof: for the identity section, its kernel ideal is zero. On every affine chart
its extended Rees algebra is R[t] and its associated graded is R in degree zero.
The canonical family and normal projections are therefore isomorphisms, as proved
by standardZeroGeometry. The augmented family pair is the pullback of the identity
pair along the line projection. Apply the counit-normalized exceptional comparison
to this square, and invert its section base-change map, to construct kappa.
The canonical one-fibre square, composed with this square, is the identity square
for the identity pair. The triangle identities for the exceptional adjunction and
the inverse-image composition constraint therefore give the first equation. The
zero-fibre square composes instead to the canonical normal collapse. Its
counit-normalized restriction is exactly restriction of standardZeroNormalMap,
so the same mate-pasting and triangle identities give the second equation.
All algebra maps fix the coefficient ring and the parameter t; hence these are
the prescribed Rees and fibre maps, rather than arbitrarily chosen isomorphisms.
The calculation includes nonreduced and empty bases. -/
theorem rank_zero_family_readings (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    ∃ κ : invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
        (familyPair (standardZero B)) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj
          (invariant P aB (standardZero B)),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
        (lineCounit P B _ (AffineSpace.oneSection_comp_over _ B)).app _ =
          endpointOne P aB (standardZero B) ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
        (lineCounit P B _ (AffineSpace.zeroSection_comp_over _ B)).app _ =
          endpointZero P aB (standardZero B) ≪≫
            restriction P aB (standardZeroNormalMap P aB)  := by
  let X := standardZero B
  let Y := familyPair X
  let Z := normalPair P aB X
  let sq := familyCollapse P aB
  let collapse := normalCollapse P aB
  let e := baseComparison P aB ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) sq
  let : Etale X.g := by change Etale (𝟙 B); infer_instance
  let : IsIso Z.g := (standardZeroGeometry P aB).1
  refine ⟨e.symm, ?_, ?_⟩
  · change _ = baseComparison P
      ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) aB (oneSquare X)
    have hm : (oneSquare X).map ≫ sq.map = (BaseChange.id X).map := by
      change (oneSquare X).map ≫ (Y.g ≫ _) = 𝟙 B
      rw [← Category.assoc, (oneSquare X).square.w]
      change ((𝟙 B) ≫ AffineSpace.oneSection (ULift.{u} (Fin 1)) B) ≫ _ = _
      rw [Category.id_comp, AffineSpace.oneSection_comp_over]
    have h := reading_from_pasting P aB X Y X _
      (AffineSpace.oneSection_comp_over _ B) sq (oneSquare X) (BaseChange.id X) hm
      (Iso.refl _) (by simp)
    simpa only [Iso.trans_refl] using h
  · change _ = baseComparison P
      ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) aB (zeroSquare P aB X) ≪≫ _
    have hm : (zeroSquare P aB X).map ≫ sq.map = collapse.map := by
      change (zeroSquare P aB X).map ≫ (Y.g ≫ _) = Z.g
      rw [← Category.assoc, (zeroSquare P aB X).square.w, Category.assoc,
        AffineSpace.zeroSection_comp_over, Category.comp_id]
    let := (standardZeroGeometry P aB).1
    have hr : baseComparison P aB aB collapse ≪≫
        restriction P aB (standardZeroNormalMap P aB) =
        baseComparison P aB aB (BaseChange.id X) :=
      iso_comparison_restriction P aB (standardZeroNormalMap P aB) collapse rfl
    exact reading_from_pasting P aB X Y Z _
      (AffineSpace.zeroSection_comp_over _ B) sq (zeroSquare P aB X) collapse hm
      (restriction P aB (standardZeroNormalMap P aB)) hr

end WeilConjectures.PurityFiniteSetting.SectionRestriction
