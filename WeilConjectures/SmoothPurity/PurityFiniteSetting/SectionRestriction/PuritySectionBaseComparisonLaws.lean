/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.SmoothSectionExchangeComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # Base comparison and restriction laws

Source: blueprint latest, sec-smooth-purity, orientation charts Step 3 and
composition coherence Step 1 (blueprint: lem-pur-section-base-comparison-laws).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

private theorem baseComparison_comp (P : PurityFiniteSetting.{u})
    {B B₁ B₂ : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₁ : B₁ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₁] [QuasiCompact aB₁]
    (aB₂ : B₂ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₂] [QuasiCompact aB₂]
    {b₁ : B₁ ⟶ B} {b₂ : B₂ ⟶ B₁} {d : ℕ}
    {X : Pair B d} {X₁ : Pair B₁ d} {X₂ : Pair B₂ d}
    (sq₁ : BaseChange b₁ X₁ X) (sq₂ : BaseChange b₂ X₂ X₁) :
    baseComparison P aB aB₂ (sq₂.comp sq₁) =
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        b₂ b₁).app (invariant P aB X) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b₂).leftDerivedFunctor.mapIso
        (baseComparison P aB aB₁ sq₁) ≪≫ baseComparison P aB₁ aB₂ sq₂ := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X₁.g
  let := SmoothOfRelativeDimension.smooth d X₂.g
  let := P.noetherian aB
  let := P.noetherian aB₁
  let := P.noetherian aB₂
  let := P.noetherian (X.g ≫ aB)
  let := P.noetherian (X₁.g ≫ aB₁)
  let := P.noetherian (X₂.g ≫ aB₂)
  let := Dnc.compactifiable P X.g aB
  let := Dnc.compactifiable P X₁.g aB₁
  let := Dnc.compactifiable P X₂.g aB₂
  let := Dnc.invertibleExponent P (X.g ≫ aB)
  let := Dnc.invertibleExponent P (X₁.g ≫ aB₁)
  have he := Dnc.section_baseChange_comp P.Coefficient d X.g X₁.g X₂.g
    sq₁.square sq₂.square X.s X₁.s X₂.s sq₁.section_eq sq₂.section_eq
  have hp := Dnc.pullComparison_comp P b₂ b₁ (sectionEtale P aB X)
  have hn := Dnc.pullComparison_naturality P b₂
    (Dnc.sectionBaseChange P.Coefficient d X.g sq₁.square X.s X₁.s sq₁.section_eq)
  have hc := (ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) b₂ b₁).hom.naturality
      (Dnc.sourceComparison P d X.g aB X.s).hom
  have hnh := congrArg Iso.hom hn
  apply Iso.ext
  dsimp only [baseComparison, BaseChange.comp, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [he]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc] at hnh ⊢
  simp only [invariant, sectionEtale, Dnc.sourceEtale, Functor.comp_map] at hp hc hnh ⊢
  simp only [Iso.map_inv_hom_id_assoc]
  erw [reassoc_of% hp, reassoc_of% hc, ← reassoc_of% hnh]

private theorem baseComparison_congr (P : PurityFiniteSetting.{u})
    {B B' : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {d : ℕ} {X : Pair B d} {X' : Pair B' d} {b b' : B' ⟶ B}
    (sq : BaseChange b X' X) (sq' : BaseChange b' X' X)
    (hb : b = b') (ha : sq.map = sq'.map) :
    baseComparison P aB aB' sq =
      (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hb).app
        (invariant P aB X) ≪≫ baseComparison P aB aB' sq' := by
  subst b'
  cases sq with
  | mk a h hs =>
    cases sq' with
    | mk a' h' hs' =>
      dsimp only at ha
      subst a'
      apply Iso.ext
      simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Iso.app_hom,
        Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private theorem baseComparison_id (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ} (X : Pair B d) :
    baseComparison P aB aB (BaseChange.id X) =
      (ProEtale.leftDerivedUpperStarId
        (ModuleCat.{u + 1} P.Coefficient) B).app (invariant P aB X) := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := invariant P aB X
  let e := baseComparison P aB aB (BaseChange.id X)
  have hp := baseComparison_comp P aB aB aB (BaseChange.id X) (BaseChange.id X)
  have hg := baseComparison_congr P aB aB
    ((BaseChange.id X).comp (BaseChange.id X)) (BaseChange.id X)
    (Category.id_comp (𝟙 B)) (Category.id_comp (𝟙 X.V))
  have hn := (ProEtale.leftDerivedUpperStarId C B).hom.naturality e.hom
  have hu := ProEtale.leftDerivedUpperStarComp_id_left_app (A := C) (𝟙 B) K
  have hh := congrArg Iso.hom (hg.symm.trans hp)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hh
  rw [← hu] at hh
  have he : (ProEtale.leftDerivedUpperStarId C B).hom.app
      ((ProEtale.upperStar C (𝟙 B)).leftDerivedFunctor.obj K) =
      (ProEtale.upperStar C (𝟙 B)).leftDerivedFunctor.map e.hom := by
    exact (cancel_mono e.hom).mp ((cancel_epi
      ((ProEtale.leftDerivedUpperStarComp C (𝟙 B) (𝟙 B)).hom.app K)).mp
        (by simpa only [Category.assoc] using hh))
  apply Iso.ext
  apply (cancel_epi ((ProEtale.leftDerivedUpperStarId C B).hom.app
    ((ProEtale.upperStar C (𝟙 B)).leftDerivedFunctor.obj K))).mp
  simp only [Functor.id_map] at hn
  rw [← he] at hn
  dsimp only [C, K, e] at hn
  exact hn.symm

private theorem sourceEtale_locality (P : PurityFiniteSetting.{u})
    {U V B : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    (a : U ⟶ V) [a.IsOver (Spec (.of P.field.k))]
    [Etale a] [IsSeparated a] [QuasiCompact a]
    (f : V ⟶ B) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    letI := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P U
    letI := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P V
    letI := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P B
    letI := ProEtale.FiniteEtaleNormalization.compactification P f
    letI := ProEtale.FiniteEtaleNormalization.compactification P (a ≫ f)
    ProEtale.FiniteEtaleNormalization.sourceEtale P a f =
      (Etale.sectionStructuralLocalityIso P.Coefficient a f (a ≫ f) rfl).symm := by
  let := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P U
  let := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P V
  let := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P B
  let := ProEtale.FiniteEtaleNormalization.compactification P a
  let := ProEtale.FiniteEtaleNormalization.compactification P f
  let := ProEtale.FiniteEtaleNormalization.compactification P (a ≫ f)
  let C := ModuleCat.{u + 1} P.Coefficient
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  let adjA := Etale.derivedEtaleLowerShriekUpperStarAdjunction C a inferInstance
  let adjF := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
  let adjG := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (a ≫ f)
  let H := Etale.existsUnique_etaleAmbientAdjointLocalityIso P.Coefficient a f
    (HasCompactification.compactification f) (HasCompactification.compactification (a ≫ f))
    (Etale.rightDerivedUpperShriek P.Coefficient f)
    (Etale.rightDerivedUpperShriek P.Coefficient (a ≫ f)) adjF adjG
  let α := Etale.etaleAmbientLeftComparison P.Coefficient N a f
    (HasCompactification.compactification f) (HasCompactification.compactification (a ≫ f))
  let τ := conjugateIsoEquiv (adjA.comp adjF) adjG α.symm
  have hτ : Classical.choose H = τ := by
    apply ((Classical.choose_spec H).2 τ ?_).symm
    intro N' K
    have hα : Etale.etaleAmbientLeftComparison P.Coefficient N' a f
        (HasCompactification.compactification f)
        (HasCompactification.compactification (a ≫ f)) = α := by
      unfold Etale.etaleAmbientLeftComparison α
      rw [Etale.normalization_comparison_eq P.Coefficient N' N]
      rfl
    rw [hα]
    exact (conjugateEquiv_counit (adjA.comp adjF) adjG α.inv K).trans
      (by
        simp only [Adjunction.comp_counit_app]
        rfl)
  have hα : α = Functor.isoWhiskerRight
      (Etale.etaleCanonicalCompactSupportComparison P.Coefficient a N).symm
      (Etale.rightDerivedLowerShriek C f) ≪≫
        Etale.unboundedEtaleLowerShriekCompIso P.Coefficient a f := by
    apply Iso.ext
    ext K
    have ht := Etale.chart_comparison_formula P.Coefficient N a f
      (HasCompactification.compactification a) (HasCompactification.compactification f)
      (HasCompactification.compactification (a ≫ f)) K
    rw [Etale.chart_comparison_ambient] at ht
    have hi := (Etale.unboundedEtaleCompactSupport_comparison_coherence
      P.Coefficient f).1 (HasCompactification.compactification f)
    have hg := (Etale.unboundedEtaleCompactSupport_comparison_coherence
      P.Coefficient (a ≫ f)).1 (HasCompactification.compactification (a ≫ f))
    have ha := (Etale.unboundedEtaleCompactSupport_comparison_coherence
      P.Coefficient a).1 (HasCompactification.compactification a)
    simp only [Etale.rightDerivedLowerShriekIso, hi, hg,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] at ht
    erw [Category.comp_id] at ht
    dsimp only [α, C]
    simpa only [Etale.etaleCanonicalCompactSupportComparison,
      Etale.rightDerivedLowerShriekIso, hi, hg, ha, Iso.refl_hom, Iso.refl_inv,
      Iso.trans_inv, Iso.symm_inv, Iso.app_inv, NatTrans.id_app,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, NatTrans.comp_app, Category.id_comp, Category.comp_id] using ht
  have hr := ProEtale.FiniteEtaleNormalization.rho_canonical (P := P) (e := a)
  apply Iso.ext
  simp only [Etale.sectionStructuralLocalityIso, hτ, Iso.symm_hom,
    Iso.trans_inv, Iso.app_inv]
  have ht : τ.inv =
      (ProEtale.FiniteEtaleNormalization.comp P a f).hom ≫
        Functor.whiskerLeft (Etale.rightDerivedUpperShriek P.Coefficient f)
          (ProEtale.FiniteEtaleNormalization.rho P a ≪≫
            Etale.leftDerivedUpperStarIsoMapDerivedCategory C a).hom := by
    change conjugateEquiv adjG (adjA.comp adjF) α.hom = _
    rw [hα]
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    rw [← conjugateEquiv_comp _
      ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient a).comp adjF)]
    rw [conjugateEquiv_whiskerRight]
    have hrh := congrArg Iso.hom hr
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom, Iso.trans_hom] at hrh
    erw [hrh]
    rfl
  rw [ht]
  simp only [ProEtale.FiniteEtaleNormalization.sourceEtale, Iso.trans_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  dsimp only [C, ProEtale.FiniteEtaleNormalization.coefficientUnit,
    ProEtale.FiniteEtaleNormalization.omega, Etale.dualizingComplex]
  erw [Iso.hom_inv_id_app, Category.comp_id]

private theorem sourceEtale_locality_congr (P : PurityFiniteSetting.{u})
    {U V B : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    (a : U ⟶ V) [a.IsOver (Spec (.of P.field.k))]
    [Etale a] [IsSeparated a] [QuasiCompact a]
    (f : V ⟶ B) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f' : U ⟶ B) [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f'] (hf : a ≫ f = f') :
    letI := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P U
    letI := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P V
    letI := ProEtale.FiniteEtaleNormalization.fieldSchemeNoetherian P B
    letI := ProEtale.FiniteEtaleNormalization.compactification P f
    letI := ProEtale.FiniteEtaleNormalization.compactification P f'
    (ProEtale.FiniteEtaleNormalization.congr P f' (a ≫ f) hf.symm).app (𝟙_ _) ≪≫
        ProEtale.FiniteEtaleNormalization.sourceEtale P a f =
      (Etale.sectionStructuralLocalityIso P.Coefficient a f f' hf).symm := by
  subst f'
  have hc : ProEtale.FiniteEtaleNormalization.congr P (a ≫ f) (a ≫ f) rfl =
      Iso.refl _ := by
    apply Iso.ext
    simp only [ProEtale.FiniteEtaleNormalization.congr,
      Etale.unboundedEtaleLowerShriekCongr, conjugateIsoEquiv_apply_hom,
      Iso.refl_hom, conjugateEquiv_id]
  rw [hc]
  change Iso.refl _ ≪≫ _ = _
  rw [Iso.refl_trans]
  exact sourceEtale_locality P a f

private noncomputable def localityRestriction (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {X' X : Pair B d} (a : EtaleMap X' X) :
    sectionEtale P aB X ≅ sectionEtale P aB X' :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := SmoothOfRelativeDimension.smooth d X'.g
  letI := P.noetherian aB
  letI := P.noetherian (X.g ≫ aB)
  letI := P.noetherian (X'.g ≫ aB)
  letI := Dnc.compactifiable P X.g aB
  letI := Dnc.compactifiable P X'.g aB
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      X'.s a.map X.s a.section_eq.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) X'.s).leftDerivedFunctor.mapIso
      (Etale.sectionStructuralLocalityIso P.Coefficient a.map X.g X'.g a.over_eq)

private theorem restrictionEtale_locality (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {X' X : Pair B d} (a : EtaleMap X' X) :
    restrictionEtale P aB a = (localityRestriction P aB a).symm := by
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
  have he := sourceEtale_locality_congr P a.map X.g X'.g a.over_eq
  dsimp only [restrictionEtale, localityRestriction]
  rw [he]
  simp only [Iso.trans_symm, Functor.mapIso_symm]

private noncomputable def sectionBaseComparison (P : PurityFiniteSetting.{u})
    {B B₀ : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    {b : B₀ ⟶ B} {d : ℕ} {X : Pair B d} {X₀ : Pair B₀ d}
    (sq : BaseChange b X₀ X) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj
      (sectionEtale P aB X) ≅ sectionEtale P aB₀ X₀ :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := SmoothOfRelativeDimension.smooth d X₀.g
  letI := Dnc.compactifiable P X.g aB
  letI := Dnc.compactifiable P X₀.g aB₀
  letI := Dnc.invertibleExponent P (X.g ≫ aB)
  Dnc.sectionBaseChange P.Coefficient d X.g sq.square X.s X₀.s sq.section_eq

private theorem locality_baseComparison (P : PurityFiniteSetting.{u})
    {B B₀ : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    {b : B₀ ⟶ B} {d : ℕ} {X' X : Pair B d} {X₀' X₀ : Pair B₀ d}
    (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
    (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
    (ha : a₀.map ≫ sq.map = sq'.map ≫ a.map) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (localityRestriction P aB a) ≪≫ sectionBaseComparison P aB aB₀ sq' =
      sectionBaseComparison P aB aB₀ sq ≪≫ localityRestriction P aB₀ a₀ := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let := SmoothOfRelativeDimension.smooth d X₀.g
  let := SmoothOfRelativeDimension.smooth d X₀'.g
  let := P.noetherian aB
  let := P.noetherian aB₀
  let := P.noetherian (X.g ≫ aB)
  let := P.noetherian (X'.g ≫ aB)
  let := P.noetherian (X₀.g ≫ aB₀)
  let := P.noetherian (X₀'.g ≫ aB₀)
  let := Dnc.compactifiable P X.g aB
  let := Dnc.compactifiable P X'.g aB
  let := Dnc.compactifiable P X₀.g aB₀
  let := Dnc.compactifiable P X₀'.g aB₀
  let := Dnc.invertibleExponent P (X.g ≫ aB)
  let := Dnc.invertibleExponent P (X'.g ≫ aB)
  have squ : IsPullback sq'.map a₀.map a.map sq.map := by
    have ho := sq'.square
    rw [← a.over_eq, ← a₀.over_eq] at ho
    exact ho.of_bot ha.symm sq.square
  have hd := Etale.structural_locality_baseChange P.Coefficient a.map X.g
    a₀.map X₀.g X'.g a.over_eq X₀'.g a₀.over_eq
    b sq.map sq'.map sq.square squ sq'.square
  have hc := Etale.section_pullback_locality_comp P.Coefficient b
    X.s X₀.s X'.s X₀'.s a.map a₀.map sq.map sq'.map
    sq.section_eq.symm sq'.section_eq.symm a.section_eq a₀.section_eq squ.w
    (Etale.dualizingComplex P.Coefficient X.g)
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      b X'.s).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      X₀'.s sq'.map (b ≫ X'.s) sq'.section_eq.symm).hom.naturality
    (Etale.sectionStructuralLocalityIso P.Coefficient a.map X.g X'.g a.over_eq).hom
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hn
  unfold Etale.sectionCoherencePullbackIso at hd hc
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc] at hd hc
  apply Iso.ext
  dsimp only [localityRestriction, sectionBaseComparison, Dnc.sectionBaseChange]
  simp only [sectionEtale, Dnc.sourceEtale, Etale.sectionInvariant,
    Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← CategoryTheory.Functor.map_comp, ← hd]
  simp only [Functor.map_comp]
  erw [reassoc_of% hc]
  have hn' := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    X₀'.s a₀.map X₀.s a₀.section_eq.symm).hom.naturality
    (Etale.dualizingComplexBaseChangeMap P.Coefficient sq.square)
  simp only [Functor.comp_map] at hn'
  erw [← reassoc_of% hn']

private theorem restrictionEtale_baseComparison (P : PurityFiniteSetting.{u})
    {B B₀ : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    {b : B₀ ⟶ B} {d : ℕ} {X' X : Pair B d} {X₀' X₀ : Pair B₀ d}
    (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
    (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
    (ha : a₀.map ≫ sq.map = sq'.map ≫ a.map) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (restrictionEtale P aB a) ≪≫ sectionBaseComparison P aB aB₀ sq =
      sectionBaseComparison P aB aB₀ sq' ≪≫ restrictionEtale P aB₀ a₀ := by
  have he := congrArg Iso.hom (locality_baseComparison P aB aB₀ a a₀ sq sq' ha)
  rw [restrictionEtale_locality, restrictionEtale_locality]
  apply Iso.ext
  apply (cancel_epi
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
      (localityRestriction P aB a)).hom).mp
  apply (cancel_mono (localityRestriction P aB₀ a₀).hom).mp
  simpa only [Iso.trans_hom, Functor.mapIso_symm, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using he.symm

private theorem restriction_baseComparison (P : PurityFiniteSetting.{u})
    {B B₀ : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    {b : B₀ ⟶ B} {d : ℕ} {X' X : Pair B d} {X₀' X₀ : Pair B₀ d}
    (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
    (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
    (ha : a₀.map ≫ sq.map = sq'.map ≫ a.map) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (restriction P aB a) ≪≫ baseComparison P aB aB₀ sq =
      baseComparison P aB aB₀ sq' ≪≫ restriction P aB₀ a₀ := by
  have he := restrictionEtale_baseComparison P aB aB₀ a a₀ sq sq' ha
  have hn := congrArg Iso.hom
    (Dnc.pullComparison_naturality P b (restrictionEtale P aB a))
  apply Iso.ext
  dsimp only [restriction, baseComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at hn ⊢
  simp only [invariant, sectionEtale, Dnc.sourceEtale] at hn ⊢
  simp only [Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  erw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc]
  have heh := congrArg Iso.hom he
  simp only [Iso.trans_hom, Functor.mapIso_hom, sectionBaseComparison] at heh
  erw [heh]
  simp only [Functor.map_comp, Category.assoc]

/-- The smooth section base-comparison map respects base pasting and ordinary restriction.
Source: blueprint latest, composition coherence Step 1, smooth tensor/exceptional pasting
(blueprint: lem-pur-section-base-comparison-laws).
Proof: section exceptional base-change pasting and the natural comparison with nu*
give composition. Apply composition to two identity squares, use pullback unit coherence,
and cancel the invertible comparison to obtain the identity law. For restriction, identify
E = rho c with the inverse of the counit-normalized structural locality isomorphism:
the chart comparison formula identifies their compact-support mates, and uniqueness of
adjoint locality identifies their right adjoints. Structural locality base change and
section pullback coherence then give the ordinary-etale restriction square. Invert the
locality maps and transport through the natural nu* comparison, cancelling source
comparison isomorphisms. No flatness of b is used; the argument includes empty schemes
and relative dimension zero. -/
theorem section_base_comparison_laws (P : PurityFiniteSetting.{u}) :
    BasePasting P ∧
    ∀ (B B₀ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
      [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
      (aB₀ : B₀ ⟶ Spec (.of P.field.k))
      [IsSeparated aB₀] [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
      (b : B₀ ⟶ B) (_hb : b ≫ aB = aB₀) (d : ℕ)
      (X' X : Pair B d) (X₀' X₀ : Pair B₀ d)
      (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
      (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
      (_ha : a₀.map ≫ sq.map = sq'.map ≫ a.map),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
          (restriction P aB a) ≪≫ baseComparison P aB aB₀ sq =
        baseComparison P aB aB₀ sq' ≪≫ restriction P aB₀ a₀
    := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro B aB _ _ _ d X
    exact baseComparison_id P aB X
  · intro B B₁ B₂ aB _ _ _ aB₁ _ _ _ aB₂ _ _ _ b₁ h₁ b₂ h₂ d X X₁ X₂ sq₁ sq₂
    exact baseComparison_comp P aB aB₁ aB₂ sq₁ sq₂
  · intro B B₀ aB _ _ _ aB₀ _ _ _ b hb d X' X X₀' X₀ a a₀ sq sq' ha
    exact restriction_baseComparison P aB aB₀ a a₀ sq sq' ha

end WeilConjectures.PurityFiniteSetting.SectionRestriction
