/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence
import WeilConjectures.EtaleCohomology.TateTwist.Normalized

/-! # Constant models for the section deformation family

Source: smooth purity, DNC Local construction and Gluing
(blueprint: lem-pur-section-constant-trivialization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

private theorem natIso_app_symm {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) : e.symm.app X = (e.app X).symm := rfl

/-- Reading a pullback from the base along a section uses the canonical composition
and identity constraints. Source: DNC normalization, restriction to a fibre
(blueprint: lem-pur-section-constant-trivialization). -/
def lineCounit (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B) :=
  (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) i
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).symm ≪≫
    ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hi ≪≫
      ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B

section ProofHelpers

-- Cache the canonical sheaf-colimit instances once; their scope ends before the
-- public theorem's statement, and they are not used by the public definition.
private theorem etale_colimits (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u + 1} P.Coefficient)] :
    HasColimitsOfShape J (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  Sheaf.instHasColimitsOfShape

private theorem proetale_colimits (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u + 1} P.Coefficient)] :
    HasColimitsOfShape J
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)) :=
  Sheaf.instHasColimitsOfShape

attribute [local instance] etale_colimits proetale_colimits

private theorem etale_model (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ} (X : Pair B d) :
    (∃ κ : Dnc.familyEtale P d X.g aB X.s X.section_eq ≅
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj
            (sectionEtale P aB X),
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso _ _ _
            (AffineSpace.oneSection_comp_over _ B)).app _ =
              Dnc.fibreOne P d X.g aB X.s X.section_eq) ∧
    Etale.DerivedCategory.isInvertible P.Coefficient
      (AffineSpace (ULift.{u} (Fin 1)) B) (Dnc.familyEtale P d X.g aB X.s X.section_eq) := by
  classical
  let := P.noetherian aB
  let := SmoothOfRelativeDimension.smooth d X.g
  let := Dnc.compactifiable P X.g aB
  let := Dnc.invertibleExponent P aB
  let := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj
    d X.g X.s X.section_eq
  have hm : ((Scheme.Hom.puncturedLine B).ι ≫ X.s.deformationSpaceSection) ≫
      Scheme.Hom.deformationSpaceProj X.g X.s = 𝟙 _ ≫ (Scheme.Hom.puncturedLine B).ι := by
    rw [Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj X.section_eq,
      Category.comp_id, Category.id_comp]
  let sq := Scheme.Hom.isPullback_deformationSpaceGeneric X.g X.s
  let D : Scheme.Hom.DeformationToNormalConeData d X.g X.s
      (Scheme.Hom.normalConeData d X.section_eq) :=
    { scheme := X.s.ker.deformationSpace
      proj := Scheme.Hom.deformationSpaceProj X.g X.s
      sect := X.s.deformationSpaceSection
      sect_comp_proj := Scheme.Hom.deformationSpaceSection_deformationSpaceProj X.section_eq
      smoothOfRelativeDimension_proj := inferInstance
      isSeparated_proj := inferInstance
      hasCompactification_proj :=
        Scheme.Hom.hasCompactification_deformationSpaceProj X.g X.s d X.section_eq
      oneFibre := Scheme.Hom.deformationSpaceOneFibre X.g X.s
      isPullback_oneFibre := Scheme.Hom.isPullback_deformationSpaceOneFibre X.g X.s
      comp_oneFibre := Scheme.Hom.comp_deformationSpaceOneFibre X.section_eq
      zeroFibre := X.s.ker.normalConeToDeformationSpace
      isPullback_zeroFibre := Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s
      comp_zeroFibre := Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace
      puncturedLine := Scheme.Hom.puncturedLine B
      coe_puncturedLine := Scheme.Hom.coe_puncturedLine B
      generic := Scheme.Hom.deformationSpaceGeneric X.g X.s
      isPullback_generic := sq
      exists_sect_generic := ⟨sq.lift _ _ hm, by
        rw [← Scheme.Hom.deformationSpaceGeneric_toBase X.g X.s, sq.lift_fst_assoc,
          Category.assoc, Scheme.Hom.deformationSpaceSection_toBase, Category.assoc],
        sq.lift_snd _ _ _, sq.lift_fst _ _ _⟩
      exists_etale_coordinates :=
        Scheme.Hom.exists_etale_coordinates_deformationSpace d X.g X.s X.section_eq }
  let : NeZero (ringChar P.Coefficient) :=
    ⟨CharP.ringChar_ne_zero_of_finite P.Coefficient⟩
  obtain ⟨κ, hκ, -⟩ := D.existsUnique_familyObject_iso P.Coefficient aB
    (Dnc.fibreOne P d X.g aB X.s X.section_eq)
  exact ⟨⟨κ, Iso.ext hκ⟩, D.isInvertible_familyObject P.Coefficient⟩

private theorem comparison_comp_explicit (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) (f : T ⟶ R) (h : f = a ≫ b)
    (K : Etale.DerivedCategoryModule P.Coefficient R) :
    Dnc.pullComparison P f K ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
            ((Etale.leftDerivedUpperStarComp _ a b f h).app K) =
      (ProEtale.leftDerivedUpperStarCongr _ h).app _ ≪≫
        (ProEtale.leftDerivedUpperStarComp _ a b).app _ ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.mapIso
          (Dnc.pullComparison P b K) ≪≫
        Dnc.pullComparison P a
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj K) := by
  subst f
  apply Iso.ext
  simpa only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Functor.mapIso_hom,
    Iso.refl_hom, Iso.app_hom, NatTrans.id_app, Category.id_comp, Category.assoc] using
      Dnc.pullComparison_comp P a b K

private theorem comparison_id (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (K : Etale.DerivedCategoryModule P.Coefficient B) :
    Dnc.pullComparison P (𝟙 B) K ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
            ((Etale.leftDerivedUpperStarId _ B).app K) =
      (ProEtale.leftDerivedUpperStarId _ B).app _ := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let ν := (ProEtale.comparisonUpperStar C B).mapDerivedCategory
  let L := (Etale.upperStar C (𝟙 B)).leftDerivedFunctor
  let M := (ProEtale.upperStar C (𝟙 B)).leftDerivedFunctor
  let pc := (ProEtale.leftDerivedUpperStarCongr C
    (Category.id_comp (𝟙 B)).symm).app (ν.obj K) ≪≫
      (ProEtale.leftDerivedUpperStarComp C (𝟙 B) (𝟙 B)).app (ν.obj K)
  have hp := congrArg Iso.hom (comparison_comp_explicit P (𝟙 B) (𝟙 B) (𝟙 B)
    (Category.id_comp (𝟙 B)).symm K)
  have he := Etale.leftDerivedUpperStarComp_id_left_hom_app C (𝟙 B) K
  have hq₀ := ProEtale.leftDerivedUpperStarComp_id_left_app (A := C) (𝟙 B) (ν.obj K)
  have hs {T S : Scheme.{u}} {f g : T ⟶ S} (h : f = g)
      (V : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) C)) :
      (ProEtale.leftDerivedUpperStarCongr C h.symm).hom.app V ≫
        (ProEtale.leftDerivedUpperStarCongr C h).hom.app V = 𝟙 _ := by
    subst g
    simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
  have hq : pc.hom ≫ (ProEtale.leftDerivedUpperStarId C B).hom.app (M.obj (ν.obj K)) =
      𝟙 _ := by
    have hh := congrArg (fun f ↦
      (ProEtale.leftDerivedUpperStarCongr C
        (Category.id_comp (𝟙 B)).symm).hom.app (ν.obj K) ≫ f) hq₀
    calc
      _ = (ProEtale.leftDerivedUpperStarCongr C
          (Category.id_comp (𝟙 B)).symm).hom.app (ν.obj K) ≫
            (ProEtale.leftDerivedUpperStarCongr C
              (Category.id_comp (𝟙 B))).hom.app (ν.obj K) := by
        simpa only [pc, M, Iso.trans_hom, Iso.app_hom, Category.assoc] using hh
      _ = _ := hs (Category.id_comp (𝟙 B)) (ν.obj K)
  have hn := (ProEtale.leftDerivedUpperStarId C B).hom.naturality
    (Dnc.pullComparison P (𝟙 B) K).hom
  have hn' := Dnc.pullComparison_naturality P (𝟙 B)
    ((Etale.leftDerivedUpperStarId C B).app K)
  have hL : Dnc.pullComparison P (𝟙 B) (L.obj K) ≪≫
      ν.mapIso ((Etale.leftDerivedUpperStarId C B).app (L.obj K)) =
        (ProEtale.leftDerivedUpperStarId C B).app (ν.obj (L.obj K)) := by
    apply Iso.ext
    apply (cancel_epi (pc.hom ≫ M.map (Dnc.pullComparison P (𝟙 B) K).hom)).mp
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    calc
      _ = (Dnc.pullComparison P (𝟙 B) K).hom ≫
          ν.map ((Etale.leftDerivedUpperStarComp C (𝟙 B) (𝟙 B) (𝟙 B)
            (Category.id_comp (𝟙 B)).symm).hom.app K) ≫
          ν.map ((Etale.leftDerivedUpperStarId C B).hom.app (L.obj K)) := by
        simpa only [pc, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
          Category.assoc, C, ν, M, L] using
          congrArg (fun f ↦ f ≫ ν.map
            ((Etale.leftDerivedUpperStarId C B).hom.app (L.obj K))) hp.symm
      _ = (Dnc.pullComparison P (𝟙 B) K).hom := by
        erw [← Functor.map_comp, he, CategoryTheory.Functor.map_id, Category.comp_id]
      _ = _ := by
        erw [hn, ← Category.assoc, hq, Category.id_comp, Functor.id_map]
  have he' : L.mapIso ((Etale.leftDerivedUpperStarId C B).app K) =
      (Etale.leftDerivedUpperStarId C B).app (L.obj K) := by
    apply Iso.ext
    apply (cancel_mono ((Etale.leftDerivedUpperStarId C B).hom.app K)).mp
    exact (Etale.leftDerivedUpperStarId C B).hom.naturality
      ((Etale.leftDerivedUpperStarId C B).hom.app K)
  have hh := congrArg (fun z ↦ z ≪≫
    ν.mapIso ((Etale.leftDerivedUpperStarId C B).app K)) hn'
  erw [he', hL] at hh
  apply Iso.ext
  have hhom := congrArg Iso.hom hh
  have hn'' := (ProEtale.leftDerivedUpperStarId C B).hom.naturality
    (ν.map ((Etale.leftDerivedUpperStarId C B).hom.app K))
  exact (cancel_epi (M.map (ν.map ((Etale.leftDerivedUpperStarId C B).hom.app K)))).mp
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.id_map,
      Functor.id_obj, C, ν, L, M, Category.assoc] using
      hhom.trans hn''.symm)

private theorem comparison_section (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    (K : Etale.DerivedCategoryModule P.Coefficient B) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.mapIso
        (Dnc.pullComparison P (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) K) ≪≫
      Dnc.pullComparison P i
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj K) ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
          ((Etale.leftDerivedUpperStarCompSectionIso _ _ _ hi).app K) =
      (lineCounit P B i hi).app _ := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let a := AffineSpace (ULift.{u} (Fin 1)) B ↘ B
  have hc := comparison_comp_explicit P i a (𝟙 B) hi.symm K
  have hh := congrArg (fun z ↦
    (ProEtale.leftDerivedUpperStarComp C i a).symm.app _ ≪≫
      (ProEtale.leftDerivedUpperStarCongr C hi.symm).symm.app _ ≪≫ z ≪≫
      (ProEtale.comparisonUpperStar C B).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarCompSectionIso C i a hi).app K)) hc
  have hid := comparison_id P B K
  simp only [C, a, Etale.leftDerivedUpperStarCompSectionIso, NatIso.trans_app,
    natIso_app_symm,
    Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.self_symm_id_assoc, Iso.symm_self_id_assoc] at hh
  rw [hid] at hh
  have hg : (ProEtale.leftDerivedUpperStarCongr C hi.symm).symm =
      ProEtale.leftDerivedUpperStarCongr C hi := by
    have hs {T S : Scheme.{u}} {f g : T ⟶ S} (h : f = g) :
        (ProEtale.leftDerivedUpperStarCongr C h.symm).symm =
          ProEtale.leftDerivedUpperStarCongr C h := by
      subst g
      rfl
    exact hs hi
  have hg' := congrArg (fun z ↦ z.app
    ((ProEtale.comparisonUpperStar C B).mapDerivedCategory.obj K)) hg
  simp only [natIso_app_symm, C] at hg'
  simpa only [C, a, lineCounit, Etale.leftDerivedUpperStarCompSectionIso,
    NatIso.trans_app, natIso_app_symm, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, hg'] using hh.symm

private theorem etale_family_plus (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ} (X : Pair B d) :
    _root_.DerivedCategory.TStructure.t.plus
      (Dnc.familyEtale P d X.g aB X.s X.section_eq) := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let g := Scheme.Hom.deformationSpaceProj X.g X.s
  let s := X.s.deformationSpaceSection
  let := P.noetherian aB
  let := SmoothOfRelativeDimension.smooth d X.g
  let := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj
    d X.g X.s X.section_eq
  let := Scheme.Hom.hasCompactification_deformationSpaceProj X.g X.s d X.section_eq
  let := P.noetherian ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
  let := SmoothOfRelativeDimension.smooth d g
  let := Dnc.compactifiable P g ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
  obtain ⟨n, hn⟩ := exceptionalBoundedBelow P.Coefficient g (𝟙_ _)
    (Dnc.etaleUnitPlus P _)
  let : (Etale.dualizingComplex P.Coefficient
    (Scheme.Hom.deformationSpaceProj X.g X.s)).IsGE n := hn
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C s).app _).symm
      ⟨n, (Etale.upperStar C s).isGE_mapDerivedCategory_obj _ n⟩

private theorem comparison_naturality (P : PurityFiniteSetting.{u})
    {T S : Scheme.{u}} (b : T ⟶ S)
    {K L : Etale.DerivedCategoryModule P.Coefficient S} (f : K ⟶ L) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory.map f) ≫
        (Dnc.pullComparison P b L).hom =
      (Dnc.pullComparison P b K).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map f) := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let η := Functor.isoWhiskerLeft (ProEtale.comparisonUpperStar C S).mapDerivedCategory
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory C b) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso C b ≪≫
      Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory C b).symm
        (ProEtale.comparisonUpperStar C T).mapDerivedCategory
  exact η.hom.naturality f

private theorem comparison_pull_plus (P : PurityFiniteSetting.{u})
    {T S : Scheme.{u}} (b : T ⟶ S)
    {K : Etale.DerivedCategoryModule P.Coefficient S}
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    _root_.DerivedCategory.TStructure.t.plus
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj K) := by
  obtain ⟨n, hn⟩ := hK
  let := hn
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ b).app K).symm
      ⟨n, (Etale.upperStar _ b).isGE_mapDerivedCategory_obj K n⟩

private theorem proetale_detection (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}}
    (F : Etale.DerivedCategoryModule P.Coefficient (AffineSpace (ULift.{u} (Fin 1)) B))
    (hF : Etale.DerivedCategory.isInvertible P.Coefficient
      (AffineSpace (ULift.{u} (Fin 1)) B) F)
    (hplus : _root_.DerivedCategory.TStructure.t.plus F)
    {Z : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B))
        (ModuleCat.{u + 1} P.Coefficient))}
    (σ : Z ≅ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B)).mapDerivedCategory.obj F)
    (C : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)))
    (α β : Z ≅ (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj C)
    (h : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso α =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso β) :
    α = β := by
  let A := AffineSpace (ULift.{u} (Fin 1)) B
  let R := ModuleCat.{u + 1} P.Coefficient
  let i := AffineSpace.oneSection (ULift.{u} (Fin 1)) B
  let π := A ↘ B
  let ν := (ProEtale.comparisonUpperStar R A).mapDerivedCategory
  let νB := (ProEtale.comparisonUpperStar R B).mapDerivedCategory
  let E := (Etale.upperStar R i).leftDerivedFunctor
  let Q := (ProEtale.upperStar R i).leftDerivedFunctor
  let γ := σ.symm ≪≫ α ≪≫ β.symm ≪≫ σ
  have hγ : Q.map γ.hom = 𝟙 _ := by
    have hh : Q.mapIso α = Q.mapIso β := h
    have hγ' : Q.mapIso γ = Iso.refl _ := by
      simp only [γ, Functor.mapIso_trans, Functor.mapIso_symm, hh,
        Iso.self_symm_id_assoc, Iso.symm_self_id]
    exact congrArg Iso.hom hγ'
  obtain ⟨f, hf⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    F F hplus).2 γ.hom
  change ν.map f = γ.hom at hf
  have hE : E.map f = 𝟙 _ := by
    apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      (E.obj F) (E.obj F) (comparison_pull_plus P i hplus)).1
    have hn := comparison_naturality P i f
    rw [hf, hγ, Category.id_comp] at hn
    change νB.map (E.map f) = νB.map (𝟙 _)
    rw [νB.map_id]
    exact (cancel_epi (Dnc.pullComparison P i F).hom).mp
      (hn.symm.trans (Category.comp_id _).symm)
  have hp : i ≫ π = 𝟙 B := AffineSpace.oneSection_comp_over _ _
  let : IsClosedImmersion (i ≫ π) := by rw [hp]; infer_instance
  let : IsClosedImmersion i := IsClosedImmersion.of_comp i π
  have hi : ∀ x : A, ∃ S : Set A,
      _root_.IsPreconnected S ∧ x ∈ S ∧ (S ∩ Set.range i.base).Nonempty := fun x ↦
    ⟨π.base ⁻¹' {π.base x}, (π.isIrreducible_preimage
      (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin 1)) B)
      isIrreducible_singleton).isPreirreducible.isPreconnected, rfl, i.base (π.base x),
      by simpa using congrArg (fun z : B ⟶ B ↦ z.base (π.base x)) hp, π.base x, rfl⟩
  have hid := Etale.eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible i hi hF f hE
  have hg : γ.hom = 𝟙 _ := by rw [← hf, hid, ν.map_id]
  apply Iso.ext
  have hh := congrArg (fun z ↦ σ.hom ≫ z ≫ σ.inv ≫ β.hom) hg
  simpa only [γ, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id] using hh

private theorem section_reading_id (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    {F : Etale.DerivedCategoryModule P.Coefficient (AffineSpace (ULift.{u} (Fin 1)) B)}
    {C C₀ : Etale.DerivedCategoryModule P.Coefficient B}
    (θ : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.obj F ≅ C)
    (κ : F ≅ (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj C₀) :
    Etale.sectionRestrictionIso _ (𝟙 B) (𝟙 (AffineSpace (ULift.{u} (Fin 1)) B))
        (by simp) hi θ
        ((Etale.leftDerivedUpperStarId _ _).app F ≪≫ κ) =
      (Etale.leftDerivedUpperStarId _ B).app C ≪≫ θ.symm ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso _ _ _ hi).app C₀ := by
  let R := ModuleCat.{u + 1} P.Coefficient
  have hl := Etale.leftDerivedUpperStarComp_id_left_hom_app R i F
  have hr := Etale.leftDerivedUpperStarComp_id_right_hom_app R i F
  have hn := (Etale.leftDerivedUpperStarId R B).hom.naturality θ.inv
  have hl' : (Etale.leftDerivedUpperStarComp R (𝟙 B) i i
      (Category.id_comp i).symm).inv.app F =
        (Etale.leftDerivedUpperStarId R B).hom.app
          ((Etale.upperStar R i).leftDerivedFunctor.obj F) := by
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp R (𝟙 B) i i
      (Category.id_comp i).symm).hom.app F)).mp
    simpa only [Iso.hom_inv_id_app] using hl.symm
  apply Iso.ext
  simp only [Etale.sectionRestrictionIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp,
    Iso.symm_inv, Category.assoc]
  erw [reassoc_of% hr]
  erw [hl', reassoc_of% hn]

private theorem section_reading_identity_map (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    (v : AffineSpace (ULift.{u} (Fin 1)) B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hv : v = 𝟙 _) (h : i ≫ v = 𝟙 B ≫ i)
    {F : Etale.DerivedCategoryModule P.Coefficient (AffineSpace (ULift.{u} (Fin 1)) B)}
    {C C₀ : Etale.DerivedCategoryModule P.Coefficient B}
    (θ : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.obj F ≅ C)
    (κ : F ≅ (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj C₀) :
    Etale.sectionRestrictionIso _ (𝟙 B) v h hi θ
      (eqToIso (congrArg (fun f ↦ (Etale.upperStar
        (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj F) hv) ≪≫
          (Etale.leftDerivedUpperStarId _ _).app F ≪≫ κ) =
      (Etale.leftDerivedUpperStarId _ B).app C ≪≫ θ.symm ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso _ _ _ hi).app C₀ := by
  subst v
  simpa only [eqToIso_refl, Iso.refl_trans] using section_reading_id P i hi θ κ

private theorem model_reading (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) = 𝟙 B)
    {F : Etale.DerivedCategoryModule P.Coefficient (AffineSpace (ULift.{u} (Fin 1)) B)}
    {S : Etale.DerivedCategoryModule P.Coefficient B}
    {Z : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B))
        (ModuleCat.{u + 1} P.Coefficient))}
    {W : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient))}
    (σ : Z ≅ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B)).mapDerivedCategory.obj F)
    (τ : W ≅ (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj S)
    (κ : F ≅ (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj S) :
    let A := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor
    let E := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor
    let ν := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B)).mapDerivedCategory
    let νB := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
    E.mapIso (σ ≪≫ ν.mapIso κ ≪≫
      (Dnc.pullComparison P (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) S).symm ≪≫
        A.mapIso τ.symm) ≪≫ (lineCounit P B i hi).app W =
      E.mapIso σ ≪≫ Dnc.pullComparison P i F ≪≫
        νB.mapIso ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.mapIso
          κ ≪≫ (Etale.leftDerivedUpperStarCompSectionIso _ _ _ hi).app S) ≪≫ τ.symm := by
  dsimp only
  have hn := (lineCounit P B i hi).hom.naturality τ.inv
  have hc := congrArg Iso.hom (comparison_section P B i hi S)
  have hk := congrArg Iso.hom (Dnc.pullComparison_naturality P i κ)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hc hk
  apply Iso.ext
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Category.assoc]
  erw [hn]
  rw [← hc]
  simp only [Category.assoc, Functor.id_map, Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% hk]

private theorem delta_etale_reading (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ} (X : Pair B d)
    (κ : Dnc.familyEtale P d X.g aB X.s X.section_eq ≅
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj (sectionEtale P aB X))
    (hκ : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
        (Etale.leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.oneSection_comp_over _ B)).app _ =
            Dnc.fibreOne P d X.g aB X.s X.section_eq) :
    delta P aB X = Dnc.sourceComparison P d X.g aB X.s ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
            (Etale.leftDerivedUpperStarCompSectionIso _ _ _
              (AffineSpace.zeroSection_comp_over _ B)).app _).symm ≪≫
          Dnc.fibreZero P d X.g aB X.s X.section_eq) ≪≫
        (Dnc.normalComparison P d X.g aB X.s X.section_eq).symm := by
  classical
  dsimp only [sectionEtale] at κ hκ ⊢
  let δ : Dnc.sourceSection P d X.g aB X.s ≅
      Dnc.normalSection P d X.g aB X.s X.section_eq :=
    Classical.choose (Dnc.existsUnique_dncInvariance P d X.g aB X.s X.section_eq)
  change δ = _
  let R := ModuleCat.{u + 1} P.Coefficient
  let A := AffineSpace (ULift.{u} (Fin 1)) B
  let F := Dnc.familyEtale P d X.g aB X.s X.section_eq
  let S := Dnc.sourceEtale P d X.g aB X.s
  let N := Dnc.normalEtale P d X.g aB X.s X.section_eq
  let ν := (ProEtale.comparisonUpperStar R B).mapDerivedCategory
  let θ₁ := Dnc.fibreOne P d X.g aB X.s X.section_eq
  let θ₀ := Dnc.fibreZero P d X.g aB X.s X.section_eq
  let r₀ := (Etale.upperStar R
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso R _ _
      (AffineSpace.zeroSection_comp_over _ B)).app S
  let ψ := r₀.symm ≪≫ θ₀
  let e := eqToIso (congrArg (fun f ↦ (Etale.upperStar R f).leftDerivedFunctor.obj F)
      (AffineSpace.map_id (n := ULift.{u} (Fin 1)) (S := B))) ≪≫
    (Etale.leftDerivedUpperStarId R A).app F ≪≫ κ
  have hd := (Classical.choose_spec
    (Dnc.existsUnique_dncInvariance P d X.g aB X.s X.section_eq)).1
      B aB (𝟙 B) (Category.id_comp aB) S e
  change (ProEtale.upperStar R (𝟙 B)).leftDerivedFunctor.mapIso δ = _ at hd
  dsimp only [e] at hd
  rw [section_reading_identity_map (hv :=
    AffineSpace.map_id (n := ULift.{u} (Fin 1)) (S := B)),
    section_reading_identity_map (hv :=
      AffineSpace.map_id (n := ULift.{u} (Fin 1)) (S := B))] at hd
  have hread :
      ((Etale.leftDerivedUpperStarId R B).app S ≪≫ θ₁.symm ≪≫
        (Etale.upperStar R
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso R _ _
            (AffineSpace.oneSection_comp_over _ B)).app S) ≪≫
      ((Etale.leftDerivedUpperStarId R B).app N ≪≫ θ₀.symm ≪≫ r₀).symm =
        (Etale.upperStar R (𝟙 B)).leftDerivedFunctor.mapIso ψ := by
    have hk : (Etale.upperStar R
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso R _ _
            (AffineSpace.oneSection_comp_over _ B)).app S = θ₁ := hκ
    rw [hk]
    simp only [Iso.symm_self_id, Iso.trans_refl]
    apply Iso.ext
    simpa only [ψ, R, S, N, Functor.id_obj, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.id_map,
      Category.assoc] using
        NatIso.naturality_2 (Etale.leftDerivedUpperStarId R B) ψ.hom
  rw [hread] at hd
  have hn := comparison_naturality P (𝟙 B) ψ.hom
  let δ' := Dnc.sourceComparison P d X.g aB X.s ≪≫ ν.mapIso ψ ≪≫
    (Dnc.normalComparison P d X.g aB X.s X.section_eq).symm
  have heq : (ProEtale.upperStar R (𝟙 B)).leftDerivedFunctor.mapIso δ =
      (ProEtale.upperStar R (𝟙 B)).leftDerivedFunctor.mapIso δ' := by
    apply Iso.ext
    rw [congrArg Iso.hom hd]
    simp only [δ', Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom,
      Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv]
    erw [← reassoc_of% hn]
    simp only [R, ν, Iso.hom_inv_id_assoc]
  apply Iso.ext
  have hn₁ := (ProEtale.leftDerivedUpperStarId R B).hom.naturality δ.hom
  have hn₂ := (ProEtale.leftDerivedUpperStarId R B).hom.naturality δ'.hom
  have hh := congrArg Iso.hom heq
  simp only [Functor.mapIso_hom] at hh
  simp only [Functor.id_map] at hn₁ hn₂
  rw [hh] at hn₁
  exact (cancel_epi ((ProEtale.leftDerivedUpperStarId R B).hom.app
    (Dnc.sourceSection P d X.g aB X.s))).mp (hn₁.symm.trans hn₂)

end ProofHelpers

/-- The actual family has a constant model normalized at one; reading that model
at zero gives the published delta. Isomorphisms from this family to a pullback are
also determined at one. No restriction or base-change naturality is asserted here.
Source: latest blueprint, sk-thm-dnc, Local construction and Gluing, and
prop-pur-dnc-family-constancy, normalization and uniqueness
(blueprint: lem-pur-section-constant-trivialization).

Proof: use centred etale charts for the smooth section to obtain the ordinary-etale
family comparison with the pullback of the source section invariant. The canonical
one-fibre comparison normalizes it, by composing with the pullback of the inverse
of its one-fibre automorphism. Two such normalized comparisons agree: after the
common shift they are maps of lisse rank-one sheaves; on each geometric affine-line
fibre their ratio is a locally constant unit, equal to one at the unit section.
Thus the local comparisons glue. Apply the exact comparison pullback nu*, its
canonical commutation with derived inverse image, and sourceComparison to obtain
kappa for the actual pro-etale family. The same sheaf-Hom argument gives the last
assertion, including any target C admitting the displayed isomorphisms: evaluation
at one identifies C with the corresponding etale-origin shifted line. The definition
of lineCounit is precisely the composition constraint used for this evaluation.
The normalization predicate of existsUnique_dncInvariance, at the identity base
change and the constructed ordinary-etale trivialization, identifies delta with
the inverse zero reading followed by endpointZero. Naturality of the comparison
pullback and its identity constraint cancel the presentation isomorphisms. The
argument on an empty base is vacuous, and rank zero uses the same shifts. -/
theorem section_constant_trivialization (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ} (X : Pair B d) :
    let A := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor
    let E₁ := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor
    let E₀ := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor
    let F := invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)
    let ε₁ := lineCounit P B _ (AffineSpace.oneSection_comp_over _ B)
    let ε₀ := lineCounit P B _ (AffineSpace.zeroSection_comp_over _ B)
    (∃ κ : F ≅ A.obj (invariant P aB X),
      E₁.mapIso κ ≪≫ ε₁.app _ = endpointOne P aB X ∧
      delta P aB X = (E₀.mapIso κ ≪≫ ε₀.app _).symm ≪≫ endpointZero P aB X) ∧
    (∀ (C : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)))
      (α β : F ≅ A.obj C), E₁.mapIso α = E₁.mapIso β → α = β) := by
  obtain ⟨⟨κ, hκ⟩, hF⟩ := etale_model P aB X
  let R := ModuleCat.{u + 1} P.Coefficient
  let A := AffineSpace (ULift.{u} (Fin 1)) B
  let π := A ↘ B
  let ν := (ProEtale.comparisonUpperStar R A).mapDerivedCategory
  let νB := (ProEtale.comparisonUpperStar R B).mapDerivedCategory
  let L := (ProEtale.upperStar R π).leftDerivedFunctor
  let σ : invariant P (π ≫ aB) (familyPair X) ≅
      ν.obj (Dnc.familyEtale P d X.g aB X.s X.section_eq) :=
    Dnc.sourceComparison P d (familyPair X).g (π ≫ aB) (familyPair X).s
  let τ : invariant P aB X ≅ νB.obj (sectionEtale P aB X) :=
    Dnc.sourceComparison P d X.g aB X.s
  let κP := σ ≪≫ ν.mapIso κ ≪≫
    (Dnc.pullComparison P π (sectionEtale P aB X)).symm ≪≫ L.mapIso τ.symm
  constructor
  · refine ⟨κP, ?_, ?_⟩
    · have h := model_reading P B _ (AffineSpace.oneSection_comp_over _ B) σ τ κ
      dsimp only at h
      rw [hκ] at h
      exact h
    · have h := model_reading P B _ (AffineSpace.zeroSection_comp_over _ B) σ τ κ
      dsimp only at h
      rw [delta_etale_reading P aB X κ hκ]
      erw [h]
      apply Iso.ext
      simp only [σ, τ, π, A, endpointZero, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
        Functor.mapIso_hom, Functor.mapIso_inv, Functor.mapIso_trans, Functor.mapIso_symm,
        Iso.symm_inv, Category.assoc, Iso.map_inv_hom_id_assoc,
        Iso.inv_hom_id_assoc]
  · intro C α β h
    exact proetale_detection P _ hF (etale_family_plus P aB X) σ C α β h

end WeilConjectures.PurityFiniteSetting.SectionRestriction
