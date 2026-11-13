/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsComplexUnit
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # The source affine model and its extension unit normalization
Source: Stacks Project, Tags 06Z0, 08DW(2) and 0AA7.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def normalizationChartSectionsIso (Y : Scheme.{u}) [IsAffine Y] :
    SheafOfModules.evaluation.{u} Y.ringCatSheaf (Opposite.op ⊤) ≅
      SheafOfModules.pushforward Y.isoSpec.hom.toRingCatSheafHom ⋙
        moduleSpecΓFunctor (R := Γ(Y, ⊤)) := by
  refine NatIso.ofComponents (fun N ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    change (Y.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r)) •
      (show Γ(N, ⊤) from x) = (show Γ(Y, ⊤) from r) • (show Γ(N, ⊤) from x)
    congr 1
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(Y, ⊤)).inv_hom_id_apply r
  · intro N N' f
    ext x
    rfl

private noncomputable def normalizationChartModuleIso (Y : Scheme.{u}) [IsAffine Y] :
    𝟭 (ModuleCat.{u} Γ(Y, ⊤)) ≅
      (tilde.functor Γ(Y, ⊤) ⋙ restrictFunctor Y.toSpecΓ) ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace := by
  let F := pushforward Y.isoSpec.hom
  let G := pushforward Y.isoSpec.inv
  let e : Y.Modules ≌ (Spec Γ(Y, ⊤)).Modules :=
    CategoryTheory.Equivalence.mk F G
      (pushforwardComp Y.isoSpec.hom Y.isoSpec.inv ≪≫
        pushforwardCongr Y.isoSpec.hom_inv_id ≪≫ pushforwardId Y).symm
      (pushforwardComp Y.isoSpec.inv Y.isoSpec.hom ≪≫
        pushforwardCongr Y.isoSpec.inv_hom_id ≪≫ pushforwardId (Spec Γ(Y, ⊤)))
  have : (pushforward Y.toSpecΓ).IsEquivalence := e.isEquivalence_functor
  let L := restrictFunctor Y.toSpecΓ
  let H := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let S := moduleSpecΓFunctor (R := Γ(Y, ⊤))
  let j : L ⋙ H ≅ S :=
    Functor.isoWhiskerLeft L (normalizationChartSectionsIso Y) ≪≫
      (Functor.associator L (pushforward Y.toSpecΓ) S).symm ≪≫
      Functor.isoWhiskerRight (asIso (restrictAdjunction Y.toSpecΓ).unit).symm S ≪≫
      Functor.leftUnitor S
  exact tilde.toTildeΓNatIso ≪≫ Functor.isoWhiskerLeft (tilde.functor Γ(Y, ⊤)) j.symm ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

set_option maxHeartbeats 500000 in
-- The derived unit calculation elaborates several affine carrier identifications.
/-- The extension counit computes the affine chart source, and intertwines Hom transposes.
Source: Stacks Project, Tags 06Z0, 08DW(2), 0AA7.
(blueprint: lem-sc-mixed-affine-extension-unit-normalization).

Proof: The ordinary affine tilde unit identifies H(F(P)) with P termwise, so this
complex is K-flat. Its left-derived extension counit is therefore invertible.
Identify the fixed mixedGlobalExtension adjunction with the derived extension
adjunction by left-adjoint uniqueness, preserving its unit. The source comparison a
is the inverse of extension applied to mixedSectionsComplexUnit, followed by this
counit. The affine sections comparison is invertible by the affine chart sections
unit theorem. Apply derivedη_fac_app to extension/restriction, inserting the exact
restriction comparison and quotient-to-homotopy factors. This proves the formula for
the unit. Postcompose with an arbitrary complex map f and use naturality of the
exact restriction comparison to obtain the displayed equality. It is uniform in Z
and f and uses no pullback, Leray comparison, or ordinary comparison c. Zero rings,
zero complexes and zero morphisms satisfy the same unit and naturality equations. -/
theorem exists_mixedAffineSections_extension_unit_normalization
    {S T : Scheme.{u}} [IsAffine S] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    ∀ [F.Additive] [H.Additive] [E.Additive]
      (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
      (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
    let C := (F.mapHomologicalComplex (.up ℤ)).obj P
    let X := ((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj P
    ∃ a : (mixedGlobalExtension g).obj
        ((schemeDerivedGlobalSections S).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj (((F ⋙ H ⋙ E).mapHomologicalComplex (.up ℤ)).obj P),
    ∀ (Z : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℤ)
      (f : ((E.mapHomologicalComplex (.up ℤ)).obj X) ⟶ Z),
      mixedSectionsComplexUnit S C ≫
          (mixedGlobalExtensionAdjunction g).homEquiv _ _
            (a.hom ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).mapHomologicalComplex
            (.up ℤ)).unit.app X ≫
              (R.mapHomologicalComplex (.up ℤ)).map f) ≫
          R.mapDerivedCategoryFactors.inv.app Z := by
  classical
  dsimp only
  intro instF instH instE P hP
  let F := tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
  let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
  let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
  let R := ModuleCat.restrictScalars.{u} g.appTop.hom
  let lAdj : mixedGlobalExtension g ⊣ R.mapDerivedCategory :=
    mixedGlobalExtensionAdjunction g
  let C := (F.mapHomologicalComplex (.up ℤ)).obj P
  let X : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ :=
    ((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj P
  let Y : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)) :=
    (schemeDerivedGlobalSections S).obj (DerivedCategory.Q.obj C)
  let eX : P ≅ X :=
    ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P).symm ≪≫
      (NatIso.mapHomologicalComplex
        (Scheme.Modules.normalizationChartModuleIso S) (.up ℤ)).app P
  have hX : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat X :=
    ((HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat.prop_iff_of_iso
      eX).mp hP
  have : IsIso (mixedSectionsComplexUnit S C) :=
    mixedAffineChart_sectionsComplexUnit_isIso S P
  let s : Y ≅ DerivedCategory.Q.obj X := (asIso (mixedSectionsComplexUnit S C)).symm
  have : (ModuleCat.extendScalars.{u, u, u} g.appTop.hom).PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ α hα
    let U₀ := CategoryTheory.MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} Γ(T, ⊤))
    let N := (HomologicalComplex.single (ModuleCat.{u} Γ(T, ⊤)) (.up ℤ) 0).obj U₀
    have h := (CochainComplex.mixedTensor_kFlat_quasiIso g.appTop.hom).1 N P Q α hα hP hQ
    let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor g.appTop.hom).flip U₀
    have h' : QuasiIso
        ((((ModuleCat.mixedTensor g.appTop.hom).obj
          U₀).mapHomologicalComplex
          (.up ℤ)).map α) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality α).symm)).1 h
    let e₀ : (ModuleCat.mixedTensor g.appTop.hom).obj U₀ ≅
        ModuleCat.extendScalars.{u, u, u} g.appTop.hom :=
      Functor.isoWhiskerLeft (ModuleCat.extendScalars g.appTop.hom)
        (CategoryTheory.MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} Γ(T, ⊤))) ≪≫
          Functor.rightUnitor _
    let e₁ := NatIso.mapHomologicalComplex e₀ (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e₁.app P) (e₁.app Q) (e₁.hom.naturality α).symm)).1 h'
  let adj := ModuleCat.extendRestrictScalarsAdj g.appTop.hom
  let b : E.leftDerivedFunctor ⊣ R.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight R.rightDerivedFunctorIsoMapDerivedCategory
  let e := lAdj.leftAdjointUniq b
  have : IsIso (E.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) :=
    E.isIso_leftDerivedFunctorCounit_app_of_kFlat X hX
  let q₀ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} Γ(S, ⊤))).app X
  let q₁ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} Γ(T, ⊤))).app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  let q₂ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} Γ(S, ⊤))).app
    ((R.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj X))
  let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  let d : E.leftDerivedFunctor.obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj X) :=
    E.leftDerivedFunctor.mapIso q₀.symm ≪≫ asIso ε ≪≫ q₁
  let a := (mixedGlobalExtension g).mapIso s ≪≫ e.app (DerivedCategory.Q.obj X) ≪≫ d
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ))
    E.leftDerivedFunctorCounit R.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  have ht : b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      R.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) := by
    simp only [b, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    erw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    erw [← Category.assoc, hfac]
    have hβ := NatTrans.congr_app
      R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hβ
    rw [Category.assoc]
    erw [reassoc_of% hβ]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hu := R.mapDerivedCategoryFactorsh_hom_app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  have hquot : DerivedCategory.Qh.map
      ((R.mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj X)) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [hquot] at hu
  erw [Category.comp_id] at hu
  have hu' : R.mapDerivedCategory.map q₁.hom ≫
      R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) =
      R.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
    have h := congrArg (fun z ↦ z ≫ q₂.hom) hu
    change R.mapDerivedCategoryFactorsh.hom.app
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom =
      (R.mapDerivedCategory.map q₁.hom ≫
        R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₂.inv) ≫ q₂.hom at h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact h.symm
  have hstd : b.unit.app (DerivedCategory.Q.obj X) ≫ R.mapDerivedCategory.map d.hom =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
      ((E.mapHomologicalComplex (.up ℤ)).obj X))).mp
    apply (cancel_epi q₀.hom).mp
    have hn := b.unit.naturality q₀.hom
    change q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) =
      b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        R.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) at hn
    have hq := DerivedCategory.quotientCompQhIso_hom_naturality
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app X)
    have hd : E.leftDerivedFunctor.map q₀.hom ≫ d.hom = ε ≫ q₁.hom := by
      change (E.leftDerivedFunctor.mapIso q₀).hom ≫
        ((E.leftDerivedFunctor.mapIso q₀).inv ≫ ε ≫ q₁.hom) = _
      exact Iso.hom_inv_id_assoc _ _
    have hdnat : q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) ≫
        R.mapDerivedCategory.map d.hom =
      b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        R.mapDerivedCategory.map ε ≫ R.mapDerivedCategory.map q₁.hom := by
      calc
        _ = b.unit.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          R.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) ≫
            R.mapDerivedCategory.map d.hom := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ z ≫ R.mapDerivedCategory.map d.hom) hn
        _ = _ := by
          rw [← R.mapDerivedCategory.map_comp, hd, Functor.map_comp]
    calc
      _ = b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          R.mapDerivedCategory.map ε ≫ R.mapDerivedCategory.map q₁.hom ≫
            R.mapDerivedCategoryFactors.hom.app
              ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
          R.mapDerivedCategoryFactors.hom.app
            ((E.mapHomologicalComplex (.up ℤ)).obj X)) hdnat
      _ = b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          R.mapDerivedCategory.map ε ≫
          R.mapDerivedCategoryFactorsh.hom.app
            ((E.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
        exact congrArg (fun z ↦ b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
          R.mapDerivedCategory.map ε ≫ z) hu'
      _ = DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q₂.hom) ht
      _ = q₀.hom ≫ DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) := by
        erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
        exact hq
      _ = _ := by
        simp only [Category.assoc, Iso.inv_hom_id_app]
        erw [Category.comp_id]
  have ha : lAdj.unit.app Y ≫
      R.mapDerivedCategory.map a.hom =
      s.hom ≫ DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
    change lAdj.unit.app Y ≫
      R.mapDerivedCategory.map
        ((mixedGlobalExtension g).map s.hom ≫ e.hom.app (DerivedCategory.Q.obj X) ≫
          d.hom) = _
    have hn := lAdj.unit.naturality s.hom
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    have he := lAdj.unit_leftAdjointUniq_hom_app b
      (DerivedCategory.Q.obj X)
    calc
      _ = (lAdj.unit.app Y ≫
          R.mapDerivedCategory.map ((mixedGlobalExtension g).map s.hom)) ≫
        R.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj X)) ≫
          R.mapDerivedCategory.map d.hom := by
        rw [Functor.map_comp, Functor.map_comp]
        simp only [Category.assoc]
      _ = s.hom ≫ lAdj.unit.app (DerivedCategory.Q.obj X) ≫
          R.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj X)) ≫
            R.mapDerivedCategory.map d.hom := by
        rw [← hn]
        simp only [Category.assoc]
      _ = s.hom ≫ b.unit.app (DerivedCategory.Q.obj X) ≫ R.mapDerivedCategory.map d.hom := by
        erw [reassoc_of% he]
      _ = _ := congrArg (fun z ↦ s.hom ≫ z) hstd
  refine ⟨a, ?_⟩
  intro Z f
  change s.inv ≫ lAdj.homEquiv _ _ (a.hom ≫ DerivedCategory.Q.map f) = _
  rw [lAdj.homEquiv_unit]
  change s.inv ≫ lAdj.unit.app Y ≫
    R.mapDerivedCategory.map (a.hom ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X ≫
        (R.mapHomologicalComplex (.up ℤ)).map f) ≫ R.mapDerivedCategoryFactors.inv.app Z
  rw [Functor.map_comp]
  erw [reassoc_of% ha]
  simp only [Iso.inv_hom_id_assoc]
  erw [← R.mapDerivedCategoryFactors.inv.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

end AlgebraicGeometry
