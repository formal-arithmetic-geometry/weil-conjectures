/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.ProperBaseChange.RingedToposKFlatPullback

/-!
# Composition of unbounded derived direct images of ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
-/

@[expose] public section

universe u w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

section Generic

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
omit [HasDerivedCategory A] in
variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w} E]
private theorem composition [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (hFG : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      ∀ (T : CochainComplex B ℤ), T.IsKInjective →
      ∀ (j : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
      ∀ [QuasiIso j], QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j)) :
    ∃ (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
      (RG : DerivedCategory.{w} B ⥤ DerivedCategory.{w} E)
      (RFG : DerivedCategory.{w} A ⥤ DerivedCategory.{w} E)
      (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF)
      (ηg : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RG)
      (ηfg : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RFG),
      RF.IsRightDerivedFunctor ηf (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      RG.IsRightDerivedFunctor ηg (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) ∧
      RFG.IsRightDerivedFunctor ηfg (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      (∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I) ∧ IsIso (ηfg.app I)) ∧
      (∀ T : CochainComplex B ℤ, T.IsKInjective → IsIso (ηg.app T)) ∧
      ∃! κ : RFG ≅ RF ⋙ RG,
        (∀ M : CochainComplex A ℤ,
          ηfg.app M ≫ κ.hom.app (DerivedCategory.Q.{w}.obj M) =
            ηg.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
              RG.map (ηf.app M)) ∧
        ∀ I : CochainComplex A ℤ, I.IsKInjective →
        ∀ T : CochainComplex B ℤ, T.IsKInjective →
        ∀ (j : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
        ∀ [QuasiIso j],
        QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
          ηfg.app I ≫ κ.hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ≫
              ηg.app T ≫ RG.map (inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I) := by
  obtain ⟨RF, ηf, hf, hIf⟩ := exists_derived F
  obtain ⟨RG, ηg, hg, hIg⟩ := exists_derived G
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Gc := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let ηfg : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ RG) :=
    { app := fun M ↦ ηg.app (Fc.obj M) ≫ RG.map (ηf.app M)
      naturality := by
        intro M N a
        dsimp only [Functor.comp_map]
        change DerivedCategory.Q.map (Gc.map (Fc.map a)) ≫
            (ηg.app (Fc.obj N) ≫ RG.map (ηf.app N)) =
          (ηg.app (Fc.obj M) ≫ RG.map (ηf.app M)) ≫ RG.map (RF.map (DerivedCategory.Q.map a))
        have hn := ηg.naturality (Fc.map a)
        have hm := ηf.naturality a
        dsimp only [Functor.comp_map] at hn hm
        rw [← Category.assoc, hn]
        simp only [Category.assoc]
        rw [← RG.map_comp, hm, RG.map_comp] }
  have hGFI (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      IsIso (ηg.app (Fc.obj I)) := by
    obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective (Fc.obj I)
    have : QuasiIso j := hj
    have : QuasiIso (Gc.map j) := hFG I hI T hT j
    have : IsIso (ηg.app T) := hIg T hT
    have : IsIso (DerivedCategory.Q.map (Gc.map j)) := inferInstance
    have : IsIso (RG.map (DerivedCategory.Q.map j)) := inferInstance
    have hn := ηg.naturality j
    dsimp only [Functor.comp_map] at hn
    have : IsIso (ηg.app (Fc.obj I) ≫ RG.map (DerivedCategory.Q.map j)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (RG.map (DerivedCategory.Q.map j))
  have hIfg (I : CochainComplex A ℤ) (hI : I.IsKInjective) : IsIso (ηfg.app I) := by
    have := hIf I hI
    have := hGFI I hI
    dsimp only [ηfg]
    infer_instance
  have hfg : (RF ⋙ RG).IsRightDerivedFunctor ηfg
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
    apply (derives (F ⋙ G)).isRightDerivedFunctor_of_isIso ηfg
    intro X
    exact hIfg X.obj X.property
  refine ⟨RF, RG, RF ⋙ RG, ηf, ηg, ηfg, hf, hg, hfg,
    (fun I hI ↦ ⟨hIf I hI, hIfg I hI⟩), hIg, Iso.refl _, ⟨?_, ?_⟩, ?_⟩
  · intro M
    exact Category.comp_id _
  · intro I hI T hT j hj
    refine ⟨hFG I hI T hT j, ?_⟩
    change (ηg.app (Fc.obj I) ≫ RG.map (ηf.app I)) ≫ 𝟙 _ = _
    rw [Category.comp_id, RG.map_comp]
    have hn := ηg.naturality j
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc (DerivedCategory.Q.map (Gc.map j)), hn]
    simp only [Category.assoc]
    rw [← RG.map_comp_assoc, IsIso.hom_inv_id, RG.map_id, Category.id_comp]
  · intro κ hκ
    apply Iso.ext
    have := hfg
    apply Functor.rightDerived_ext (RF ⋙ RG) ηfg
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    apply NatTrans.ext
    funext M
    simpa [ηfg] using hκ.1 M

omit [HasDerivedCategory A] in
end Generic

set_option maxHeartbeats 800000 in
-- Repeated module localizations and their comparison-unit equations require more elaboration steps.
end CategoryTheory
