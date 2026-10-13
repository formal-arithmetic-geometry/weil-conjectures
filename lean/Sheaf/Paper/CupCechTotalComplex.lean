/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import all Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # Cech total complexes of computing resolutions

Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: def-sc-cup-cech-total)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Global sections of a computing resolution.
Source: Stacks 0FKV (blueprint: def-sc-cup-cech-total). -/
abbrev cupSections {X : Scheme.{u}} {F : X.Modules} (D : CupAcyclicResolution F) :=
  ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.K

/-- Components of the map from global sections of the resolution to its Čech total complex.
Source: Stacks 01EQ (blueprint: def-sc-cup-cech-total). -/
noncomputable def cupCechAlphaComponent {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F : X.Modules} (I : CupAcyclicResolution F) (n : ℕ) :
    (cupSections I).X n ⟶
      ((cupCechDouble U I.K).total (ComplexShape.up ℕ)).X n :=
  moduleCechZero U (I.K.X n) ≫
    (cupCechDouble U I.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)

/-- The alpha components commute with the differential. Source: Stacks 01EQ
(blueprint: def-sc-cup-cech-total).
Proof: restrictions commute with the resolution differential. The Čech differential
of the restrictions of a global section is zero. The total differential on the (n,0)
summand is the resolution differential plus (-1)^n times that zero differential. -/
theorem cupCechAlpha_comm {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : CupAcyclicResolution F) (n m : ℕ) :
    cupCechAlphaComponent U I n ≫
        ((cupCechDouble U I.K).total (ComplexShape.up ℕ)).d n m =
      (cupSections I).d n m ≫ cupCechAlphaComponent U I m := by
  by_cases hnm : n + 1 = m
  · dsimp only [cupCechAlphaComponent]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      Category.assoc, Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ hnm 0 m (by simp [← hnm]),
      HomologicalComplex₂.d₂_eq' _ _ n (show (0 : ℕ) + 1 = 1 from rfl)]
    dsimp
    simp only [one_smul, Linear.comp_units_smul]
    have hv : moduleCechZero U (I.K.X n) ≫
        ((cupCechDouble U I.K).X n).d 0 1 = 0 := by
      change moduleCechZero U (I.K.X n) ≫
        ((CategoryTheory.cechComplexFunctor U).obj
          (I.K.X n).presheafModuleCat).d 0 1 = 0
      exact moduleCechZero_d U (I.K.X n)
    simp only [← Category.assoc, hv,
      zero_comp, smul_zero, add_zero]
    have hh : moduleCechZero U (I.K.X n) ≫
        ((cupCechDouble U I.K).d n m).f 0 =
      (cupSections I).d n m ≫
        moduleCechZero U (I.K.X m) := by
      change moduleCechZero U (I.K.X n) ≫
        ((CategoryTheory.cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (I.K.d n m).val)).f 0 =
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (I.K.d n m) ≫
          moduleCechZero U (I.K.X m)
      exact moduleCechZero_naturality U (I.K.d n m)
    rw [hh]
  · rw [HomologicalComplex.shape _ _ _ hnm, HomologicalComplex.shape _ _ _ hnm]
    simp

/-- The map alpha of Stacks 01EQ (blueprint: def-sc-cup-cech-total). -/
noncomputable def cupCechAlpha {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : CupAcyclicResolution F) :
    cupSections I ⟶
      (cupCechDouble U I.K).total (ComplexShape.up ℕ) where
  f := cupCechAlphaComponent U I
  comm' := fun n m _ => cupCechAlpha_comm U I n m

/-- Components of the augmentation beta into the Čech total complex.
Source: Stacks 01EQ (blueprint: def-sc-cup-cech-total). -/
noncomputable def cupCechBetaComponent {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F : X.Modules} (I : CupAcyclicResolution F) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).X n ⟶
      ((cupCechDouble U I.K).total (ComplexShape.up ℕ)).X n :=
  ((CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (I.augmentation.f 0).val)).f n ≫
    (cupCechDouble U I.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)

/-- The beta components commute with the differential. Source: Stacks 01EQ
(blueprint: def-sc-cup-cech-total).
Proof: Čech differentials commute with the augmentation. The augmentation followed by
the resolution differential is zero. On the (0,n) summand the Čech differential has sign +1. -/
theorem cupCechBeta_comm {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : CupAcyclicResolution F) (n m : ℕ) :
    cupCechBetaComponent U I n ≫
        ((cupCechDouble U I.K).total (ComplexShape.up ℕ)).d n m =
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).d n m ≫
        cupCechBetaComponent U I m := by
  by_cases h : n + 1 = m
  · subst m
    dsimp [cupCechBetaComponent]
    rw [HomologicalComplex₂.total_d, Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [HomologicalComplex₂.d₁_eq' _ _ (by simp : (ComplexShape.up ℕ).Rel 0 1),
      HomologicalComplex₂.d₂_eq _ _ 0 (by simp : (ComplexShape.up ℕ).Rel n (n + 1))
        (n + 1) (by simp)]
    simp only [PresheafOfModules.forgetToPresheafModuleCat_map, ComplexShape.ε₁_def,
      one_smul, ComplexShape.ε₂_def, ComplexShape.ε_zero, Preadditive.comp_add]
    let T := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    have hz : I.augmentation.f 0 ≫ I.K.d 0 1 = 0 := by
      rw [I.augmentation.comm 0 1]
      simp
    have hz' : (T.map (I.augmentation.f 0)).f n ≫ (T.map (I.K.d 0 1)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, ← T.map_comp, hz, T.map_zero]
      rfl
    have hc := (T.map (I.augmentation.f 0)).comm n (n + 1)
    change (T.map (I.augmentation.f 0)).f n ≫ (T.map (I.K.d 0 1)).f n ≫ _ +
      (T.map (I.augmentation.f 0)).f n ≫ (T.obj (I.K.X 0)).d n (n + 1) ≫ _ = _
    rw [← Category.assoc, hz', zero_comp, zero_add, ← Category.assoc, hc,
      Category.assoc]
    rfl
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape _ _ _ h]
    simp

/-- The map beta of Stacks 01EQ (blueprint: def-sc-cup-cech-total). -/
noncomputable def cupCechBeta {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : CupAcyclicResolution F) :
    (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U I.K).total (ComplexShape.up ℕ) where
  f := cupCechBetaComponent U I
  comm' := fun n m _ => cupCechBeta_comm U I n m

end
end AlgebraicGeometry.Scheme.Modules
