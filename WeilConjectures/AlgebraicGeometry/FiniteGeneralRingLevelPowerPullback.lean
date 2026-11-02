/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineHelper
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

/-! # Pullback of the ordered finite Tate level power

Source: general-ring smooth purity, proof (3), local frame calculation.
(blueprint: lem-sp-general-ring-level-power-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] Functor.leftDerivedFunctor Etale.upperStar
attribute [local implicit_reducible] Etale.ordinaryFiniteSingleFunctor
  Etale.ordinaryFiniteDegreeZero Etale.derivedTensorRight Etale.ordinaryFiniteTensorPullback
  Etale.ordinaryFiniteTensorRightMapIso Etale.leftDerivedUpperStarTensorIso
  Etale.affineLinearBaseCoefficient

private theorem shift_square
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K L : C} {K' L' : D}
    (g : K ⟶ L) (a : F.obj K ⟶ K') (b : F.obj L ⟶ L') (g' : K' ⟶ L')
    (h : F.map g ≫ b = a ≫ g') (n : ℤ) :
    F.map (g⟦n⟧') ≫ (F.commShiftIso n).hom.app L ≫ b⟦n⟧' =
      (F.commShiftIso n).hom.app K ≫ a⟦n⟧' ≫ g'⟦n⟧' := by
  rw [F.commShiftIso_hom_naturality_assoc]
  simp only [← Functor.map_comp, h]

private theorem tensor_square
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) {K L K₁ L₁ : C} {K' L' K₁' L₁' : D}
    (a : K ⟶ K₁) (b : L ⟶ L₁)
    (c : F.obj K₁ ⟶ K₁') (e : F.obj L₁ ⟶ L₁')
    (c' : F.obj K ⟶ K') (e' : F.obj L ⟶ L')
    (a' : K' ⟶ K₁') (b' : L' ⟶ L₁')
    (δ : F.obj (K ⊗ L) ⟶ F.obj K ⊗ F.obj L)
    (δ' : F.obj (K₁ ⊗ L₁) ⟶ F.obj K₁ ⊗ F.obj L₁)
    (hn : δ ≫ (F.map a ⊗ₘ F.map b) = F.map (a ⊗ₘ b) ≫ δ')
    (hx : F.map a ≫ c = c' ≫ a') (hy : F.map b ≫ e = e' ≫ b') :
    F.map (a ⊗ₘ b) ≫ δ' ≫ (c ⊗ₘ e) = δ ≫ (c' ⊗ₘ e') ≫ (a' ⊗ₘ b') := by
  rw [← reassoc_of% hn]
  simp only [tensorHom_comp_tensorHom, hx, hy]

private theorem single_square
    {B B' C D : Type*} [Category B] [Category B'] [Category C] [Category D]
    (F : C ⥤ D) (sY : B ⥤ C) (sX : B' ⥤ D) (H : B ⥤ B')
    (c : sY ⋙ F ≅ H ⋙ sX) {K L : B} {K' L' : B'}
    (b : K ≅ L) (a : H.obj K ≅ K') (e : H.obj L ≅ L') :
    F.map (sY.map b.hom) ≫ c.hom.app L ≫ sX.map e.hom =
      (c.hom.app K ≫ sX.map a.hom) ≫
        sX.map (a.inv ≫ H.map b.hom ≫ e.hom) := by
  have hn := c.hom.naturality b.hom
  dsimp only [Functor.comp_map] at hn
  calc
    _ = c.hom.app K ≫ sX.map (H.map b.hom) ≫ sX.map e.hom := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← sX.map_comp_assoc, Iso.hom_inv_id, sX.map_id, Category.id_comp]

private theorem shifted_line_square
    (A : Type (u + 1)) [CommRing A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN) :
    (Etale.ordinaryFinitePullback A f).map
        ((shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map b.hom)) ≫
      (Etale.ordinaryFiniteShiftedLinePullback A N hN tN f hS').hom =
    (Etale.ordinaryFiniteShiftedLinePullback A M hM tM f hS).hom ≫
      (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map
        (((tM.line f hS).symm ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} A) f).mapIso b ≪≫ tN.line f hS').hom)) := by
  let : (Etale.ordinaryFinitePullback A f).CommShift ℤ :=
    Etale.commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have hzero : (Etale.ordinaryFinitePullback A f).map
        ((Etale.ordinaryFiniteSingleFunctor A S).map b.hom) ≫
      (Etale.ordinaryFiniteSinglePullbackIso A f).hom.app _ ≫
        (Etale.ordinaryFiniteSingleFunctor A X).map (tN.line f hS').hom =
    ((Etale.ordinaryFiniteSinglePullbackIso A f).hom.app _ ≫
      (Etale.ordinaryFiniteSingleFunctor A X).map (tM.line f hS).hom) ≫
        (Etale.ordinaryFiniteSingleFunctor A X).map
          (((tM.line f hS).symm ≪≫
            (Etale.upperStar (ModuleCat.{u + 1} A) f).mapIso b ≪≫
              tN.line f hS').hom) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using
      single_square (Etale.ordinaryFinitePullback A f)
        (Etale.ordinaryFiniteSingleFunctor A S) (Etale.ordinaryFiniteSingleFunctor A X)
        (Etale.upperStar (ModuleCat.{u + 1} A) f) (Etale.ordinaryFiniteSinglePullbackIso A f)
        b (tM.line f hS) (tN.line f hS')
  have hs := shift_square (Etale.ordinaryFinitePullback A f) _ _ _ _ hzero (2 : ℤ)
  simpa only [Etale.ordinaryFiniteShiftedLinePullback,
    Etale.shiftedSinglePullbackIsoWith, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Etale.ordinaryFiniteSingleFunctor_eq, Etale.ordinaryFinitePullback,
    Etale.ordinaryFiniteLine, Etale.ordinaryFiniteDegreeZero] using hs

/-- The recursively ordered level power commutes with normalized pullback.

Source: general-ring smooth purity, proof (3), local frame calculation (the ordered
level-power induction).
Proof: induct on `d`. For `d = 0` both level powers are identities and both sides are the
constant-unit comparison. For `d + 1`, `vectorIntegrationBaseCoefficientPullback` is the
tensor pullback comparison followed by the stage-`d` comparison tensored with the shifted
single-line comparison of `t.line f`; the level power is the stage-`d` level power
tensored with `b[2]`. The tensor pullback comparison is natural in both factors, which
moves `f^*` of the level power past it; on the first factor the induction hypothesis
applies, and on the second factor the shifted single-degree pullback comparison is natural
in the sheaf, so `f^*(b[2])` followed by the comparison at `N` is the comparison at `M`
followed by `(λ_M⁻¹ ≫ f^*b ≫ λ_N)[2]`, by definition of the pulled-back line comparison.
(blueprint: lem-sp-general-ring-level-power-pullback). -/
theorem finiteGeneralRingLevelPower_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (d : ℕ) :
    (Etale.ordinaryFinitePullback A f).map
        (finiteGeneralRingLevelPower A M N hM hN S b d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback A N hN tN f hS' d).hom =
    (Etale.vectorIntegrationBaseCoefficientPullback A M hM tM f hS d).hom ≫
      (finiteGeneralRingLevelPower A M N hM hN X
        ((tM.line f hS).symm ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} A) f).mapIso b ≪≫ tN.line f hS') d).hom := by
  have tensor_map (T : Scheme.{u})
      {K K' L L' : Etale.DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
      (Etale.ordinaryFiniteTensorRightMapIso A T e c).hom = e.hom ⊗ₘ c.hom := by
    change e.hom ▷ L ≫ K' ◁ c.hom = _
    rw [MonoidalCategory.tensorHom_def]
  have tensor_pull (K L : Etale.DerivedCategoryModule A S) :
      (Etale.ordinaryFiniteTensorPullback A f K L).hom =
        ((Etale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app K).app L := by
    rfl
  have level_succ (T : Scheme.{u})
      (e : Scheme.finiteEtaleTateLine T M A hM ≅
        Scheme.finiteEtaleTateLine T N A hN) (d : ℕ) :
      (finiteGeneralRingLevelPower A M N hM hN T e (d + 1)).hom =
        (finiteGeneralRingLevelPower A M N hM hN T e d).hom ⊗ₘ
          (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map e.hom) := by
    change (_ ≫ _) = _
    rfl
  have coeff_succ (J : ℕ) (hJ : (J : A) = 0)
      (t : Etale.OrdinaryFiniteTwistTransport A J hJ)
      (h : IsUnit (J : Γ(S, ⊤))) (d : ℕ) :
      (Etale.vectorIntegrationBaseCoefficientPullback A J hJ t f h (d + 1)).hom =
        (Etale.ordinaryFiniteTensorPullback A f
          (Etale.affineLinearBaseCoefficient A J hJ S d)
          ((Etale.ordinaryFiniteLine A J hJ S)⟦(2 : ℤ)⟧)).hom ≫
        ((Etale.vectorIntegrationBaseCoefficientPullback A J hJ t f h d).hom ⊗ₘ
          (Etale.ordinaryFiniteShiftedLinePullback A J hJ t f h).hom) := by
    change (_ ≪≫ Etale.ordinaryFiniteTensorRightMapIso A X _ _).hom = _
    rw [Iso.trans_hom, tensor_map]
    rfl
  induction d with
  | zero =>
    change (Etale.ordinaryFinitePullback A f).map (𝟙 (Etale.ordinaryFiniteUnit A S)) ≫
        (Etale.ordinaryFiniteUnitPullback A f).hom =
      (Etale.ordinaryFiniteUnitPullback A f).hom ≫ 𝟙 (Etale.ordinaryFiniteUnit A X)
    simp
  | succ d ih =>
    rw [level_succ, level_succ, coeff_succ, coeff_succ]
    simpa only [Category.assoc, tensor_pull, Etale.FiniteSmoothPurity.line,
      Etale.affineLinearBaseCoefficient, Etale.derivedTensorRight, Etale.derivedTensor,
      Etale.ordinaryFiniteLine, Etale.ordinaryFiniteDegreeZero] using
      tensor_square (Etale.ordinaryFinitePullback A f) _ _ _ _ _ _ _ _ _ _
      (Etale.leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) f _ _)
      ih (shifted_line_square A M N hM hN f hS hS' b tM tN)

end AlgebraicGeometry.ProEtale
