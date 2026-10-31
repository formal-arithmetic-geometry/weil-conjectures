/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-mate-coherence-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 500000 in
-- The factorization calculation traverses nine exact-functor localizations.
set_option maxHeartbeats 500000 in
-- This generic calculation localizes all six faces of an exact-functor cube.
private theorem normalized_derived_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions B'] [Abelian.HasKInjectiveResolutions D']
    (F : A ⥤ B) (R : B ⥤ A) (K : C ⥤ D) (S : D ⥤ C)
    (F' : A' ⥤ B') (R' : B' ⥤ A') (K' : C' ⥤ D') (S' : D' ⥤ C')
    (G : A ⥤ C) (H : B ⥤ D) (G' : A' ⥤ C') (H' : B' ⥤ D')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [F.Additive] [K.Additive] [F'.Additive] [K'.Additive]
    [R.Additive] [S.Additive] [R'.Additive] [S'.Additive]
    [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
    [a.Additive] [b.Additive] [c.Additive] [d.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits c] [PreservesFiniteColimits c]
    [PreservesFiniteLimits d] [PreservesFiniteColimits d]
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : a ⋙ G' ≅ G ⋙ c)
    (pH : b ⋙ H' ≅ H ⋙ d) (pK : K ⋙ d ≅ c ⋙ K')
    (e : F ⋙ H ≅ G ⋙ K) (e' : F' ⋙ H' ≅ G' ⋙ K')
    (comm : ∀ X : A,
      H'.map (pF.hom.app X) ≫ e'.hom.app (a.obj X) ≫ K'.map (pG.hom.app X) =
        pH.hom.app (F.obj X) ≫ d.map (e.hom.app X) ≫ pK.hom.app (G.obj X))
    (Z : DerivedCategory B) :
    c.mapDerivedCategory.map ((SystemEvaluationNormalization.derivedMate adj adjK e).app Z) ≫
        (SystemEvaluationNormalization.derivedMate adjK adjK' pK).app
          (H.mapDerivedCategory.obj Z) =
      (Functor.mapDerivedCategorySquareIso pG).inv.app (R.rightDerivedFunctor.obj Z) ≫
        G'.mapDerivedCategory.map
          ((SystemEvaluationNormalization.derivedMate adj adj' pF).app Z) ≫
        (SystemEvaluationNormalization.derivedMate adj' adjK' e').app
          (b.mapDerivedCategory.obj Z) ≫
        S'.rightDerivedFunctor.map ((Functor.mapDerivedCategorySquareIso pH).hom.app Z) := by
  let sd := Functor.mapDerivedCategorySquareIso pF
  let ca := Functor.mapDerivedCategorySquareIso e'
  let cb := Functor.mapDerivedCategorySquareIso e
  let sy := Functor.mapDerivedCategorySquareIso pG
  let sx := Functor.mapDerivedCategorySquareIso pH
  let sl := Functor.mapDerivedCategorySquareIso pK
  have cube := Functor.mapDerivedCategory_exactCube
    F b H' a F' G' K' G c H d K pF e' pG pH e pK comm
  have hc (X : DerivedCategory A) :
      K'.mapDerivedCategory.map (sy.hom.app X) ≫
          sl.inv.app (G.mapDerivedCategory.obj X) ≫
          d.mapDerivedCategory.map (cb.inv.app X) =
        ca.inv.app (a.mapDerivedCategory.obj X) ≫
          H'.mapDerivedCategory.map (sd.inv.app X) ≫
          sx.hom.app (F.mapDerivedCategory.obj X) := by
    have cx := NatTrans.congr_app cube X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at cx
    change H'.mapDerivedCategory.map (sd.hom.app X) ≫
        ca.hom.app (a.mapDerivedCategory.obj X) ≫
        K'.mapDerivedCategory.map (sy.hom.app X) =
      sx.hom.app (F.mapDerivedCategory.obj X) ≫
        d.mapDerivedCategory.map (cb.hom.app X) ≫
        sl.hom.app (G.mapDerivedCategory.obj X) at cx
    apply (cancel_epi
      (H'.mapDerivedCategory.map (sd.hom.app X) ≫
        ca.hom.app (a.mapDerivedCategory.obj X))).1
    simp only [Category.assoc]
    rw [reassoc_of% cx]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id, Functor.map_id, Category.id_comp]
  have h := exchangeMate_cube adj.mapDerivedCategoryRightDerivedAdjunction
    adjK.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    adjK'.mapDerivedCategoryRightDerivedAdjunction
    a.mapDerivedCategory b.mapDerivedCategory c.mapDerivedCategory d.mapDerivedCategory
    sd sy.symm sx.symm sl cb.inv ca.inv hc Z
  have hh := congrArg (fun t ↦ t ≫ S'.rightDerivedFunctor.map (sx.hom.app Z)) h
  simp only [Iso.symm_hom, Category.assoc] at hh
  erw [← S'.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    S'.rightDerivedFunctor.map_id, Category.comp_id] at hh
  simpa only [SystemEvaluationNormalization.derivedMate, Functor.comp_obj,
    sd, ca, cb, sl, sx, sy] using hh


end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))


set_option maxHeartbeats 500000 in
-- Unfolding the underlying semilinear module functors exceeds the default allowance.
variable (HB : StrictRingSystem BX ⥤ StrictRingSystem BY) [HB.Additive]
  (HA : StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj AY)) [HA.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  (adjB : FB.functor ⊣ HB) (adjA : FA.functor ⊣ HA)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, FB.levelFunctor n ⊣ Hn n)
  (H0 : systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0 ⥤
    systemLevel ((Functor.const ℕᵒᵖ).obj AY) 0) [H0.Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)]
  (adj0 : FA.levelFunctor 0 ⊣ H0)

set_option maxHeartbeats 500000 in
-- The six faces contain nested system, evaluation, and derived-functor comparisons.
private theorem scalar_coherence
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA)
    (n : ℕ) (Z : DerivedCategory (StrictRingSystem BX)) :
        (singletonLevelRestriction aY n).mapDerivedCategory.map
            ((SystemEvaluationNormalization.derivedMate adjB (adjn n) (FB.evaluation n)).app Z) ≫
          (SystemEvaluationNormalization.derivedMate (adjn n) adj0 (d.level n)).app
            ((derivedSystemEvaluation BX n).obj Z) =
        (systemNormalizationDerivedRestrictionEvaluation aY n).inv.app
            (HB.rightDerivedFunctor.obj Z) ≫
          (derivedSystemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n).map
            ((SystemEvaluationNormalization.derivedMate adjB adjA d.scalar).app Z) ≫
          (CategoryTheory.SystemEvaluationNormalization.derivedMate adjA adj0 (FA.evaluation n)).app
              ((systemNormalizationRestriction aX).mapDerivedCategory.obj Z) ≫
          H0.rightDerivedFunctor.map
            ((systemNormalizationDerivedRestrictionEvaluation aX n).hom.app Z) := by
  simpa only [systemNormalizationDerivedRestrictionEvaluation, derivedSystemEvaluation] using
    CategoryTheory.normalized_derived_cube
      FB.functor HB (FB.levelFunctor n) (Hn n)
      FA.functor HA (FA.levelFunctor 0) H0
      (systemEvaluation BY n) (systemEvaluation BX n)
      (systemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n)
      (systemEvaluation ((Functor.const ℕᵒᵖ).obj AX) n)
      (systemNormalizationRestriction aY) (systemNormalizationRestriction aX)
      (singletonLevelRestriction aY n) (singletonLevelRestriction aX n)
      adjB (adjn n) adjA adj0 d.scalar
      (systemNormalizationRestrictionEvaluation aY n)
      (systemNormalizationRestrictionEvaluation aX n)
      (d.level n) (FB.evaluation n) (FA.evaluation n)
      (fun M ↦ d.scalarEvaluation M n) Z

omit [Abelian.HasKInjectiveResolutions
    (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions
    (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)] in
end SheafOfModules
